set Usine;
set Depots;
set Depots_Ouvrir_Fermer ordered;
set Depots_Ouvrir_Fermer_Sans_Birmingham := Depots_Ouvrir_Fermer diff {first(Depots_Ouvrir_Fermer)};
set Clients;
set Usine_Depots:= Usine union Depots;
set Depots_Clients:= Depots union Clients;
set Usine_ne_livre within (Depots_Clients cross Usine);
set Depots_ne_livre within (Clients cross Depots);


param Couts_Distribution{Depots_Clients,Usine_Depots}>=0;
param Capacite_Usine{Usine}>=0;
param Debit_Depots{Depots}>=0;
param Besoins_Clients{Clients}>=0;
param Cout_Occasionnees{Depots_Ouvrir_Fermer}>=0;

var agr_ouv_fer{Depots_Ouvrir_Fermer} binary;
var Usine_Fournit{t in Depots_Clients, p in Usine}>=0;
var Depots_Fournit{t in Clients, p in Depots}>=0;

minimize cout_total :
    (sum{t in Depots_Clients, p in Usine} Couts_Distribution[t,p]*Usine_Fournit[t,p] )+ (sum{t in Clients, p in Depots} Couts_Distribution[t,p]*Depots_Fournit[t,p])+(sum{p in Depots_Ouvrir_Fermer} agr_ouv_fer[p]*Cout_Occasionnees[p])-10000-5000; 

subject to Null_Usine_Depots_Fournit:
    sum{(t,p) in Usine_ne_livre} Usine_Fournit[t,p] + sum{(t,p) in Depots_ne_livre} Depots_Fournit[t,p] =0;

subject to Usine_Capacite {p in Usine} :
    sum{t in Depots_Clients} Usine_Fournit[t,p] <= Capacite_Usine[p];

subject to Clients_Besoins {t in Clients}:
    (sum{p in Usine} Usine_Fournit[t,p]) + (sum{p in Depots} Depots_Fournit[t,p]) >= Besoins_Clients[t];
    
subject to Depots_Débits {t in Depots}:
    sum{p in Usine} Usine_Fournit[t,p] <= (if t='Birmingham' or t='Londres' then 1 else agr_ouv_fer[t])*Debit_Depots[t] + (if t='Birmingham' then agr_ouv_fer[t] else 0)*20000;   

subject to Balance {t in Depots} :
    sum{p in Usine} Usine_Fournit[t,p] = sum{i in Clients} Depots_Fournit[i,t];
    
subject to Nombre_De_Depots :
    sum{p in Depots_Ouvrir_Fermer_Sans_Birmingham} agr_ouv_fer[p] <=2;
#---------------------------------------------------exo3---------------------------------------------------------------------------------------
subject to Preference_C5 :
    Depots_Fournit['C5','Birmingham'] = 50000; 
#----------------------------------------------------------------------------------------------------------------------------------------------  

#-------------------------------------------------exo1------------------------------------------------------------------------------------------
subject to partie1 :
    agr_ouv_fer['Birmingham']+agr_ouv_fer['Bristol']+agr_ouv_fer['Northampton']=0;
subject to Partie1 :
    sum{p in Depots_Ouvrir_Fermer_Sans_Birmingham} agr_ouv_fer[p] =2;
#---------------------------------------------------------------------------------------------------------------------------------------------