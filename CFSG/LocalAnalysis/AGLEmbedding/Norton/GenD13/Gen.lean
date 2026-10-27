module

public import Certificates.Certificate125530
public import Certificates.Certificate125531
public import Certificates.Certificate125532
public import Certificates.Certificate125533
public import Certificates.Certificate125534
public import Certificates.Certificate125535
public import Certificates.Certificate125536
public import Certificates.Certificate125537
public import Certificates.Certificate125538
public import Certificates.Certificate125539
public import Certificates.Certificate125540
public import Certificates.Certificate125541
public import Certificates.Certificate125542

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.GenD13

open CFSG.Monster CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7

theorem closure_genD13_eq_top :
    Subgroup.closure (Set.range fun i : Fin genD13Gens.size => gw genD13Gens[i]) = ⊤ :=
  closure_eq_top_of_prod
    (prodStepsOK_append (prodStepsOK_append (prodStepsOK_append (prodStepsOK_append (prodStepsOK_append (prodStepsOK_append (prodStepsOK_append (prodStepsOK_append (prodStepsOK_append (prodStepsOK_append (prodStepsOK_append (prodStepsOK_of_prodCheck Certificates.certificate125530)
      (prodStepsOK_of_prodCheck Certificates.certificate125531))
      (prodStepsOK_of_prodCheck Certificates.certificate125532))
      (prodStepsOK_of_prodCheck Certificates.certificate125533))
      (prodStepsOK_of_prodCheck Certificates.certificate125534))
      (prodStepsOK_of_prodCheck Certificates.certificate125535))
      (prodStepsOK_of_prodCheck Certificates.certificate125536))
      (prodStepsOK_of_prodCheck Certificates.certificate125537))
      (prodStepsOK_of_prodCheck Certificates.certificate125538))
      (prodStepsOK_of_prodCheck Certificates.certificate125539))
      (prodStepsOK_of_prodCheck Certificates.certificate125540))
      (prodStepsOK_of_prodCheck Certificates.certificate125541))
    Certificates.certificate125542

end CFSG.AGLEmbedding.Norton.GenD13
