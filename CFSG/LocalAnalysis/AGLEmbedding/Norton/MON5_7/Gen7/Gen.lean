module

public import Certificates.Certificate125340
public import Certificates.Certificate125341
public import Certificates.Certificate125342
public import Certificates.Certificate125343
public import Certificates.Certificate125344
public import Certificates.Certificate125345
public import Certificates.Certificate125346
public import Certificates.Certificate125347
public import Certificates.Certificate125348
public import Certificates.Certificate125349
public import Certificates.Certificate125350
public import Certificates.Certificate125351

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON5_7.Gen7

open CFSG.Monster CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7

theorem closure_gen7_eq_top :
    Subgroup.closure (Set.range fun i : Fin gen7Gens.size => gw gen7Gens[i]) = ⊤ := by
  have h0 := prodStepsOK_of_prodCheck Certificates.certificate125340
  have h1 := prodStepsOK_append h0 (prodStepsOK_of_prodCheck Certificates.certificate125341)
  have h2 := prodStepsOK_append h1 (prodStepsOK_of_prodCheck Certificates.certificate125342)
  have h3 := prodStepsOK_append h2 (prodStepsOK_of_prodCheck Certificates.certificate125343)
  have h4 := prodStepsOK_append h3 (prodStepsOK_of_prodCheck Certificates.certificate125344)
  have h5 := prodStepsOK_append h4 (prodStepsOK_of_prodCheck Certificates.certificate125345)
  have h6 := prodStepsOK_append h5 (prodStepsOK_of_prodCheck Certificates.certificate125346)
  have h7 := prodStepsOK_append h6 (prodStepsOK_of_prodCheck Certificates.certificate125347)
  have h8 := prodStepsOK_append h7 (prodStepsOK_of_prodCheck Certificates.certificate125348)
  have h9 := prodStepsOK_append h8 (prodStepsOK_of_prodCheck Certificates.certificate125349)
  have h10 := prodStepsOK_append h9 (prodStepsOK_of_prodCheck Certificates.certificate125350)
  exact closure_eq_top_of_prod h10 Certificates.certificate125351

end CFSG.AGLEmbedding.Norton.MON5_7.Gen7
