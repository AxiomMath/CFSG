module

public import Certificates.Certificate125000
public import Certificates.Certificate125001
public import Certificates.Certificate125002
public import Certificates.Certificate125003
public import Certificates.Certificate125004
public import Certificates.Certificate125005
public import Certificates.Certificate125006
public import Certificates.Certificate125007
public import Certificates.Certificate125008

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.Gen13

open CFSG.Monster CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7

theorem closure_gen13_eq_top :
    Subgroup.closure (Set.range fun i : Fin gen13Gens.size => gw gen13Gens[i]) = ⊤ := by
  have h0 := prodStepsOK_of_prodCheck Certificates.certificate125000
  have h1 := prodStepsOK_append h0 (prodStepsOK_of_prodCheck Certificates.certificate125001)
  have h2 := prodStepsOK_append h1 (prodStepsOK_of_prodCheck Certificates.certificate125002)
  have h3 := prodStepsOK_append h2 (prodStepsOK_of_prodCheck Certificates.certificate125003)
  have h4 := prodStepsOK_append h3 (prodStepsOK_of_prodCheck Certificates.certificate125004)
  have h5 := prodStepsOK_append h4 (prodStepsOK_of_prodCheck Certificates.certificate125005)
  have h6 := prodStepsOK_append h5 (prodStepsOK_of_prodCheck Certificates.certificate125006)
  have h7 := prodStepsOK_append h6 (prodStepsOK_of_prodCheck Certificates.certificate125007)
  exact closure_eq_top_of_prod h7 Certificates.certificate125008

end CFSG.AGLEmbedding.Norton.Gen13
