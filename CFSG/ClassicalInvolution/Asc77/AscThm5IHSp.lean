module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHPair
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSp
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHSpStruct

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

theorem t5BaseAt_nt_psp {k e : ℕ} : T5BaseAt p f .PSp k e Not :=
  t5BaseAt_nt_of_prod_layers (by decide) (by decide)
    (fun hp2 hq hadm => Balance.Bootstrap.layerGenerationPairAt_psp hp2 hq hadm)
    (fun hp2 hq _ _ _ _ π hπ y hy2 hyc => ⟨_, _, thm5IH_sp_centralizerProd hp2 hq hπ hy2 hyc⟩)

end CFSG.ClassicalInvolution.Asc77
