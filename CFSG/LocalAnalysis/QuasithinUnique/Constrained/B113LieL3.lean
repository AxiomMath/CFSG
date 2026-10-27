module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieRes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieLinCent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.QuasithinUnique.B113Lie

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem l3_sylowFacts {S : Type} [Group S] [Finite S] {f : ℕ} (_hf : 2 ≤ f)
    (hX : StatedClassicalModel S .PSL 3 2 f) {T : Subgroup S} (hT : IsSylowTwoOf T ⊤) :
    SylowFacts S T := by
  have hS : IsSimpleGroup S := (CFSG.LieType.Simplicity.fam_PSL_simplicity S 3 2 f hX).2
  obtain ⟨K, hF, hFin, hCh, φ, -, -, hRes, -⟩ := Setup.X7a.even_rank_two_residual_linear hX hT
  have hchar : ∀ j : Fin 2, CharTwo
      ((projStabilizer (flagSpace 3 K ((j : ℕ) + 1))).map φ.symm.toMonoidHom) := by
    intro j
    exact CFSG.QuasithinUnique.Ch1.charTwo_map_mulEquiv φ.symm
      (Lin.charTwo_projStabilizer (by omega) (by have := j.isLt; omega))
  have h2 : 2 ∣ Nat.card S := by
    have := Lin.two_dvd_card_projectiveSL (n := 3) (K := K) (by norm_num)
    rwa [← Nat.card_congr φ.toEquiv] at this
  exact sylowFacts_of_residualAt hT (ne_bot_of_two_dvd hT h2) hRes hchar

end CFSG.QuasithinUnique.B113Lie
