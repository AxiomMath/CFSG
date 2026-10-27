module

public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinBender
import CFSG.RankThree.GF2n.Tim78S48PhaseSzGrp

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

theorem eq_bot_of_isPerfect_of_le_normalizer_of_lieModel_PSU3 {X : Type} [Group X] [Finite X]
    {n : ℕ} (hL : CFSG.Blueprint.LieModel X .PSU 3 2 n) {D K : Subgroup X} (hD : IsPGroup 2 D)
    (hD1 : D ≠ ⊥) (hK : Group.IsPerfect K) (hKD : K ≤ Subgroup.normalizer (D : Set X)) :
    K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hDQ⟩ := hD.exists_le_sylow
  obtain ⟨hSE, ⟨D', hD'c, -, -, hsup⟩, -⟩ := fusionBenderBorel_of_lieModel_PSU3 hL Q
  have hEven : Even (Nat.card D) := by
    obtain ⟨k, hk⟩ := hD.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hD1 (Subgroup.eq_bot_of_card_eq D (by rw [hk, pow_zero]))
    rw [hk]
    exact Nat.even_pow.mpr ⟨even_two, hk0⟩
  have hKB : K ≤ Subgroup.normalizer ((Q : Subgroup X) : Set X) :=
    hKD.trans (CFSG.RankThree.GF2n.Tim78.normalizer_le_of_fusionStronglyEmbedded hSE
      (hDQ.trans Subgroup.le_normalizer) hEven)
  haveI := CFSG.QuasithinUnique.Unc25G2.BenderBorel.isSolvable_normalizer_of_sup_cyclic
    Q.isPGroup' hD'c hsup
  haveI : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKB)
  haveI := hK
  by_contra hne
  haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  exact Group.IsPerfect.not_isSolvable K inferInstance

end CFSG.LocalAnalysis.EvenBN.GMSK
