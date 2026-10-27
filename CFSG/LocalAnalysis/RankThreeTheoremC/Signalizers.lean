module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXWeakCoreSaturation

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_elemAbelian_normalizes (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) {E K : Subgroup G}
    (hEP : E ≤ P) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (hK : ¬ p ∣ Nat.card K)
    (hEK : E ≤ normalizer (K : Set G)) : K ≤ M := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hp hM).2
  have hrank : 3 ≤ CFSG.Assembly.pRank p (⊤ : Subgroup G) := by
    have := pRank_mono p hprime.one_lt (le_top : (P : Subgroup G) ≤ ⊤)
    change 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G)
    omega
  obtain ⟨hPW, -, -, -, -, -, -, habsorb, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.weak_core_sylow_saturation_and_locality hprime hodd hrank P
      (W := CFSG.Assembly.LargeEvenWeakCore p (P : Subgroup G)) rfl
  have hKW := habsorb E K 3 (hEP.trans hPW) hE hEc le_rfl hK hEK
  exact hKW.trans hM.2

end CFSG.LocalAnalysis.RankThreeTheoremC
