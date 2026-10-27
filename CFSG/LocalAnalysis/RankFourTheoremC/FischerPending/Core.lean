module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXWeakCoreSaturation

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

structure ObstructionSetting (G : Type) [Group G] [Finite G] : Prop where
  charTwo : IsCharTwoType G
  exists_core : ∀ p ∈ rankThreeSigmaA G, ∀ P : Sylow p G, ∃ M : Subgroup G, IsCoreMaxLocal p P M
  three_le_pRank : ∀ p ∈ rankThreeSigmaA G, ∀ P : Sylow p G, 3 ≤ Open.pRank p (P : Subgroup G)

namespace ObstructionSetting

theorem sylow_le (hS : ObstructionSetting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) : (P : Subgroup G) ≤ M := by
  have h3 := hS.three_le_pRank p hp P
  exact (sylowGroup_le_aschCore 2 p (P : Subgroup G) (by omega) h3).trans hM.2

theorem exists_isCoreMaxLocal (hS : ObstructionSetting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    (P : Sylow p G) : ∃ M : Subgroup G, IsCoreMaxLocal p P M ∧ (P : Subgroup G) ≤ M := by
  obtain ⟨M, hM⟩ := hS.exists_core p hp P
  exact ⟨M, hM, hS.sylow_le hp hM⟩

theorem exists_elemAbelian_card_eq (hS : ObstructionSetting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) (P : Sylow p G) :
    ∃ A : Subgroup G, A ≤ P ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 3 := by
  have hprime := sigmaA_prime p hp
  have h3 := hS.three_le_pRank p hp P
  obtain ⟨E, hEP, hE, hEc⟩ := pRank_attained p (P : Subgroup G) (by omega)
  have hdvd : p ^ 3 ∣ Nat.card E := hEc ▸ pow_dvd_pow p h3
  obtain ⟨A, hAc, -, hAE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hprime (H := ⊥) (L := E) (by simp) hdvd bot_le
  exact ⟨A, hAE.trans hEP, hE.mono hAE, hAc⟩

theorem normalizer_sylow_le (hS : ObstructionSetting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) :
    normalizer ((P : Subgroup G) : Set G) ≤ M := by
  have hP3 := hS.three_le_pRank p hp P
  refine (aschCore_normalizer_le 2 p (P : Subgroup G) (P : Subgroup G) le_rfl (by omega) ?_).trans
    hM.2
  rwa [sup_eq_left.mpr inf_le_left]

theorem le_of_elemAbelian_normalizes (hS : ObstructionSetting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {E K : Subgroup G} (hEP : E ≤ P) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (hK : ¬ p ∣ Nat.card K) (hEK : E ≤ normalizer (K : Set G)) : K ≤ M := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hP3 := hS.three_le_pRank p hp P
  have hrank : 3 ≤ CFSG.Assembly.pRank p (⊤ : Subgroup G) := by
    have := pRank_mono p hprime.one_lt (le_top : (P : Subgroup G) ≤ ⊤)
    change 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G)
    omega
  obtain ⟨hPW, -, -, -, -, -, -, habsorb, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.weak_core_sylow_saturation_and_locality hprime hodd hrank P
      (W := CFSG.Assembly.LargeEvenWeakCore p (P : Subgroup G)) rfl
  have hKW := habsorb E K 3 (hEP.trans hPW) hE hEc le_rfl hK hEK
  exact hKW.trans hM.2

theorem normalizer_le_of_isSylowOf_two (hS : ObstructionSetting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {X T : Subgroup G} (hXM : X ≤ M) (hPX : (P : Subgroup G) ≤ normalizer (X : Set G))
    (hX : Nat.Coprime p (Nat.card X)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hTne : T ≠ ⊥) : normalizer (T : Set G) ≤ M :=
  normalizer_le_of_isSylowOf_two_of_le hD1 hp hM (hS.sylow_le hp hM) P.isPGroup'
    (hS.three_le_pRank p hp P) hXM hPX hX hT hTne

end ObstructionSetting

end CFSG.LocalAnalysis.RankFourTheoremC
