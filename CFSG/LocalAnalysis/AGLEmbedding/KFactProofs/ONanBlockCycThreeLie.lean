module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreePerfect
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabAutIrr
  CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def LieCyclicParabolicThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsClassicalTwoOrG2 Y → ∀ T J : Subgroup Y,
    IsSylowTwoOf T ⊤ → Subgroup.normalizer (T : Set Y) ≤ J →
      J ≠ Subgroup.normalizer (T : Set Y) → J ≠ ⊤ →
        HasE9 Y ∨ Aut3Le Y ∨ ∃ P : Subgroup Y, P ≤ J ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P

section PSL

theorem hasE9_psl_three_of_even {Y : Type} [Group Y] {f : ℕ}
    (h : StatedClassicalModel Y .PSL 3 2 f) (hf : Even f) : HasE9 Y := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL h
  have h3 : 3 ∣ Nat.card Kˣ := by
    obtain ⟨k, hk⟩ := hf
    rw [Nat.card_units, hK, hk, ← two_mul, pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hω : (g : K) ^ 3 = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hω1 : (g : K) ≠ 1 := by
    intro h1
    have : g = 1 := Units.ext h1
    rw [this, orderOf_one] at hg
    omega
  exact hasE9_of_mulEquiv e.symm (hasE9_projectiveSL_three hω hω1)

theorem lieCyclicThree_of_model_psl {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSL n 2 f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hJtop : J ≠ ⊤) :
    HasE9 Y ∨ Aut3Le Y ∨ ∃ P : Subgroup Y, P ≤ J ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  have h' := h
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ePSL := (projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm
  rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | hm
  · exfalso
    obtain ⟨i, j, hij⟩ := (borelQuotient_sl ePSL).exists_two_nodes T J hNJ hJ hJtop
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    exact hij (Fin.ext (by omega))
  · by_cases hfe : Even f
    · exact Or.inl (hasE9_psl_three_of_even h' hfe)
    · by_cases hf1 : f = 1
      · subst hf1
        exact Or.inr (Or.inl (aut3Le_of_model_psl_three_two h'))
      · refine Or.inr (Or.inr (exists_perfect_psl ?_ ePSL T J hNJ hJ))
        have hf3 : 2 ≤ f := by
          have := h'.1.2.1
          omega
        have h4 : 4 ≤ Finset.univ.card (α := F) := by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
        obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
        exact ⟨s, hs⟩
  · exact Or.inl (hasE9_psl_of_three_le hm ePSL)

end PSL

theorem lieCyclicParabolicThree_of (hG2 : LieCyclicG2) : LieCyclicParabolicThree := by
  intro Y _ _ hY T J hT hNJ hJ hJtop
  obtain ⟨T', rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  rcases isClassicalTwoOrG2_cases hY with ⟨t, n, f, ht, h⟩ | hG | hS
  · rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact lieCyclicThree_of_model_psl h T' J hNJ hJ hJtop
    · exact Or.inl (hasE9_of_model_psu_of_parabolic h T' J hNJ hJ hJtop)
    · exact Or.inl (hasE9_of_model_psp h)
    · exact Or.inl (hasE9_of_model_pomegaPlus h)
    · exact Or.inl (hasE9_of_model_pomegaMinus h)
  · exact Or.inl (hG2 Y hG)
  · rcases hasE9_or_aut3Le_of_small hS with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem lieCyclicOrthogonalThree : ∀ (Y : Type) [Group Y] [Finite Y], IsOrthogonalTwo Y → HasE9 Y ∨ Aut3Le Y := by
  intro Y _ _ hY
  rcases hY with ⟨⟨d, hv⟩, ⟨m, q, hq, hdm⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hp2 := p_eq_two_of_card_eq_two hq
    rcases hdm with rfl | rfl | ⟨rfl, rfl⟩
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even m q hv hp2 e
      rw [hp2] at h
      exact Or.inl (hasE9_of_model_pomegaPlus h)
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even m q hv hp2 e
      rw [hp2] at h
      exact Or.inl (hasE9_of_model_pomegaMinus h)
    · have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      rw [hp2] at h
      exact Or.inl (hasE9_of_model_psu h (by norm_num))
  · rcases hn with rfl | rfl | rfl
    · exact Or.inr (aut3Le_of_mulEquiv e.symm aut3Le_alternatingGroup_five)
    · exact Or.inl (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup (by norm_num)))
    · exact Or.inl (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup (by norm_num)))

end CFSG.AGLEmbedding.BlockCyc
