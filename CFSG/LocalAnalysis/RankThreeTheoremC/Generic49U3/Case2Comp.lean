module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

namespace Case2Data

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

private theorem pow_pow_eq_one_of_mem_sylow (S : Sylow p Y) {a : Y} (ha : a ∈ (S : Subgroup Y)) :
    ∃ k : ℕ, a ^ (p ^ k) = 1 := by
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨a, ha⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem mem_normalizer_of_pow_coprime {H : Subgroup Y} {y : Y} {n : ℕ}
    (hy : y ^ n = 1) {m : ℕ} (hm : Nat.Coprime m n) (hym : y ^ m ∈ normalizer (H : Set Y)) :
    y ∈ normalizer (H : Set Y) := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm hn
    have h1 : y = (y ^ m) ^ k := by
      rw [← pow_mul, pow_eq_pow_mod (m * k) hy, hk, pow_one]
    rw [h1]
    exact pow_mem hym k
  · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · have hm1 : m = 1 := by simpa using hm
      subst hm1
      simpa using hym
    · have hy1 : y = 1 := by simpa using hy
      subst hy1
      exact one_mem _

theorem mem_normalizer_of_pElement (h : Case2Data p P T D F x) {y : Y}
    (hy : ∃ k : ℕ, y ^ (p ^ k) = 1) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    y ∈ normalizer (L : Set Y) := by
  classical
  obtain ⟨k, hk⟩ := hy
  have hp5 : 5 ≤ p := h.five
  by_contra hyL
  set f : ℕ → Subgroup Y := fun i => L.map (MulAut.conj (y ^ i)).toMonoidHom with hf
  have hfK : ∀ i, IsComponentOf (f i) ⊤ := fun i =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (y ^ i)) L).mpr hL
  have hinj : Set.InjOn f (Finset.range 4 : Set ℕ) := by
    have key : ∀ i j : ℕ, i < j → j < 4 → f i ≠ f j := by
      intro i j hij hj hfij
      apply hyL
      refine mem_normalizer_of_pow_coprime hk (m := j - i) ?_ ?_
      · have hcop : Nat.Coprime (j - i) p :=
          (Nat.coprime_of_lt_prime (by omega) (by omega) h.prime).symm
        exact Nat.Coprime.pow_right k hcop
      · rw [mem_normalizer_iff_map_conj_eq]
        have h1 : f j = (f (j - i)).map (MulAut.conj (y ^ i)).toMonoidHom := by
          simp only [hf]
          rw [← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, ← pow_add,
            Nat.add_sub_cancel' hij.le]
        rw [h1] at hfij
        exact (map_injective (MulAut.conj (y ^ i)).injective hfij).symm
    intro i hi j hj hfij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with hlt | heq | hlt
    · exact absurd hfij (key i j hlt hj)
    · exact heq
    · exact absurd hfij.symm (key j i hlt hi)
  have hcard := CFSG.LocalAnalysis.RankThreeTheoremC.card_le_pRank_of_isComponentOf h.prime
    (by omega) h.core ((Finset.range 4).image f) (fun K' hK' => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK'
      exact hfK i)
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  have hrank := h.rank
  omega

theorem P_le_normalizer (h : Case2Data p P T D F x) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    P ≤ normalizer (L : Set Y) := by
  intro a ha
  obtain ⟨S, hS⟩ := h.sylow
  rw [← hS] at ha
  exact mem_normalizer_of_pElement h (pow_pow_eq_one_of_mem_sylow S ha) hL

theorem exists_mem_P_inf (h : Case2Data p P T D F x) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    ∃ t ∈ P ⊓ L, orderOf t = p ∧ t ∉ centralizer (L : Set Y) := by
  obtain ⟨S, hS⟩ := h.sylow
  subst hS
  have hp2 : p ≠ 2 := by have := h.five; omega
  exact exists_mem_sylow_inf_component h.prime hp2 h.core S hL

end Case2Data

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
