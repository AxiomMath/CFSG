module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Spec
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Set.Card.Arithmetic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

open Subgroup MulAction

variable {V : Type} [CommGroup V] {M : Subgroup (MulAut V)} {t : V} {O : Fin 5 → Set V}

theorem simple_subset_or_disjoint (hO : OrbitData M t O) {B : Set V}
    (hinv : ∀ m ∈ M, ∀ b ∈ B, m b ∈ B) (i : Fin 5) : O i ⊆ B ∨ Disjoint (O i) B := by
  obtain ⟨x, hx⟩ := hO.isOrbit i
  by_cases h : ∃ b, b ∈ O i ∧ b ∈ B
  · left
    obtain ⟨b, hbO, hbB⟩ := h
    have hbx : orbit M b = O i := by
      rw [hx] at hbO ⊢
      exact orbit_eq_iff.mpr hbO
    rw [← hbx]
    rintro _ ⟨m, rfl⟩
    exact hinv m m.2 b hbB
  · right
    rw [Set.disjoint_left]
    exact fun b hbO hbB => h ⟨b, hbO, hbB⟩

theorem simple_ncard_invariant [Finite V] (hO : OrbitData M t O) {B : Set V} (htB : t ∈ B)
    (h1 : (1 : V) ∉ B) (hinv : ∀ m ∈ M, ∀ b ∈ B, m b ∈ B) :
    ∃ a : Fin 5 → ℕ, (∀ i, a i ≤ 1 ∧ (a i = 1 ↔ O i ⊆ B)) ∧
      B.ncard = 1 + (22 * a 0 + 22 * a 1 + 231 * a 2 + 231 * a 3 + 1540 * a 4) := by
  classical
  have hdich := simple_subset_or_disjoint hO hinv
  have hB : B = insert t (⋃ i, O i ∩ B) := by
    ext b
    constructor
    · intro hb
      rcases hO.cover b (fun h => h1 (h ▸ hb)) with rfl | ⟨i, hi⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨i, hi, hb⟩)
    · rintro (rfl | hb)
      · exact htB
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hb
        exact hi.2
  have hnot : t ∉ ⋃ i, O i ∩ B := fun h => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact hO.not_mem_t i hi.1
  have hdisj : Pairwise (Function.onFun Disjoint fun i => O i ∩ B) := fun i j hij =>
    (hO.disjoint i j hij).mono Set.inter_subset_left Set.inter_subset_left
  have hterm : ∀ i, (O i ∩ B).ncard = ![22, 22, 231, 231, 1540] i * if O i ⊆ B then 1 else 0 := by
    intro i
    by_cases hs : O i ⊆ B
    · rw [Set.inter_eq_left.mpr hs, hO.ncard i]
      simp [hs]
    · rw [Set.disjoint_iff_inter_eq_empty.mp ((hdich i).resolve_left hs), Set.ncard_empty]
      simp [hs]
  have hsum : (⋃ i, O i ∩ B).ncard =
      22 * (if O 0 ⊆ B then 1 else 0) + 22 * (if O 1 ⊆ B then 1 else 0) +
        231 * (if O 2 ⊆ B then 1 else 0) + 231 * (if O 3 ⊆ B then 1 else 0) +
          1540 * (if O 4 ⊆ B then 1 else 0) := by
    rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite _) hdisj, finsum_eq_sum_of_fintype]
    simp only [hterm, Fin.sum_univ_five]
    simp
  refine ⟨fun i => if O i ⊆ B then 1 else 0, fun i => ?_, ?_⟩
  · by_cases hs : O i ⊆ B <;> simp [hs]
  · calc B.ncard = (insert t (⋃ i, O i ∩ B)).ncard := congrArg Set.ncard hB
      _ = (⋃ i, O i ∩ B).ncard + 1 := Set.ncard_insert_of_notMem hnot (Set.toFinite _)
      _ = _ := by rw [hsum, add_comm]

theorem simple_zero_subset [Finite V] (hO : OrbitData M t O) {Ω : Set V} (hΩ : Ω.ncard = 276)
    (htΩ : t ∈ Ω) (h1 : (1 : V) ∉ Ω) (hinv : ∀ m ∈ M, ∀ b ∈ Ω, m b ∈ Ω) : O 0 ⊆ Ω := by
  obtain ⟨a, ha, hn⟩ := simple_ncard_invariant hO htΩ h1 hinv
  have h0 : a 0 = 1 := by
    have := (ha 0).1
    have := (ha 1).1
    have := (ha 2).1
    have := (ha 3).1
    have := (ha 4).1
    omega
  exact (ha 0).2.mp h0

theorem simple_ncard_block [Finite V] (hO : OrbitData M t O) {Ω B : Set V} (hΩ : Ω.ncard = 276)
    (htΩ : t ∈ Ω) (h1 : (1 : V) ∉ Ω) (hΩinv : ∀ m ∈ M, ∀ b ∈ Ω, m b ∈ Ω) (hBΩ : B ⊆ Ω)
    (htB : t ∈ B) (hBinv : ∀ m ∈ M, ∀ b ∈ B, m b ∈ B) (h01 : O 0 ⊆ B ↔ O 1 ⊆ B)
    (hdvd : B.ncard ∣ 276) : B.ncard = 1 ∨ B.ncard = 276 := by
  obtain ⟨a, ha, hn⟩ := simple_ncard_invariant hO htΩ h1 hΩinv
  obtain ⟨b, hb, hm⟩ := simple_ncard_invariant hO htB (fun h => h1 (hBΩ h)) hBinv
  have hab : ∀ i, b i ≤ a i := by
    intro i
    have := (ha i).1
    have := (hb i).1
    by_cases hbi : b i = 1
    · have hsub : O i ⊆ B := (hb i).2.mp hbi
      have : a i = 1 := (ha i).2.mpr (hsub.trans hBΩ)
      omega
    · omega
  have h01' : b 0 = 1 ↔ b 1 = 1 := ((hb 0).2.trans h01).trans (hb 1).2.symm
  have hcases : B.ncard = 1 ∨ B.ncard = 45 ∨ B.ncard = 232 ∨ B.ncard = 276 := by
    have := (ha 0).1
    have := (ha 1).1
    have := (ha 2).1
    have := (ha 3).1
    have := (ha 4).1
    have := (hb 0).1
    have := (hb 1).1
    have := (hb 2).1
    have := (hb 3).1
    have := (hb 4).1
    have := hab 0
    have := hab 1
    have := hab 2
    have := hab 3
    have := hab 4
    omega
  rcases hcases with h | h | h | h
  · exact Or.inl h
  · rw [h] at hdvd
    exact absurd hdvd (by omega)
  · rw [h] at hdvd
    exact absurd hdvd (by omega)
  · exact Or.inr h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44
