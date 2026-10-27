module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SurvivorGlue

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem survivor_chain_data [Finite K] [CharP K 2] {r ε : ℕ} (h : UnitaryFieldData 2 1 K)
    (hε : ε ≤ 1) (hn : 4 ≤ 2 * r + ε) {I : Set ℕ} (hIne : I.Nonempty) (hIsub : I ⊆ Set.Icc 1 r)
    (hshort : ∀ j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ < j₂ → j₂ < r → j₁ ∉ I → j₂ ∉ I → False)
    (htail : 2 ≤ r → r ∉ I → r - 1 ∉ I → False)
    {W : ℕ → Submodule K (Fin (2 * r + ε) → K)}
    (hWd : ∀ i ∈ I, Module.finrank K (W i) = i ∧ IsTotallyIsotropicSU (2 ^ 1) (W i))
    (hWm : ∀ i ∈ I, ∀ j ∈ I, i ≤ j → W i ≤ W j)
    (Dt : Subgroup (StatedSU (2 * r + ε) (2 ^ 1) K))
    (hDtW : ∀ y ∈ Dt, ∀ i ∈ I, ∀ w ∈ W i,
      ((y : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ w ∈ W i)
    (hDt : ⁅Dt, Dt⁆ = Dt) {d : StatedSU (2 * r + ε) (2 ^ 1) K} (hd : d ∈ Dt)
    (hds : (d : GL (Fin (2 * r + ε)) K) ∉ StatedScalars (Fin (2 * r + ε)) K) :
    ∃ (S : Finset ℕ) (a : ℕ → ℕ) (k₀ : ℕ), (∀ i, i ∈ S ↔ i ∈ I) ∧
      SUChain h (2 * r + ε) Dt S a W ∧ 1 ≤ k₀ ∧ k₀ ≤ S.card ∧ a k₀ = a (k₀ - 1) + 2 ∧
      (∀ k, 1 ≤ k → k ≤ S.card → k ≠ k₀ → a k = a (k - 1) + 1) ∧
      2 * r + ε - 2 * a S.card ≤ 3 := by
  classical
  have := h.charP
  have hr2 : 2 ≤ r := by omega
  set S : Finset ℕ := (Finset.Icc 1 r).filter (· ∈ I) with hSdef
  have hSI : ∀ i, i ∈ S ↔ i ∈ I := fun i =>
    ⟨fun hi => (Finset.mem_filter.mp hi).2, fun hi => Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr (by simpa using hIsub hi), hi⟩⟩
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hIne
    exact ⟨i, (hSI i).mpr hi⟩
  have hS'' : ∀ i ∈ S, 1 ≤ i ∧ i ≤ r := fun i hi => by
    simpa using hIsub ((hSI i).mp hi)
  have hS' : ∀ i ∈ S, i ≤ r := fun i hi => (hS'' i hi).2
  obtain ⟨a, ha⟩ := exists_enumeration S (fun i hi => (hS'' i hi).1)
  have hshortS : ∀ j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ < j₂ → j₂ < r → j₁ ∉ S → j₂ ∉ S → False :=
    fun j₁ j₂ h1 h2 h3 h4 h5 => hshort j₁ j₂ h1 h2 h3 (fun hh => h4 ((hSI j₁).mpr hh))
      (fun hh => h5 ((hSI j₂).mpr hh))
  have htailS : 2 ≤ r → r ∉ S → r - 1 ∉ S → False :=
    fun h1 h2 h3 => htail h1 (fun hh => h2 ((hSI r).mpr hh)) (fun hh => h3 ((hSI (r - 1)).mpr hh))
  have hc : SUChain h (2 * r + ε) Dt S a W :=
    { enum := ha
      ne := hSne
      mono := fun i hi j hj hij => hWm i ((hSI i).mp hi) j ((hSI j).mp hj) hij
      dim := fun i hi => (hWd i ((hSI i).mp hi)).1
      iso := fun i hi v hv w hw =>
        (ToralCensus.isTotallyIsotropicSU_iff h (W i)).mp (hWd i ((hSI i).mp hi)).2 v hv w hw
      stab := fun y hy i hi w hw => hDtW y hy i ((hSI i).mp hi) w hw
      perf := hDt }
  have hlast := le_last_of_tail ha hSne hS' htailS hr2
  have htailb : 2 * r + ε - 2 * a S.card ≤ 3 := by omega
  by_cases hopen : ∃ j, 1 ≤ j ∧ j < r ∧ j ∉ I
  swap
  · exfalso
    push Not at hopen
    have hall : ∀ j, 1 ≤ j → j < r → j ∈ S := fun j h1 h2 => (hSI j).mpr (hopen j h1 h2)
    have hone := hc.eq_one_of_gaps_one
      (fun k hk1 hk2 => gap_eq_one_of_no_short_open ha hS' hall hk1 hk2) htailb d hd
    exact hds (by rw [hone, Subgroup.coe_one]; exact Subgroup.one_mem _)
  obtain ⟨j₀, hj1, hjr, hj₀⟩ := hopen
  obtain ⟨k₀, hk1, hk2, hplane, hother⟩ := exists_unique_plane_piece ha hSne hS'' hshortS htailS
    hj1 hjr (fun hh => hj₀ ((hSI j₀).mp hh))
  exact ⟨S, a, k₀, hSI, hc, hk1, hk2, hplane, hother, htailb⟩

@[expose] def SurvivorShapeTable (r ε : ℕ) (I : Set ℕ) (s k₀ m : ℕ) : Prop :=
  (r = 2 ∧ ε = 0 ∧ I = {2} ∧ s = 1 ∧ k₀ = 1 ∧ m = 0) ∨
  (r = 2 ∧ ε = 1 ∧ I = {2} ∧ s = 1 ∧ k₀ = 1 ∧ m = 1) ∨
  (r = 3 ∧ ε = 0 ∧ I = {2} ∧ s = 1 ∧ k₀ = 1 ∧ m = 2) ∨
  (r = 3 ∧ ε = 0 ∧ I = {1, 3} ∧ s = 2 ∧ k₀ = 2 ∧ m = 0) ∨
  (r = 3 ∧ ε = 0 ∧ I = {2, 3} ∧ s = 2 ∧ k₀ = 1 ∧ m = 0) ∨
  (r = 3 ∧ ε = 1 ∧ I = {1, 3} ∧ s = 2 ∧ k₀ = 2 ∧ m = 1) ∨
  (r = 3 ∧ ε = 1 ∧ I = {2, 3} ∧ s = 2 ∧ k₀ = 1 ∧ m = 1) ∨
  (r = 3 ∧ ε = 1 ∧ I = {2} ∧ s = 1 ∧ k₀ = 1 ∧ m = 3)

namespace SurvivorShapeTable

variable {r ε : ℕ} {I : Set ℕ} {s k₀ m : ℕ}

theorem m_le_two_of_ne (h : SurvivorShapeTable r ε I s k₀ m) (hne : ¬ (r = 3 ∧ ε = 1 ∧ I = {2})) :
    m ≤ 2 := by
  unfold SurvivorShapeTable at h
  rcases h with h | h | h | h | h | h | h | h <;> first | omega | exact absurd ⟨h.1, h.2.1, h.2.2.1⟩ hne

theorem eq_last_of_not_le_two (h : SurvivorShapeTable r ε I s k₀ m) (hm : ¬ m ≤ 2) :
    r = 3 ∧ ε = 1 ∧ I = {2} := by
  by_contra hne
  exact hm (h.m_le_two_of_ne hne)

end SurvivorShapeTable

theorem survivor_shape {r ε : ℕ} {I : Set ℕ} {S : Finset ℕ} {a : ℕ → ℕ}
    (hSI : ∀ i, i ∈ S ↔ i ∈ I) (ha : Enumeration S a) {k₀ : ℕ} (hk1 : 1 ≤ k₀)
    (hk2 : k₀ ≤ S.card) (hplane : a k₀ = a (k₀ - 1) + 2)
    (hsurv : (r = 2 ∧ ε = 0 ∧ I = {2}) ∨ (r = 2 ∧ ε = 1 ∧ I = {2}) ∨
      (r = 3 ∧ ε = 0 ∧ I = {2}) ∨ (r = 3 ∧ ε = 0 ∧ I = {1, 3}) ∨ (r = 3 ∧ ε = 0 ∧ I = {2, 3}) ∨
      (r = 3 ∧ ε = 1 ∧ I = {1, 3}) ∨ (r = 3 ∧ ε = 1 ∧ I = {2, 3}) ∨ (r = 3 ∧ ε = 1 ∧ I = {2})) :
    SurvivorShapeTable r ε I S.card k₀ (2 * r + ε - 2 * a S.card) := by
  unfold SurvivorShapeTable
  have hone : ∀ x : ℕ, I = {x} → S = {x} := fun x hI => by
    ext i; rw [hSI, hI]; simp
  have htwo : ∀ x y : ℕ, I = {x, y} → S = {x, y} := fun x y hI => by
    ext i; rw [hSI, hI]; simp
  have hzero := ha.zero
  have hlt := ha.lt
  have hmem := ha.mem
  have key1 : S = {2} → S.card = 1 ∧ k₀ = 1 ∧ a 1 = 2 := by
    rintro rfl
    have hc : ({2} : Finset ℕ).card = 1 := rfl
    rw [hc] at hk2 hmem
    have hk : k₀ = 1 := by omega
    subst hk
    have h1 := hmem 1 le_rfl le_rfl
    simp only [Finset.mem_singleton] at h1
    exact ⟨hc, rfl, h1⟩
  have key23 : S = {2, 3} → S.card = 2 ∧ k₀ = 1 ∧ a 1 = 2 ∧ a 2 = 3 := by
    rintro rfl
    have hc : ({2, 3} : Finset ℕ).card = 2 := rfl
    rw [hc] at hk2 hmem hlt
    have h1 := hmem 1 le_rfl (by omega)
    have h2 := hmem 2 (by omega) le_rfl
    have h12 : a 1 < a 2 := hlt 1 (by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have : k₀ = 1 ∨ k₀ = 2 := by omega
    rcases this with rfl | rfl
    · refine ⟨hc, rfl, ?_⟩
      simp only [Nat.sub_self, hzero] at hplane
      omega
    · simp at hplane
      omega
  have key13 : S = {1, 3} → S.card = 2 ∧ k₀ = 2 ∧ a 1 = 1 ∧ a 2 = 3 := by
    rintro rfl
    have hc : ({1, 3} : Finset ℕ).card = 2 := rfl
    rw [hc] at hk2 hmem hlt
    have h1 := hmem 1 le_rfl (by omega)
    have h2 := hmem 2 (by omega) le_rfl
    have h12 : a 1 < a 2 := hlt 1 (by omega)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have : k₀ = 1 ∨ k₀ = 2 := by omega
    rcases this with rfl | rfl
    · simp only [Nat.sub_self, hzero] at hplane
      omega
    · simp at hplane
      refine ⟨hc, rfl, ?_⟩
      omega
  rcases hsurv with ⟨rfl, rfl, hI⟩ | ⟨rfl, rfl, hI⟩ | ⟨rfl, rfl, hI⟩ | ⟨rfl, rfl, hI⟩ |
    ⟨rfl, rfl, hI⟩ | ⟨rfl, rfl, hI⟩ | ⟨rfl, rfl, hI⟩ | ⟨rfl, rfl, hI⟩
  · obtain ⟨c, hk, h1⟩ := key1 (hone 2 hI)
    refine Or.inl ⟨rfl, rfl, hI, c, hk, ?_⟩
    rw [c, h1]
  · obtain ⟨c, hk, h1⟩ := key1 (hone 2 hI)
    refine Or.inr (Or.inl ⟨rfl, rfl, hI, c, hk, ?_⟩)
    rw [c, h1]
  · obtain ⟨c, hk, h1⟩ := key1 (hone 2 hI)
    refine Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hI, c, hk, ?_⟩))
    rw [c, h1]
  · obtain ⟨c, hk, h1, h2⟩ := key13 (htwo 1 3 hI)
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hI, c, hk, ?_⟩)))
    rw [c, h2]
  · obtain ⟨c, hk, h1, h2⟩ := key23 (htwo 2 3 hI)
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hI, c, hk, ?_⟩))))
    rw [c, h2]
  · obtain ⟨c, hk, h1, h2⟩ := key13 (htwo 1 3 hI)
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hI, c, hk, ?_⟩)))))
    rw [c, h2]
  · obtain ⟨c, hk, h1, h2⟩ := key23 (htwo 2 3 hI)
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hI, c, hk, ?_⟩))))))
    rw [c, h2]
  · obtain ⟨c, hk, h1⟩ := key1 (hone 2 hI)
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hI, c, hk, ?_⟩))))))
    rw [c, h1]

end CFSG.HardMathSupport.Curtis.UnitaryLevi
