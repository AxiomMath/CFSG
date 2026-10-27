module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsSmall

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21bAbsProof

open KFactsSmall
open scoped Pointwise

theorem fixed_of_orbits {G X : Type} [Group G] [MulAction G X] [Finite X] {E U : Subgroup G}
    (hperm : Permutable E U) (hE : Nat.card E = 9) {x₀ : X} (hx₀ : ∀ u ∈ U, u • x₀ = x₀)
    {L A : Set X} {q : ℕ} (hL : ∀ y ∈ L, ∀ y' ∈ L, ∃ u ∈ U, u • y = y') (hLc : L.ncard = q)
    (hx₀L : x₀ ∉ L) (hA : ∀ y ∈ A, ∀ y' ∈ A, ∃ u ∈ U, u • y = y') (hAc : 9 < A.ncard)
    (hcover : ∀ y : X, y = x₀ ∨ y ∈ L ∨ y ∈ A) (hq4 : 4 ≤ q) (hq8 : q ≠ 8) :
    ∀ e ∈ E, e • x₀ = x₀ := by
  intro e he
  by_contra hne
  have hperm' : (U : Set G) * (E : Set G) = (E : Set G) * (U : Set G) := hperm.symm
  set O : Set X := MulAction.orbit E x₀ with hO
  have hxO : x₀ ∈ O := MulAction.mem_orbit_self x₀
  have hdvd : O.ncard ∣ 9 := by
    have h1 := MulAction.index_stabilizer E x₀
    have h2 := Subgroup.index_dvd_card (MulAction.stabilizer E x₀)
    rw [h1, hE] at h2
    exact h2
  have hle9 : O.ncard ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
  have hU : ∀ u ∈ U, ∀ y ∈ O, u • y ∈ O := by
    intro u hu y hy
    obtain ⟨e', rfl⟩ := hy
    have hmem : u * (e' : G) ∈ (U : Set G) * (E : Set G) := ⟨u, hu, e', e'.2, rfl⟩
    rw [hperm'] at hmem
    obtain ⟨e'', he'', u'', hu'', hprod⟩ := hmem
    refine ⟨⟨e'', he''⟩, ?_⟩
    show e'' • x₀ = u • (e' • x₀)
    rw [Subgroup.smul_def, ← mul_smul, ← hprod, mul_smul, hx₀ u'' hu'']
  have hAO : ∀ y ∈ A, y ∈ O → A ⊆ O := by
    intro y hyA hyO y' hy'
    obtain ⟨u, hu, rfl⟩ := hA y hyA y' hy'
    exact hU u hu y hyO
  have hLO : ∀ y ∈ L, y ∈ O → L ⊆ O := by
    intro y hyL hyO y' hy'
    obtain ⟨u, hu, rfl⟩ := hL y hyL y' hy'
    exact hU u hu y hyO
  have hA_not : ∀ y ∈ A, y ∉ O := by
    intro y hyA hyO
    have hsub := Set.ncard_le_ncard (hAO y hyA hyO) (Set.toFinite O)
    omega
  have hy : e • x₀ ∈ O := ⟨⟨e, he⟩, rfl⟩
  rcases hcover (e • x₀) with h | h | h
  · exact hne h
  · have hLsub := hLO _ h hy
    have hOsub : O ⊆ insert x₀ L := by
      intro z hz
      rcases hcover z with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · exact absurd hz (hA_not z h')
    have hOeq : O = insert x₀ L := Set.Subset.antisymm hOsub (Set.insert_subset hxO hLsub)
    have hcardO : O.ncard = q + 1 := by
      rw [hOeq, Set.ncard_insert_of_notMem hx₀L (Set.toFinite L), hLc]
    rw [hcardO] at hdvd hle9
    have hq9 : q ≤ 8 := by omega
    interval_cases q <;> omega
  · exact hA_not _ h hy

theorem permutable_map {G H : Type} [Group G] [Group H] (f : G →* H) {E U : Subgroup G}
    (h : Permutable E U) : Permutable (E.map f) (U.map f) := by
  have h' : (E : Set G) * (U : Set G) = (U : Set G) * (E : Set G) := h
  show ((E.map f : Subgroup H) : Set H) * ((U.map f : Subgroup H) : Set H) =
    ((U.map f : Subgroup H) : Set H) * ((E.map f : Subgroup H) : Set H)
  rw [Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul, h']

theorem le_normalizer_of_forward {G : Type} [Group G] (K U : Subgroup G)
    (h : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U) : K ≤ Subgroup.normalizer (U : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h k hk x
  · intro hx
    have h2 := h k⁻¹ (K.inv_mem hk) _ hx
    simpa [mul_assoc] using h2

end K21bAbsProof

end CFSG.LocalAnalysis.RankThreeUC.S15
