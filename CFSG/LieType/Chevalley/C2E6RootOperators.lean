module

public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def e6Root (k : Fin 72) : Fin Tag.E6.rank → ℤ := e6Certificate.root k

theorem length_e6Certificate : e6Certificate.roots.length = 72 := by decide

theorem isRoot_e6Root (k : Fin 72) : IsRoot Tag.E6 (e6Root k) :=
  RootCertificate.isRoot_root e6Certificate_check k (by rw [length_e6Certificate]; exact k.2)

theorem exists_e6Root_eq
    {v : Fin Tag.E6.rank → ℤ} (hv : IsRoot Tag.E6 v) :
    ∃ k : Fin 72, e6Root k = v := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq e6Certificate_check hv
  exact ⟨⟨k, length_e6Certificate ▸ hk⟩, rfl⟩

theorem isRoot_iff_exists_e6Root {v : Fin Tag.E6.rank → ℤ} :
    IsRoot Tag.E6 v ↔ ∃ k : Fin 72, e6Root k = v :=
  ⟨exists_e6Root_eq, fun ⟨k, hk⟩ => hk ▸ isRoot_e6Root k⟩

theorem e6_root_strings : ∀ (k : Fin 72) (i : Fin Tag.E6.rank),
    e6Root k ≠ Pi.single i 1 → e6Root k ≠ -Pi.single i 1 →
      (¬∃ k', e6Root k' = e6Root k + (2 : ℤ) • Pi.single i 1) ∧
      (¬∃ k', e6Root k' = e6Root k - (2 : ℤ) • Pi.single i 1) ∧
      ¬((∃ k', e6Root k' = e6Root k + Pi.single i 1) ∧
        (∃ k', e6Root k' = e6Root k - Pi.single i 1)) := by
  decide +kernel

theorem stringUp_add_stringDown_E6
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    {i : Fin Tag.E6.rank} (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    stringUp Tag.E6 i α ≤ 1 ∧ stringDown Tag.E6 i α ≤ 1 ∧
      stringUp Tag.E6 i α + stringDown Tag.E6 i α ≤ 1 := by
  obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  obtain ⟨k, rfl⟩ := exists_e6Root_eq hα
  obtain ⟨hp2, hq2, hpq⟩ := e6_root_strings k i h₁ h₂
  have hp : stringUp Tag.E6 i (e6Root k) ≤ 1 := by
    by_contra h
    refine hp2 (isRoot_iff_exists_e6Root.mp ((hs 2).mpr ⟨by omega, by omega⟩))
  have hq : stringDown Tag.E6 i (e6Root k) ≤ 1 := by
    by_contra h
    have := (hs (-2)).mpr ⟨by omega, by omega⟩
    rw [neg_smul, ← sub_eq_add_neg] at this
    exact hq2 (isRoot_iff_exists_e6Root.mp this)
  refine ⟨hp, hq, ?_⟩
  by_contra h
  have h1 : stringUp Tag.E6 i (e6Root k) = 1 := by omega
  have h2 : stringDown Tag.E6 i (e6Root k) = 1 := by omega
  have hu := (hs 1).mpr ⟨by omega, by omega⟩
  have hd := (hs (-1)).mpr ⟨by omega, by omega⟩
  rw [one_smul] at hu
  rw [neg_smul, one_smul, ← sub_eq_add_neg] at hd
  exact hpq ⟨isRoot_iff_exists_e6Root.mp hu, isRoot_iff_exists_e6Root.mp hd⟩

variable {R : Type*} [CommRing R]

theorem rootVec_eq_single {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    rootVec Tag.E6 R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 := by
  rw [rootVec, dite_eq_left hβ]

theorem rootVec_eq_zero_of_not {β : Fin Tag.E6.rank → ℤ} (hβ : ¬IsRoot Tag.E6 β) :
    rootVec Tag.E6 R β = 0 := by
  rw [rootVec, dite_eq_right hβ]

theorem xOp_rootVec_E6
    (i : Fin Tag.E6.rank) (c : R) {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp Tag.E6 R i c (rootVec Tag.E6 R α) =
      rootVec Tag.E6 R α + c • rootVec Tag.E6 R (α + Pi.single i 1) := by
  obtain ⟨hp, -, hpq⟩ := stringUp_add_stringDown_E6 hα h₁ h₂
  rw [rootVec_eq_single hα, xOp, Finsupp.linearCombination_single, one_smul]
  simp only [ite_eq_right h₁, ite_eq_right h₂]
  rw [← rootVec_eq_single hα]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with h0 | h1
  · rw [h0, Finset.sum_range_one]
    have hnot : ¬IsRoot Tag.E6 (α + Pi.single i 1) := by
      intro h
      obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
      have := (hs 1).mp (by rwa [one_smul])
      omega
    simp [rootVec_eq_zero_of_not hnot]
  · have hq : stringDown Tag.E6 i α = 0 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_one, hq]
    simp

theorem yOp_rootVec_E6
    (i : Fin Tag.E6.rank) (c : R) {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    yOp Tag.E6 R i c (rootVec Tag.E6 R α) =
      rootVec Tag.E6 R α + c • rootVec Tag.E6 R (α - Pi.single i 1) := by
  obtain ⟨-, hq, hpq⟩ := stringUp_add_stringDown_E6 hα h₁ h₂
  rw [rootVec_eq_single hα, yOp, Finsupp.linearCombination_single, one_smul]
  simp only [ite_eq_right h₁, ite_eq_right h₂]
  rw [← rootVec_eq_single hα]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with h0 | h1
  · rw [h0, Finset.sum_range_one]
    have hnot : ¬IsRoot Tag.E6 (α - Pi.single i 1) := by
      intro h
      obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
      have := (hs (-1)).mp (by rwa [neg_smul, one_smul, ← sub_eq_add_neg])
      omega
    simp [rootVec_eq_zero_of_not hnot]
  · have hp : stringUp Tag.E6 i α = 0 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_one, hp]
    simp

theorem mem_of_mem_subsystemGroup
    {K : Type} [Field K] {X : Set (Fin Tag.E6.rank)}
    {M : Submodule K (RootModule Tag.E6 K)}
    (hx : ∀ i ∈ X, ∀ c : K, ∀ v ∈ M, xOp Tag.E6 K i c v ∈ M)
    (hy : ∀ i ∈ X, ∀ c : K, ∀ v ∈ M, yOp Tag.E6 K i c v ∈ M)
    {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K X) :
    ∀ v ∈ M, (g : Module.End K (RootModule Tag.E6 K)) v ∈ M := by
  induction hg using Subgroup.closure_induction'' with
  | mem g hg =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hg
    · exact hx i hi c
    · exact hy i hi c
  | inv_mem g hg =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hg
    · intro v hv
      rw [coe_xUnit_inv]
      exact hx i hi (-c) v hv
    · intro v hv
      rw [coe_yUnit_inv]
      exact hy i hi (-c) v hv
  | one => exact fun v hv => hv
  | mul g h _ _ hg hh => exact fun v hv => hg _ (hh v hv)

end CFSG.LieType.Chevalley.C2E6Std
