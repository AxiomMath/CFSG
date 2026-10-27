module

public import CFSG.ClassicalInvolution.Q3.Q3ExcClass

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups

section Class

variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem exc3_class_roots_of_simple_singleton {i : KernelComponent χ} {β : Fin τ.rank → ℤ}
    (hsimple : ∀ b ∈ simpleRoots (componentRoots χ i), b = β) :
    ∀ γ ∈ componentRoots χ i, γ = β ∨ γ = -β := by
  intro γ hγΨ
  obtain ⟨w, hw, b, hb, hγw⟩ := exists_smul_simpleRoot (isRootComponent_componentRoots i) hγΨ
  obtain rfl := hsimple b hb
  have hr : IsRoot τ b := simpleRoots_isRoot hb
  have hW : ∀ w ∈ componentWeylGroup (componentRoots χ i), w • b = b ∨ w • b = -b := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨β', hβ', rfl⟩ := hx
      obtain rfl := hsimple β' hβ'
      exact Or.inr (rootReflection_smul_self hr)
    | one => exact Or.inl (one_smul _ _)
    | mul x y _ _ hx hy =>
      rw [mul_smul]
      rcases hy with hy | hy
      · rw [hy]
        exact hx
      · rw [hy, smul_neg]
        rcases hx with hx | hx
        · exact Or.inr (by rw [hx])
        · exact Or.inl (by rw [hx, neg_neg])
    | inv x _ hx =>
      rcases hx with hx | hx
      · left
        calc x⁻¹ • b = x⁻¹ • (x • b) := by rw [hx]
          _ = b := inv_smul_smul x b
      · right
        have : x⁻¹ • (x • b) = x⁻¹ • -b := by rw [hx]
        rw [inv_smul_smul, smul_neg] at this
        exact neg_eq_iff_eq_neg.1 this.symm
  rcases hW w hw with h1 | h1
  · left
    rw [hγw, h1]
  · right
    rw [hγw, h1]

theorem exc3_exists_simpleRoot (i : KernelComponent χ) :
    ∃ b, b ∈ simpleRoots (componentRoots χ i) := by
  induction i using Quotient.inductionOn with
  | h a =>
  obtain ⟨α, hα⟩ := a
  have hαΨ : α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hα, rfl⟩
  obtain ⟨-, -, β, hβ, -⟩ := exists_smul_simpleRoot (isRootComponent_componentRoots _) hαΨ
  exact ⟨β, hβ⟩

theorem exc3_class_eq_of_mem {i i' : KernelComponent χ} {β : Fin τ.rank → ℤ}
    (h : β ∈ componentRoots χ i) (h' : β ∈ componentRoots χ i') : i = i' := by
  obtain ⟨hβ, e⟩ := h
  obtain ⟨hβ', e'⟩ := h'
  rw [← e, ← e']

end Class

section Datum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {D : OrthogonalSemilinearFixedRootDatum τ p₀ k}

theorem exc3_small_orbits {c : ModGL τ k} (hc : Exc3Frob D c) (hq3 : p₀ ^ D.e = 3)
    (hS : Exc3Small D.orbitGroup) : ∃ β, D.orbits = {{β}} := by
  rcases exc3_orbitGroup_big_or_small hc hq3 with hB | ⟨-, hβ⟩
  · exfalso
    obtain ⟨e⟩ := hS
    exact false_of_isQuasisimple_of_isSolvable (ModelFacts.open_isQuasisimple hB.1)
      (CFSG.LieType.HighestRoot.isSolvable_of_mulEquiv (Nat.card_zmod 3)
        (e.symm : _ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))
  · exact hβ

theorem exc3_small_simpleRootsJ {c : ModGL τ k} (hc : Exc3Frob D c) (hq3 : p₀ ^ D.e = 3)
    (hS : Exc3Small D.orbitGroup) : ∃ β, ∀ b ∈ D.simpleRootsJ, b = β := by
  obtain ⟨β, hβ⟩ := exc3_small_orbits hc hq3 hS
  refine ⟨β, fun b hb => ?_⟩
  have h1 := D.thetaOrbit_mem_orbits hb
  rw [hβ, Set.mem_singleton_iff] at h1
  have h2 := self_mem_thetaOrbit D.θ b
  rw [h1] at h2
  exact h2

theorem exc3_not_small_of_two_classes {c : ModGL τ k} (hc : Exc3Frob D c) (hq3 : p₀ ^ D.e = 3)
    {i i' : KernelComponent D.χ} (hi : i ∈ D.J) (hi' : i' ∈ D.J) (hne : i ≠ i') :
    ¬ Exc3Small D.orbitGroup := by
  intro hS
  obtain ⟨β, hβ⟩ := exc3_small_simpleRootsJ hc hq3 hS
  obtain ⟨b, hb⟩ := exc3_exists_simpleRoot i
  obtain ⟨b', hb'⟩ := exc3_exists_simpleRoot i'
  have h1 := hβ b (D.mem_simpleRootsJ_iff.2 ⟨i, hi, hb⟩)
  have h2 := hβ b' (D.mem_simpleRootsJ_iff.2 ⟨i', hi', hb'⟩)
  have h3 : b ∈ componentRoots D.χ i := simpleRoots_subset hb
  have h4 : b' ∈ componentRoots D.χ i' := simpleRoots_subset hb'
  rw [h2.trans h1.symm] at h4
  exact hne (exc3_class_eq_of_mem h3 h4)

theorem exc3_not_small_of_pair (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : ModGL τ k} (hc : Exc3Frob D c) (hq3 : p₀ ^ D.e = 3) {i : KernelComponent D.χ}
    (hi : i ∈ D.J) {γ γ' : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots D.χ i)
    (hγ' : γ' ∈ componentRoots D.χ i) (h : iform γ γ' = 1) : ¬ Exc3Small D.orbitGroup := by
  intro hS
  obtain ⟨β, hβ⟩ := exc3_small_simpleRootsJ hc hq3 hS
  have hsimple : ∀ b ∈ simpleRoots (componentRoots D.χ i), b = β := fun b hb =>
    hβ b (D.mem_simpleRootsJ_iff.2 ⟨i, hi, hb⟩)
  have hβr : IsRoot τ β := by
    obtain ⟨b, hb⟩ := exc3_exists_simpleRoot i
    rw [← hsimple b hb]
    exact simpleRoots_isRoot hb
  have hβ2 : iform β β = 2 := by
    rw [← CFSG.LieType.Chevalley.dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ hβr
  have hneg : iform β (-β) = -2 := by
    rw [← neg_one_smul ℤ β, iform_smul_right, hβ2]
    ring
  have hneg' : iform (-β) β = -2 := by
    rw [iform_comm, hneg]
  have hneg'' : iform (-β) (-β) = 2 := by
    rw [← neg_one_smul ℤ β, iform_smul_left, iform_smul_right, hβ2]
    ring
  rcases exc3_class_roots_of_simple_singleton hsimple γ hγ with h1 | h1 <;>
    rcases exc3_class_roots_of_simple_singleton hsimple γ' hγ' with h2 | h2 <;>
    rw [h1, h2] at h <;> omega

end Datum

end CFSG.ClassicalInvolution.Q3
