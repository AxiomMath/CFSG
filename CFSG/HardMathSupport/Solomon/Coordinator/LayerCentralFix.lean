module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentral
import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component
public import CFSG.HardMathSupport.Solomon.Proving.LBLayerConj

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Fix

variable {K Q : Type*} [Group K] [Group Q]

@[expose] def fixSubgroup (α : MulAut K) : Subgroup K :=
  MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id K)

theorem mem_fixSubgroup {α : MulAut K} {x : K} : x ∈ fixSubgroup α ↔ α x = x := Iff.rfl

theorem commutatorElement_mul_mul' {G : Type*} [Group G] {a b z₁ z₂ : G} (h1b : Commute z₁ b)
    (h12 : Commute z₁ z₂) (h2a : Commute z₂ a) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  have e1 : z₁ * (b * z₂) = b * z₂ * z₁ := (h1b.mul_right h12).eq
  have e2 : z₂ * a⁻¹ = a⁻¹ * z₂ := h2a.inv_right.eq
  calc a * z₁ * (b * z₂) * (z₁⁻¹ * a⁻¹) * (z₂⁻¹ * b⁻¹)
      = a * (z₁ * (b * z₂)) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * (z₂ * a⁻¹) * z₂⁻¹ * b⁻¹ := by rw [e1]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [e2]; group

variable (π : K →* Q) (hker : π.ker ≤ Subgroup.center K) (α : MulAut K) (β : MulAut Q)
  (hαβ : ∀ k, π (α k) = β (π k))
include hker hαβ

theorem alpha_eq_mul_central {k : K} (hk : π k ∈ fixSubgroup β) :
    ∃ z ∈ Subgroup.center K, α k = k * z := by
  refine ⟨k⁻¹ * α k, hker ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ, show β (π k) = π k from hk, inv_mul_cancel]

theorem map_fixSubgroup_le : (fixSubgroup α).map π ≤ fixSubgroup β := by
  rintro _ ⟨f, hf, rfl⟩
  show β (π f) = π f
  rw [← hαβ, show α f = f from hf]

theorem conj_mem_fixSubgroup {k f : K} (hk : π k ∈ fixSubgroup β) (hf : f ∈ fixSubgroup α) :
    k * f * k⁻¹ ∈ fixSubgroup α := by
  obtain ⟨z, hz, hαk⟩ := alpha_eq_mul_central π hker α β hαβ hk
  show α (k * f * k⁻¹) = k * f * k⁻¹
  have hf' : α f = f := hf
  rw [map_mul, map_mul, map_inv, hαk, hf']
  have hzc : ∀ g : K, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
  calc k * z * f * (k * z)⁻¹ = k * (z * f) * z⁻¹ * k⁻¹ := by group
    _ = k * (f * z) * z⁻¹ * k⁻¹ := by rw [← hzc f]
    _ = k * f * k⁻¹ := by group

theorem comm_mem_fixSubgroup {k₁ k₂ : K} (h₁ : π k₁ ∈ fixSubgroup β) (h₂ : π k₂ ∈ fixSubgroup β) :
    ⁅k₁, k₂⁆ ∈ fixSubgroup α := by
  obtain ⟨z₁, hz₁, hα₁⟩ := alpha_eq_mul_central π hker α β hαβ h₁
  obtain ⟨z₂, hz₂, hα₂⟩ := alpha_eq_mul_central π hker α β hαβ h₂
  show α ⁅k₁, k₂⁆ = ⁅k₁, k₂⁆
  rw [map_commutatorElement, hα₁, hα₂]
  exact commutatorElement_mul_mul' (Commute.symm (Subgroup.mem_center_iff.1 hz₁ k₂))
    (Commute.symm (Subgroup.mem_center_iff.1 hz₁ z₂))
    (Commute.symm (Subgroup.mem_center_iff.1 hz₂ k₁))

theorem normal_map_fixSubgroup (hπ : Function.Surjective π) :
    (((fixSubgroup α).map π).subgroupOf (fixSubgroup β)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨k, hk⟩ := hπ (g : Q)
  have hkg : π k ∈ fixSubgroup β := by rw [hk]; exact g.2
  refine ⟨k * f * k⁻¹, conj_mem_fixSubgroup π hker α β hαβ hkg hf, ?_⟩
  simp only [map_mul, map_inv, hk, hfx]
  rfl

theorem le_map_fixSubgroup_of_perfect (hπ : Function.Surjective π) {A : Subgroup Q}
    (hA : A ≤ fixSubgroup β) (hperf : ⁅A, A⁆ = A) : A ≤ (fixSubgroup α).map π := by
  conv_lhs => rw [← hperf]
  rw [Subgroup.commutator_le]
  intro a₁ ha₁ a₂ ha₂
  obtain ⟨k₁, rfl⟩ := hπ a₁
  obtain ⟨k₂, rfl⟩ := hπ a₂
  exact ⟨⁅k₁, k₂⁆, comm_mem_fixSubgroup π hker α β hαβ (hA ha₁) (hA ha₂), map_commutatorElement _ _ _⟩

end Fix

section Layers

variable {K Q : Type} [Group K] [Group Q] [Finite K] [Finite Q]
variable (π : K →* Q) (hker : π.ker ≤ Subgroup.center K) (α : MulAut K) (β : MulAut Q)
  (hαβ : ∀ k, π (α k) = β (π k))
include hker hαβ

theorem kerCentral_fixSubgroup :
    ∀ y ∈ fixSubgroup α ⊓ π.ker, ∀ x ∈ fixSubgroup α, x * y = y * x := fun _ hy x _ =>
  (Subgroup.mem_center_iff.1 (hker hy.2) x)

theorem glaPComponent_map_fixSubgroup (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime)
    {J : Subgroup K} (hJ : GLAPComponent p (fixSubgroup α) J) :
    GLAPComponent p (fixSubgroup β) (J.map π) :=
  CFSG.HardMathSupport.Solomon.Proving.glaPComponent_of_normal_overgroup hp
    (map_fixSubgroup_le π hker α β hαβ) (normal_map_fixSubgroup π hker α β hαβ hπ)
    (glaPComponent_map_central hp π (kerCentral_fixSubgroup π hker α β hαβ) hJ)

theorem exists_glaPComponent_map_fixSubgroup (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime)
    {A : Subgroup Q} (hA : GLAPComponent p (fixSubgroup β) A) :
    ∃ J : Subgroup K, GLAPComponent p (fixSubgroup α) J ∧ J.map π = A := by
  have hAH : A ≤ (fixSubgroup α).map π :=
    le_map_fixSubgroup_of_perfect π hker α β hαβ hπ hA.1 (glaPComponent_perfect hA)
  exact exists_glaPComponent_map_central hp π (kerCentral_fixSubgroup π hker α β hαβ)
    (glaPComponent_of_le hp hA hAH (map_fixSubgroup_le π hker α β hαβ))

theorem map_glaPLayer_fixSubgroup_eq (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime) :
    (GLAPLayer p (fixSubgroup α)).map π = GLAPLayer p (fixSubgroup β) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun J hJ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hJ' := glaPComponent_map_fixSubgroup π hker α β hαβ hπ hp hJ
    exact le_sSup hJ'
  · refine sSup_le fun A hA => ?_
    obtain ⟨J, hJ, rfl⟩ := exists_glaPComponent_map_fixSubgroup π hker α β hαβ hπ hp hA
    exact Subgroup.map_mono (le_sSup hJ)

theorem le_map_glaPLayer_fixSubgroup_of_le (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime)
    {A : Subgroup Q} (hA : A ≤ GLAPLayer p (fixSubgroup β)) :
    A ≤ (GLAPLayer p (fixSubgroup α)).map π :=
  (map_glaPLayer_fixSubgroup_eq π hker α β hαβ hπ hp).symm ▸ hA

omit hker hαβ in
theorem le_glaPLayer_of_normal_simple {p : ℕ} (hp : p.Prime) {Y A : Subgroup Q} (hAY : A ≤ Y)
    (hn : (A.subgroupOf Y).Normal) [IsSimpleGroup A] (hnc : ∃ a b : A, a * b ≠ b * a)
    (hpA : p ∣ Nat.card A) : A ≤ GLAPLayer p Y :=
  le_sSup (GL83.PiGen.glaPComponent_of_normal_simple hp hAY hn hnc hpA)

end Layers

section Join

variable {K Q : Type} [Group K] [Group Q] [Finite K] [Finite Q]
variable (π : K →* Q) (hker : π.ker ≤ Subgroup.center K) (hπ : Function.Surjective π)
include hker hπ

theorem glaPLayer_fixSubgroup_sup_eq_top_of_perfect (hK : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (α₁ α₂ : MulAut K) (β₁ β₂ : MulAut Q) (h₁ : ∀ k, π (α₁ k) = β₁ (π k))
    (h₂ : ∀ k, π (α₂ k) = β₂ (π k)) {p : ℕ} (hp : p.Prime) {A₁ A₂ : Subgroup Q}
    (hA₁ : A₁ ≤ GLAPLayer p (fixSubgroup β₁)) (hA₂ : A₂ ≤ GLAPLayer p (fixSubgroup β₂))
    (hQ : A₁ ⊔ A₂ = ⊤) :
    GLAPLayer p (fixSubgroup α₁) ⊔ GLAPLayer p (fixSubgroup α₂) = ⊤ := by
  set M := GLAPLayer p (fixSubgroup α₁) ⊔ GLAPLayer p (fixSubgroup α₂) with hM
  have hmap : A₁ ⊔ A₂ ≤ M.map π := by
    rw [hM, Subgroup.map_sup]
    exact sup_le_sup (le_map_glaPLayer_fixSubgroup_of_le π hker α₁ β₁ h₁ hπ hp hA₁)
      (le_map_glaPLayer_fixSubgroup_of_le π hker α₂ β₂ h₂ hπ hp hA₂)
  rw [hQ, top_le_iff] at hmap
  have hMZ : M ⊔ π.ker = ⊤ := by
    have h2 := Subgroup.comap_map_eq π M
    rw [hmap, Subgroup.comap_top] at h2
    exact h2.symm
  rw [eq_top_iff, ← hK, Subgroup.commutator_le]
  intro k₁ _ k₂ _
  have hk₁ : k₁ ∈ M ⊔ π.ker := by rw [hMZ]; trivial
  have hk₂ : k₂ ∈ M ⊔ π.ker := by rw [hMZ]; trivial
  obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hk₁
  obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hk₂
  rw [commutatorElement_mul_mul' (Commute.symm (Subgroup.mem_center_iff.1 (hker hz₁) m₂))
    (Commute.symm (Subgroup.mem_center_iff.1 (hker hz₁) z₂))
    (Commute.symm (Subgroup.mem_center_iff.1 (hker hz₂) m₁))]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)

end Join

end CFSG.HardMathSupport.Solomon.Coordinator
