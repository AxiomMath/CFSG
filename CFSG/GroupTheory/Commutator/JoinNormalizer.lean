module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Tactic.Group
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_sup_right_le_of_le_normalizer {Y A B N : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hBN : B ≤ Subgroup.normalizer (N : Set G))
    (hA : ⁅Y, A⁆ ≤ N) (hB : ⁅Y, B⁆ ≤ N) : ⁅Y, A ⊔ B⁆ ≤ N := by
  rw [Subgroup.commutator_comm]
  exact CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize A B Y N
    (Subgroup.commutator_comm (H₁ := Y) (H₂ := A) ▸ hA)
    (Subgroup.commutator_comm (H₁ := Y) (H₂ := B) ▸ hB) hAN hBN

theorem commutator_iSup_left_le_of_le_normalizer {ι : Sort*} {A : ι → Subgroup G}
    {Y N : Subgroup G} (hN : ∀ i, A i ≤ Subgroup.normalizer (N : Set G))
    (hA : ∀ i, ⁅A i, Y⁆ ≤ N) : ⁅⨆ i, A i, Y⁆ ≤ N := by
  let C : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (N : Set G) ∧ ∀ y ∈ Y, ⁅x, y⁆ ∈ N}
      one_mem' := ⟨Subgroup.one_mem _, fun y _ => by simp⟩
      mul_mem' := by
        rintro x₁ x₂ ⟨hx₁, hc₁⟩ ⟨hx₂, hc₂⟩
        refine ⟨Subgroup.mul_mem _ hx₁ hx₂, fun y hy => ?_⟩
        have e : ⁅x₁ * x₂, y⁆ = x₁ * ⁅x₂, y⁆ * x₁⁻¹ * ⁅x₁, y⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp hx₁ _).mp (hc₂ y hy)) (hc₁ y hy)
      inv_mem' := by
        rintro x ⟨hx, hc⟩
        refine ⟨Subgroup.inv_mem _ hx, fun y hy => ?_⟩
        have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x := by
          simp only [commutatorElement_def]; group
        rw [e]
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) _).mp
          (N.inv_mem (hc y hy)) }
  have hle : (⨆ i, A i) ≤ C :=
    iSup_le fun i a ha =>
      ⟨hN i ha, fun y hy => Subgroup.commutator_le.mp (hA i) a ha y hy⟩
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact (hle hx).2 y hy

theorem commutator_iSup_right_le_of_le_normalizer {ι : Sort*} {B : ι → Subgroup G}
    {K N : Subgroup G} (hN : ∀ i, B i ≤ Subgroup.normalizer (N : Set G))
    (h : ∀ i, ⁅K, B i⁆ ≤ N) : ⁅K, ⨆ i, B i⁆ ≤ N := by
  rw [Subgroup.commutator_comm]
  exact commutator_iSup_left_le_of_le_normalizer (A := B) (Y := K) hN
    (fun i => (Subgroup.commutator_comm (H₁ := K) (H₂ := B i)).symm ▸ h i)

theorem commutator_zpowers_le_of_forall_mem {A N : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (N : Set G)) (hc : ∀ a ∈ A, ⁅a, c⁆ ∈ N) :
    ⁅A, Subgroup.zpowers c⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro a ha z hz
  let D : Subgroup G :=
    { carrier := {y | y ∈ Subgroup.normalizer (N : Set G) ∧ ⁅a, y⁆ ∈ N}
      one_mem' := ⟨Subgroup.one_mem _, by simp [commutatorElement_one_right]⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, hc₁⟩ ⟨hy₂, hc₂⟩
        refine ⟨Subgroup.mul_mem _ hy₁ hy₂, ?_⟩
        have e : ⁅a, y₁ * y₂⁆ = ⁅a, y₁⁆ * (y₁ * ⁅a, y₂⁆ * y₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem hc₁ ((Subgroup.mem_normalizer_iff.mp hy₁ _).mp hc₂)
      inv_mem' := by
        rintro y ⟨hy, hcy⟩
        refine ⟨Subgroup.inv_mem _ hy, ?_⟩
        have e : ⁅a, y⁻¹⁆ = y⁻¹ * (⁅a, y⁆)⁻¹ * y := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff''.mp hy _).mp (N.inv_mem hcy) }
  exact (Subgroup.zpowers_le.mpr (show c ∈ D from ⟨hcN, hc a ha⟩) hz).2

end CFSG.GroupTheory

end
