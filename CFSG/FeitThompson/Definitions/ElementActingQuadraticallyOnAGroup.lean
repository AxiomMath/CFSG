module

public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped commutatorElement
open SemidirectProduct

variable {A P : Type*} [Group A] [Group P]

def displacementSubgroup (ρ : A →* MulAut P) (a : A) : Subgroup P :=
  Subgroup.closure (Set.range fun v : P => v⁻¹ * ρ a v)

def ActsQuadratically (ρ : A →* MulAut P) (a : A) : Prop :=
  ∀ w ∈ displacementSubgroup ρ a, ρ a w = w

theorem mem_displacementSubgroup (ρ : A →* MulAut P) (a : A) (v : P) :
    v⁻¹ * ρ a v ∈ displacementSubgroup ρ a :=
  Subgroup.subset_closure ⟨v, rfl⟩

theorem mem_displacementSubgroup' (ρ : A →* MulAut P) (a : A) (v : P) :
    v * (ρ a v)⁻¹ ∈ displacementSubgroup ρ a := by
  simpa using mem_displacementSubgroup ρ a v⁻¹

variable {ρ : A →* MulAut P} {a : A}

theorem displacementSubgroup_le_iff {H : Subgroup P} :
    displacementSubgroup ρ a ≤ H ↔ ∀ v : P, v⁻¹ * ρ a v ∈ H := by
  rw [displacementSubgroup, Subgroup.closure_le, Set.range_subset_iff]
  simp [SetLike.mem_coe]

instance displacementSubgroup_normal (ρ : A →* MulAut P) (a : A) :
    (displacementSubgroup ρ a).Normal := by
  constructor
  intro n hn g
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      have key : g * (u⁻¹ * ρ a u) * g⁻¹ =
          ((u * g⁻¹)⁻¹ * ρ a (u * g⁻¹)) * ((g⁻¹)⁻¹ * ρ a g⁻¹)⁻¹ := by
        simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
        group
      rw [key]
      exact mul_mem (mem_displacementSubgroup ρ a _) (inv_mem (mem_displacementSubgroup ρ a _))
  | one => simp
  | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact mul_mem hx hy
  | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem hx

theorem map_displacementSubgroup (ρ : A →* MulAut P) (a : A) :
    (displacementSubgroup ρ a).map (ρ a).toMonoidHom = displacementSubgroup ρ a := by
  rw [displacementSubgroup, MonoidHom.map_closure]
  congr 1
  rw [← Set.range_comp]
  refine subset_antisymm ?_ ?_
  · rintro x ⟨v, rfl⟩
    exact ⟨ρ a v, by simp⟩
  · rintro x ⟨v, rfl⟩
    exact ⟨(ρ a).symm v, by simp⟩

theorem apply_mem_displacementSubgroup {w : P} (hw : w ∈ displacementSubgroup ρ a) :
    ρ a w ∈ displacementSubgroup ρ a := by
  rw [← map_displacementSubgroup ρ a]; exact ⟨w, hw, rfl⟩

theorem displacementSubgroup_eq_bot_iff : displacementSubgroup ρ a = ⊥ ↔ ρ a = 1 := by
  rw [eq_bot_iff, displacementSubgroup_le_iff]
  constructor
  · intro h
    ext v
    have hv := Subgroup.mem_bot.1 (h v)
    rw [inv_mul_eq_one] at hv
    simpa using hv.symm
  · intro h v
    simp [h]

@[simp]
theorem displacementSubgroup_one (ρ : A →* MulAut P) : displacementSubgroup ρ (1 : A) = ⊥ := by
  rw [displacementSubgroup_eq_bot_iff, map_one]

theorem actsQuadratically_iff_forall :
    ActsQuadratically ρ a ↔ ∀ v : P, ρ a (v⁻¹ * ρ a v) = v⁻¹ * ρ a v := by
  rw [ActsQuadratically,
    show (∀ w ∈ displacementSubgroup ρ a, ρ a w = w) ↔
      displacementSubgroup ρ a ≤ (ρ a).toMonoidHom.eqLocus (.id P) from Iff.rfl,
    displacementSubgroup_le_iff]
  rfl

theorem actsQuadratically_one (ρ : A →* MulAut P) : ActsQuadratically ρ (1 : A) := by
  intro w hw
  simp

theorem actsQuadratically_of_apply_eq_one (h : ρ a = 1) : ActsQuadratically ρ a := by
  intro w hw
  simp [h]

theorem zpow_displacement_mem (k : ℤ) (v : P) :
    v * (ρ (a ^ k) v)⁻¹ ∈ displacementSubgroup ρ a := by
  induction k using Int.induction_on generalizing v with
  | zero => simp
  | succ n ih =>
      have h : v * (ρ (a ^ ((n : ℤ) + 1)) v)⁻¹
          = (v * (ρ a v)⁻¹) * (ρ a v * (ρ (a ^ (n : ℤ)) (ρ a v))⁻¹) := by
        rw [zpow_add, zpow_one, map_mul]; simp [mul_assoc]
      rw [h]
      exact mul_mem (mem_displacementSubgroup' ρ a v) (ih _)
  | pred n ih =>
      have hv : ρ a ((ρ a).symm v) = v := by simp
      have h : v * (ρ (a ^ (-(n : ℤ) - 1)) v)⁻¹
          = ((ρ a).symm v * (ρ a ((ρ a).symm v))⁻¹)⁻¹ *
            ((ρ a).symm v * (ρ (a ^ (-(n : ℤ))) ((ρ a).symm v))⁻¹) := by
        have hk : a ^ (-(n : ℤ) - 1) = a ^ (-(n : ℤ)) * a⁻¹ := by
          rw [sub_eq_add_neg, zpow_add, zpow_neg_one]
        rw [hk, map_mul, ← hv]; simp [mul_assoc]
      rw [h]
      exact mul_mem (inv_mem (mem_displacementSubgroup' ρ a _)) (ih _)

theorem commutatorElement_inl_inr (v : P) (b : A) :
    ⁅(inl v : P ⋊[ρ] A), (inr b : P ⋊[ρ] A)⁆ = inl (v * (ρ b v)⁻¹) := by
  apply SemidirectProduct.ext <;> simp [commutatorElement_def]

theorem commutator_range_inl_zpowers_inr :
    ⁅((inl : P →* P ⋊[ρ] A).range), (Subgroup.zpowers (inr a : P ⋊[ρ] A))⁆
      = (displacementSubgroup ρ a).map inl := by
  refine le_antisymm (Subgroup.commutator_le.2 ?_) ?_
  · rintro g₁ ⟨v, rfl⟩ g₂ hg₂
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₂
    rw [← map_zpow, commutatorElement_inl_inr]
    exact ⟨_, zpow_displacement_mem k v, rfl⟩
  · rw [Subgroup.map_le_iff_le_comap, displacementSubgroup_le_iff]
    intro v
    have hmem := Subgroup.commutator_mem_commutator
      (H₁ := (inl : P →* P ⋊[ρ] A).range) (H₂ := Subgroup.zpowers (inr a : P ⋊[ρ] A))
      (g₁ := (inl v⁻¹ : P ⋊[ρ] A)) (g₂ := (inr a : P ⋊[ρ] A))
      ⟨v⁻¹, rfl⟩ (Subgroup.mem_zpowers _)
    rwa [commutatorElement_inl_inr, show v⁻¹ * (ρ a v⁻¹)⁻¹ = v⁻¹ * ρ a v by simp] at hmem

private theorem zpow_apply_eq_self {w : P} (h : ρ a w = w) (k : ℤ) : ρ (a ^ k) w = w := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add, zpow_one, map_mul, MulAut.mul_apply, h, ih]
  | pred n ih =>
      have hinv : ρ a⁻¹ w = w := by
        rw [map_inv]; exact (MulEquiv.symm_apply_eq _).2 h.symm
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one, map_mul, MulAut.mul_apply, hinv, ih]

theorem commutator_map_inl_zpowers_inr_eq_bot_iff (H : Subgroup P) :
    ⁅(H.map (inl : P →* P ⋊[ρ] A)), (Subgroup.zpowers (inr a : P ⋊[ρ] A))⁆ = ⊥
      ↔ ∀ w ∈ H, ρ a w = w := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  constructor
  · intro h w hw
    have h1 := h _ ⟨w, hw, rfl⟩ _ (Subgroup.mem_zpowers (inr a : P ⋊[ρ] A))
    rw [commutatorElement_inl_inr] at h1
    have h2 : w * (ρ a w)⁻¹ = 1 := inl_injective (by simpa using Subgroup.mem_bot.1 h1)
    exact (mul_inv_eq_one.1 h2).symm
  · rintro h g₁ ⟨w, hw, rfl⟩ g₂ hg₂
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₂
    rw [← map_zpow, commutatorElement_inl_inr, zpow_apply_eq_self (h w hw) k]
    simp

theorem actsQuadratically_iff_commutator_eq_bot :
    ActsQuadratically ρ a ↔
      ⁅(⁅((inl : P →* P ⋊[ρ] A).range), (Subgroup.zpowers (inr a : P ⋊[ρ] A))⁆),
        (Subgroup.zpowers (inr a : P ⋊[ρ] A))⁆ = ⊥ := by
  rw [commutator_range_inl_zpowers_inr, commutator_map_inl_zpowers_inr_eq_bot_iff]
  rfl

end CFSG.FeitThompson
