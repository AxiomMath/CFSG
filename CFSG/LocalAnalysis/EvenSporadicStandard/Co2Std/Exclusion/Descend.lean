module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Facts

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

variable {G : Type*} [Group G] {L A : Subgroup G}

theorem conjN_apply (x : ↥(L ⊓ normalizer (A : Set G))) (a : A) :
    ((conjN L A x a : A) : G) = x * a * x⁻¹ := rfl

theorem conjN_mem_autImage (x : ↥(L ⊓ normalizer (A : Set G))) : conjN L A x ∈ autImage L A :=
  ⟨x, rfl⟩

@[expose] def toAutImage (x : ↥(L ⊓ normalizer (A : Set G))) : ↥(autImage L A) :=
  ⟨conjN L A x, conjN_mem_autImage x⟩

@[simp]
theorem coe_toAutImage (x : ↥(L ⊓ normalizer (A : Set G))) :
    (toAutImage x : MulAut A) = conjN L A x := rfl

theorem toAutImage_eq_rangeRestrict (x : ↥(L ⊓ normalizer (A : Set G))) :
    toAutImage x = (conjN L A).rangeRestrict x := rfl

@[simp]
theorem toAutImage_mul (x y : ↥(L ⊓ normalizer (A : Set G))) :
    toAutImage (x * y) = toAutImage x * toAutImage y :=
  Subtype.ext ((conjN L A).map_mul x y)

@[simp]
theorem toAutImage_one : toAutImage (1 : ↥(L ⊓ normalizer (A : Set G))) = 1 :=
  Subtype.ext ((conjN L A).map_one)

theorem conjN_eq_one_iff (hC : L ⊓ centralizer (A : Set G) = A)
    (x : ↥(L ⊓ normalizer (A : Set G))) : conjN L A x = 1 ↔ (x : G) ∈ A := by
  have hA : A ≤ centralizer (A : Set G) := by
    calc
      A = L ⊓ centralizer (A : Set G) := hC.symm
      _ ≤ centralizer (A : Set G) := inf_le_right
  constructor
  · intro hx
    have hxker : Subgroup.inclusion inf_le_right x ∈ A.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker]
      simpa [conjN] using hx
    rw [Subgroup.normalizerMonoidHom_ker] at hxker
    have hxmem : (x : G) ∈ L ⊓ centralizer (A : Set G) :=
      ⟨x.2.1, by simpa [Subgroup.mem_subgroupOf] using hxker⟩
    rwa [hC] at hxmem
  · intro hx
    have hxker : Subgroup.inclusion inf_le_right x ∈ A.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      rw [Subgroup.mem_subgroupOf]
      exact hA hx
    rw [MonoidHom.mem_ker] at hxker
    simpa [conjN] using hxker

@[expose] noncomputable def descend {α : Sort*} (f : ↥(L ⊓ normalizer (A : Set G)) → α) :
    ↥(autImage L A) → α :=
  fun g => f (Classical.choose g.2)

theorem descend_toAutImage {α : Sort*} (f : ↥(L ⊓ normalizer (A : Set G)) → α)
    (hf : ∀ x y, conjN L A x = conjN L A y → f x = f y) (x : ↥(L ⊓ normalizer (A : Set G))) :
    descend f (toAutImage x) = f x := by
  unfold descend
  exact hf _ _ (Classical.choose_spec (toAutImage x).2)

theorem conjN_rangeRestrict_ker_le {H : Type*} [Group H]
    (ρ : ↥(L ⊓ normalizer (A : Set G)) →* H)
    (hρ : ∀ x, conjN L A x = 1 → ρ x = 1) :
    (conjN L A).rangeRestrict.ker ≤ ρ.ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  exact hρ x (by simpa using congrArg Subtype.val hx)

@[expose] noncomputable def descendHom {H : Type*} [Group H]
    (ρ : ↥(L ⊓ normalizer (A : Set G)) →* H) (hρ : ∀ x, conjN L A x = 1 → ρ x = 1) :
    ↥(autImage L A) →* H :=
  MonoidHom.liftOfRightInverse (f := (conjN L A).rangeRestrict)
    (f_inv := Function.surjInv (conjN L A).rangeRestrict_surjective)
    (hf := Function.rightInverse_surjInv (conjN L A).rangeRestrict_surjective)
    ⟨ρ, conjN_rangeRestrict_ker_le ρ hρ⟩

theorem descendHom_toAutImage {H : Type*} [Group H] (ρ : ↥(L ⊓ normalizer (A : Set G)) →* H)
    (hρ : ∀ x, conjN L A x = 1 → ρ x = 1) (x : ↥(L ⊓ normalizer (A : Set G))) :
    descendHom ρ hρ (toAutImage x) = ρ x := by
  rw [toAutImage_eq_rangeRestrict]
  exact MonoidHom.liftOfRightInverse_comp_apply
    (f := (conjN L A).rangeRestrict)
    (f_inv := Function.surjInv (conjN L A).rangeRestrict_surjective)
    (hf := Function.rightInverse_surjInv (conjN L A).rangeRestrict_surjective)
    (g := ⟨ρ, conjN_rangeRestrict_ker_le ρ hρ⟩) (x := x)

theorem exists_toAutImage_eq (g : ↥(autImage L A)) :
    ∃ x : ↥(L ⊓ normalizer (A : Set G)), toAutImage x = g := by
  exact ⟨Classical.choose g.2, Subtype.ext (Classical.choose_spec g.2)⟩

theorem toAutImage_surjective : Function.Surjective (toAutImage (L := L) (A := A)) :=
  exists_toAutImage_eq

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
