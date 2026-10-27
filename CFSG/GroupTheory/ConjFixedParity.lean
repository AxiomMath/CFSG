module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] [Finite G]

theorem ncard_modEq_ncard_fixed {T : Subgroup G} (hT : IsPGroup 2 T) {𝒜 : Set (Subgroup G)}
    (h𝒜 : ∀ x ∈ T, ∀ C ∈ 𝒜, C.map (MulAut.conj x).toMonoidHom ∈ 𝒜) :
    𝒜.ncard ≡ {C ∈ 𝒜 | ∀ x ∈ T, C.map (MulAut.conj x).toMonoidHom = C}.ncard [MOD 2] := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) (fun H K h =>
      Subgroup.ext (Set.ext_iff.mp h))
  haveI : Finite ↥𝒜 := Finite.of_injective (fun C : ↥𝒜 => (C.1 : Set G)) (fun C D h =>
    Subtype.ext (Subgroup.ext (Set.ext_iff.mp h)))
  let _ : MulAction ↥T ↥𝒜 :=
    { smul := fun x C => ⟨C.1.map (MulAut.conj (x : G)).toMonoidHom, h𝒜 x x.2 C.1 C.2⟩
      one_smul := fun C => Subtype.ext (by
        change C.1.map (MulAut.conj (1 : G)).toMonoidHom = C.1
        rw [show MulAut.conj (1 : G) = 1 from map_one _]
        exact Subgroup.map_id C.1)
      mul_smul := fun x y C => Subtype.ext (by
        change C.1.map (MulAut.conj ((x : G) * (y : G))).toMonoidHom =
          (C.1.map (MulAut.conj (y : G)).toMonoidHom).map
            (MulAut.conj (x : G)).toMonoidHom
        have hcomp : (MulAut.conj ((x : G) * (y : G))).toMonoidHom =
            (MulAut.conj (x : G)).toMonoidHom.comp (MulAut.conj (y : G)).toMonoidHom := by
          ext z
          simp [MulAut.conj_apply, mul_assoc]
        rw [hcomp]
        exact (Subgroup.map_map (K := C.1) (MulAut.conj (x : G)).toMonoidHom
          (MulAut.conj (y : G)).toMonoidHom).symm) }
  have key := hT.card_modEq_card_fixedPoints (α := ↥𝒜)
  rw [Nat.card_coe_set_eq] at key
  have himg : Subtype.val '' (MulAction.fixedPoints ↥T ↥𝒜) =
      {C ∈ 𝒜 | ∀ x ∈ T, C.map (MulAut.conj x).toMonoidHom = C} := by
    ext C
    constructor
    · rintro ⟨⟨D, hD⟩, hfix, rfl⟩
      exact ⟨hD, fun x hx => congrArg Subtype.val (hfix ⟨x, hx⟩)⟩
    · rintro ⟨hC, hfix⟩
      exact ⟨⟨C, hC⟩, fun x => Subtype.ext (hfix x x.2), rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
  exact key

end CFSG.GroupTheory
