module

public import CFSG.GroupTheory.GLnTwoSplitting.Extension
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

section ConjHom

variable (ι : E → G) (hadd : ∀ a b, ι (a + b) = ι a * ι b) (hinj : Function.Injective ι)
  (hnorm : ∀ g e, ∃ e', g * ι e * g⁻¹ = ι e')

@[expose] noncomputable def embConjFun (g : G) (e : E) : E := Classical.choose (hnorm g e)

omit [AddCommGroup E] [Module (ZMod 2) E] in
theorem embConjFun_spec (g : G) (e : E) : g * ι e * g⁻¹ = ι (embConjFun ι hnorm g e) :=
  Classical.choose_spec (hnorm g e)

omit [Module (ZMod 2) E] in
include hadd hinj in
theorem embConjFun_add (g : G) (a b : E) :
    embConjFun ι hnorm g (a + b) = embConjFun ι hnorm g a + embConjFun ι hnorm g b := by
  apply hinj
  rw [hadd, ← embConjFun_spec ι hnorm, ← embConjFun_spec ι hnorm, ← embConjFun_spec ι hnorm, hadd]
  group

omit [AddCommGroup E] [Module (ZMod 2) E] in
include hinj in
theorem embConjFun_mul (g h : G) (e : E) :
    embConjFun ι hnorm (g * h) e = embConjFun ι hnorm g (embConjFun ι hnorm h e) := by
  apply hinj
  rw [← embConjFun_spec ι hnorm, ← embConjFun_spec ι hnorm, ← embConjFun_spec ι hnorm]
  group

omit [AddCommGroup E] [Module (ZMod 2) E] in
include hinj in
theorem embConjFun_one (e : E) : embConjFun ι hnorm 1 e = e := by
  apply hinj
  rw [← embConjFun_spec ι hnorm]
  group

@[expose] noncomputable def embConjHom : G →* (E ≃ₗ[ZMod 2] E) where
  toFun g := AddEquiv.toLinearEquiv
    { toFun := embConjFun ι hnorm g
      invFun := embConjFun ι hnorm g⁻¹
      left_inv := fun e => by
        rw [← embConjFun_mul ι hinj hnorm, inv_mul_cancel, embConjFun_one ι hinj hnorm]
      right_inv := fun e => by
        rw [← embConjFun_mul ι hinj hnorm, mul_inv_cancel, embConjFun_one ι hinj hnorm]
      map_add' := embConjFun_add ι hadd hinj hnorm g } (ZMod.map_smul _)
  map_one' := LinearEquiv.ext fun e => embConjFun_one ι hinj hnorm e
  map_mul' g h := LinearEquiv.ext fun e => embConjFun_mul ι hinj hnorm g h e

theorem conj_embConjHom (g : G) (e : E) :
    g * ι e * g⁻¹ = ι (embConjHom ι hadd hinj hnorm g e) :=
  embConjFun_spec ι hnorm g e

end ConjHom

noncomputable def natExtOfConj (ι : E → G) (hadd : ∀ a b, ι (a + b) = ι a * ι b)
    (hinj : Function.Injective ι) (hnorm : ∀ g e, ∃ e', g * ι e * g⁻¹ = ι e')
    (hsurj : Function.Surjective (embConjHom ι hadd hinj hnorm))
    (hC : ∀ g, (∀ e, g * ι e * g⁻¹ = ι e) → ∃ e, ι e = g) : NatExt G E where
  ι := ι
  ι_add := hadd
  injective := hinj
  π := embConjHom ι hadd hinj hnorm
  surjective := hsurj
  ker_iff g := by
    constructor
    · intro h
      apply hC
      intro e
      rw [conj_embConjHom ι hadd hinj hnorm, h]
      rfl
    · rintro ⟨e₀, rfl⟩
      refine LinearEquiv.ext fun e => hinj ?_
      have hc : ι e₀ * ι e = ι e * ι e₀ := by rw [← hadd, add_comm, hadd]
      change ι (embConjHom ι hadd hinj hnorm (ι e₀) e) = ι e
      rw [← conj_embConjHom ι hadd hinj hnorm, hc, mul_inv_cancel_right]
  conj := conj_embConjHom ι hadd hinj hnorm

end CFSG.GroupTheory.GLnTwoSplitting
