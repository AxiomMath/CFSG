module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module

structure ElemAb2 (E : Type*) [Group E] : Prop where
  comm : ∀ a b : E, a * b = b * a
  sq : ∀ a : E, a * a = 1

variable {E : Type*} [Group E]

@[expose] def EVec (E : Type*) [Group E] (_ : ElemAb2 E) : Type _ := Additive E

namespace EVec

variable (h : ElemAb2 E)

instance : AddCommGroup (EVec E h) :=
  letI : CommGroup E := { ‹Group E› with mul_comm := h.comm }
  inferInstanceAs (AddCommGroup (Additive E))

@[expose] def toE (v : EVec E h) : E := Additive.toMul v

@[expose] def ofE (e : E) : EVec E h := Additive.ofMul e

theorem toE_ofE (e : E) : toE h (ofE h e) = e := rfl

theorem ofE_toE (v : EVec E h) : ofE h (toE h v) = v := rfl

theorem toE_add (a b : EVec E h) : toE h (a + b) = toE h a * toE h b := rfl

theorem ofE_mul (a b : E) : ofE h (a * b) = ofE h a + ofE h b := rfl

theorem toE_zero : toE h (0 : EVec E h) = 1 := rfl

theorem ofE_one : ofE h (1 : E) = 0 := rfl

theorem toE_neg (v : EVec E h) : toE h (-v) = (toE h v)⁻¹ := rfl

theorem toE_sub (a b : EVec E h) : toE h (a - b) = toE h a * (toE h b)⁻¹ := by
  rw [sub_eq_add_neg, toE_add, toE_neg]

theorem toE_injective : Function.Injective (toE h) := fun a b hab => by
  rw [← ofE_toE h a, hab, ofE_toE h b]

theorem add_self_eq_zero' (v : EVec E h) : v + v = 0 := by
  apply toE_injective h
  rw [toE_add, toE_zero]
  exact h.sq _

theorem two_nsmul_eq_zero (v : EVec E h) : (2 : ℕ) • v = 0 := by
  rw [two_nsmul]
  exact add_self_eq_zero' h v

noncomputable instance : Module (ZMod 2) (EVec E h) :=
  AddCommGroup.zmodModule (two_nsmul_eq_zero h)

@[expose] def equivE : E ≃ EVec E h where
  toFun := ofE h
  invFun := toE h
  left_inv := toE_ofE h
  right_inv := ofE_toE h

@[expose] def autToAdd (σ : MulAut E) : EVec E h →+ EVec E h :=
  AddMonoidHom.mk' (fun v => ofE h (σ (toE h v))) (fun a b => by
    rw [toE_add, map_mul, ofE_mul])

@[expose] noncomputable def autToGL (σ : MulAut E) : EVec E h ≃ₗ[ZMod 2] EVec E h :=
  { toLinearMap := (autToAdd h σ).toZModLinearMap 2
    invFun := fun v => ofE h (σ.symm (toE h v))
    left_inv := fun v => by
      show ofE h (σ.symm (toE h (ofE h (σ (toE h v))))) = v
      rw [toE_ofE, σ.symm_apply_apply, ofE_toE]
    right_inv := fun v => by
      show ofE h (σ (toE h (ofE h (σ.symm (toE h v))))) = v
      rw [toE_ofE, σ.apply_symm_apply, ofE_toE] }

theorem autToGL_apply (σ : MulAut E) (v : EVec E h) :
    autToGL h σ v = ofE h (σ (toE h v)) := rfl

@[expose] noncomputable def glToAut (g : EVec E h ≃ₗ[ZMod 2] EVec E h) : MulAut E :=
  { toFun := fun e => toE h (g (ofE h e))
    invFun := fun e => toE h (g.symm (ofE h e))
    left_inv := fun e => by
      show toE h (g.symm (ofE h (toE h (g (ofE h e))))) = e
      rw [ofE_toE, g.symm_apply_apply, toE_ofE]
    right_inv := fun e => by
      show toE h (g (ofE h (toE h (g.symm (ofE h e))))) = e
      rw [ofE_toE, g.apply_symm_apply, toE_ofE]
    map_mul' := fun a b => by
      show toE h (g (ofE h (a * b))) = toE h (g (ofE h a)) * toE h (g (ofE h b))
      rw [ofE_mul, map_add, toE_add] }

@[expose] noncomputable def mulAutToGL : MulAut E ≃* (EVec E h ≃ₗ[ZMod 2] EVec E h) where
  toFun := autToGL h
  invFun := glToAut h
  left_inv := fun σ => by
    ext e
    show toE h (autToGL h σ (ofE h e)) = σ e
    rw [autToGL_apply, toE_ofE, toE_ofE]
  right_inv := fun g => by
    ext v
    show ofE h (toE h (g (ofE h (toE h v)))) = g v
    rw [ofE_toE, ofE_toE]
  map_mul' := fun σ τ => by
    ext v
    rfl

theorem mulAutToGL_apply (σ : MulAut E) (v : EVec E h) :
    mulAutToGL h σ v = ofE h (σ (toE h v)) := rfl

theorem toE_nu (σ : MulAut E) (v : EVec E h) :
    toE h (nu (mulAutToGL h σ) v) = σ (toE h v) * (toE h v)⁻¹ := by
  show toE h (mulAutToGL h σ v - v) = _
  rw [toE_sub, mulAutToGL_apply, toE_ofE]

theorem finrank_eq [Finite E] {n : ℕ} (hcard : Nat.card E = 2 ^ n) :
    finrank (ZMod 2) (EVec E h) = n := by
  haveI : Finite (EVec E h) := Finite.of_equiv E (equivE h)
  haveI : Module.Finite (ZMod 2) (EVec E h) := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := EVec E h)
  have h2 : Nat.card (EVec E h) = Nat.card E := Nat.card_congr (equivE h).symm
  rw [h2, hcard, Nat.card_zmod] at h1
  exact (Nat.pow_right_injective (le_refl 2) h1).symm

theorem natCard_twist [Finite E] (σ : MulAut E) :
    Nat.card {x : E // ∃ w : E, x = w * σ w} = 2 ^ rk (mulAutToGL h σ) := by
  haveI : Finite (EVec E h) := Finite.of_equiv E (equivE h)
  haveI : Module.Finite (ZMod 2) (EVec E h) := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := LinearMap.range (nu (mulAutToGL h σ)))
  rw [Nat.card_zmod] at h1
  rw [rk, ← h1]
  have hinv : ∀ w : E, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (h.sq w)
  have hfwd : ∀ x : E, (∃ w : E, x = w * σ w) →
      ofE h x ∈ LinearMap.range (nu (mulAutToGL h σ)) := by
    rintro x ⟨w, rfl⟩
    refine ⟨ofE h w, ?_⟩
    apply toE_injective h
    rw [toE_nu, toE_ofE, toE_ofE, hinv, h.comm]
  have hbwd : ∀ v : EVec E h, v ∈ LinearMap.range (nu (mulAutToGL h σ)) →
      ∃ w : E, toE h v = w * σ w := by
    rintro v ⟨u, rfl⟩
    refine ⟨toE h u, ?_⟩
    rw [toE_nu, hinv, h.comm]
  exact Nat.card_congr
    { toFun := fun x => ⟨ofE h x.1, hfwd x.1 x.2⟩
      invFun := fun v => ⟨toE h v.1, hbwd v.1 v.2⟩
      left_inv := fun x => Subtype.ext (toE_ofE h x.1)
      right_inv := fun v => Subtype.ext (ofE_toE h v.1) }

end EVec

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
