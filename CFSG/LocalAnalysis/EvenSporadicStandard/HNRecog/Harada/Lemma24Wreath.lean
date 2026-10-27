module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

structure WreathData (P : Type*) [Group P] (e u w : P) : Prop where
  card_eq : Nat.card P = 64
  gen : Subgroup.closure ({e, u, w} : Set P) = ⊤
  e_sq : e * e = 1
  u_sq : u * u = 1
  w_sq : w * w = 1
  uw_comm : u * w = w * u
  conj_comm : ∀ g ∈ ({1, u, w, u * w} : Set P), ∀ h ∈ ({1, u, w, u * w} : Set P),
    Commute (g * e * g⁻¹) (h * e * h⁻¹)

private abbrev V2 : Type := Multiplicative (ZMod 2)

private abbrev V4 : Type := Fin 2 → V2

private abbrev Em : Type := V4 → V2

private def psiAut (q : V4) : MulAut Em where
  toFun f := fun z => f (q⁻¹ * z)
  invFun f := fun z => f (q * z)
  left_inv f := by funext z; simp
  right_inv f := by funext z; simp
  map_mul' f g := by funext z; rfl

private theorem psiAut_apply (q : V4) (f : Em) :
    psiAut q f = fun z => f (q⁻¹ * z) := rfl

private def psi : V4 →* MulAut Em where
  toFun := psiAut
  map_one' := by
    apply MulEquiv.ext
    intro f
    funext z
    simp [psiAut_apply]
  map_mul' q r := by
    apply MulEquiv.ext
    intro f
    funext z
    simp only [MulAut.mul_apply, psiAut_apply, mul_inv_rev, mul_assoc]

private instance instFiniteModel : Finite (Em ⋊[psi] V4) :=
  Finite.of_equiv (Em × V4) (SemidirectProduct.equivProd).symm

section

variable {P : Type*} [Group P] {e u w : P}

private theorem pow_mod_two {x : P} (hx : x * x = 1) (n : ℕ) : x ^ (n % 2) = x ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 2, pow_add, pow_mul, pow_two, hx, one_pow, mul_one]

private theorem z2hom_mul' {x : P} (hx : x * x = 1) (a b : V2) :
    x ^ (Multiplicative.toAdd (a * b)).val =
      x ^ (Multiplicative.toAdd a).val * x ^ (Multiplicative.toAdd b).val := by
  rw [toAdd_mul, ZMod.val_add, pow_mod_two hx, pow_add]

private theorem val_zero_two : (0 : ZMod 2).val = 0 := rfl

private theorem val_one_two : (1 : ZMod 2).val = 1 := rfl

private def z2hom (x : P) (hx : x * x = 1) : V2 →* P where
  toFun a := x ^ (Multiplicative.toAdd a).val
  map_one' := by rw [toAdd_one, val_zero_two, pow_zero]
  map_mul' := z2hom_mul' hx

private theorem z2hom_apply (x : P) (hx : x * x = 1) (a : V2) :
    z2hom x hx a = x ^ (Multiplicative.toAdd a).val := rfl

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
  · left; exact (ZMod.val_eq_zero a).mp (Nat.lt_one_iff.mp h)
  · right; exact (ZMod.val_eq_one Nat.one_lt_two a).mp h

private theorem z2hom_mem (x : P) (hx : x * x = 1) (a : V2) :
    z2hom x hx a ∈ ({1, x} : Set P) := by
  rw [z2hom_apply]
  rcases zmod_two_cases (Multiplicative.toAdd a) with h | h
  · rw [h, val_zero_two, pow_zero]; exact Or.inl rfl
  · rw [h, val_one_two, pow_one]; exact Or.inr rfl

private def vHom (h : WreathData P e u w) : V4 →* P where
  toFun q := z2hom u h.u_sq (q 0) * z2hom w h.w_sq (q 1)
  map_one' := by
    change z2hom u h.u_sq ((1 : V4) 0) * z2hom w h.w_sq ((1 : V4) 1) = 1
    simp
  map_mul' q r := by
    simp only [Pi.mul_apply, map_mul]
    exact ((show Commute u w from h.uw_comm).pow_pow (Multiplicative.toAdd (r 0)).val
      (Multiplicative.toAdd (q 1)).val).mul_mul_mul_comm _ _

private theorem vHom_apply (h : WreathData P e u w) (q : V4) :
    vHom h q = z2hom u h.u_sq (q 0) * z2hom w h.w_sq (q 1) := rfl

private def conjElt (h : WreathData P e u w) (q : V4) : P :=
  vHom h q * e * (vHom h q)⁻¹

private theorem conjElt_sq (h : WreathData P e u w) (q : V4) :
    conjElt h q * conjElt h q = 1 := by
  change (MulAut.conj (vHom h q)) e * (MulAut.conj (vHom h q)) e = 1
  rw [← map_mul (MulAut.conj (vHom h q)), h.e_sq, map_one]

private theorem vHom_mem (h : WreathData P e u w) (q : V4) :
    vHom h q ∈ ({1, u, w, u * w} : Set P) := by
  rw [vHom_apply]
  have h1 := z2hom_mem u h.u_sq (q 0)
  have h2 := z2hom_mem w h.w_sq (q 1)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> simp

private theorem commute_conjElt (h : WreathData P e u w) (x y : V4) :
    Commute (conjElt h x) (conjElt h y) :=
  h.conj_comm (vHom h x) (vHom_mem h x) (vHom h y) (vHom_mem h y)

private theorem eHom_comm (h : WreathData P e u w) :
    Pairwise fun x y => ∀ a b : V2,
      Commute (z2hom (conjElt h x) (conjElt_sq h x) a)
        (z2hom (conjElt h y) (conjElt_sq h y) b) := by
  intro x y _ a b
  rw [z2hom_apply, z2hom_apply]
  exact (commute_conjElt h x y).pow_pow _ _

private def eHom (h : WreathData P e u w) : Em →* P :=
  MonoidHom.noncommPiCoprod (fun x : V4 => z2hom (conjElt h x) (conjElt_sq h x))
    (eHom_comm h)

private theorem eHom_mulSingle (h : WreathData P e u w) (x : V4) (y : V2) :
    eHom h (Pi.mulSingle x y) = (conjElt h x) ^ (Multiplicative.toAdd y).val := by
  rw [eHom, MonoidHom.noncommPiCoprod_mulSingle, z2hom_apply]

private theorem psi_mulSingle (g x : V4) (y : V2) :
    psi g (Pi.mulSingle x y) = Pi.mulSingle (g * x) y := by
  funext z
  by_cases hz : z = g * x
  · subst hz
    simp [psi, psiAut, Pi.mulSingle]
  · have hz' : g⁻¹ * z ≠ x := by
      intro hh
      apply hz
      rw [show z = g * (g⁻¹ * z) from (mul_inv_cancel_left g z).symm, hh]
    simp [psi, psiAut, Pi.mulSingle, hz, hz']

private theorem lift_cond_hom (h : WreathData P e u w) (g : V4) :
    (eHom h).comp (psi g).toMonoidHom =
      (MulAut.conj (vHom h g)).toMonoidHom.comp (eHom h) := by
  apply MonoidHom.pi_ext
  intro x y
  change eHom h (psi g (Pi.mulSingle x y)) =
    MulAut.conj (vHom h g) (eHom h (Pi.mulSingle x y))
  rw [psi_mulSingle, eHom_mulSingle, eHom_mulSingle]
  rw [map_pow, MulAut.conj_apply]
  congr 1
  simp only [conjElt, map_mul, mul_assoc, mul_inv_rev]

private def wreathHom (h : WreathData P e u w) : Em ⋊[psi] V4 →* P :=
  SemidirectProduct.lift (eHom h) (vHom h) (lift_cond_hom h)

private def eE : Em := Pi.mulSingle 1 (Multiplicative.ofAdd 1)

private def uG : V4 := Pi.mulSingle 0 (Multiplicative.ofAdd 1)

private def wG : V4 := Pi.mulSingle 1 (Multiplicative.ofAdd 1)

private theorem wreathHom_inl_e (h : WreathData P e u w) :
    wreathHom h (SemidirectProduct.inl eE) = e := by
  rw [wreathHom, SemidirectProduct.lift_inl, eE, eHom_mulSingle, toAdd_ofAdd, val_one_two,
    pow_one]
  simp [conjElt]

private theorem wreathHom_inr_u (h : WreathData P e u w) :
    wreathHom h (SemidirectProduct.inr uG) = u := by
  rw [wreathHom, SemidirectProduct.lift_inr, vHom_apply, z2hom_apply, z2hom_apply]
  simp [uG, val_zero_two, val_one_two]

private theorem wreathHom_inr_w (h : WreathData P e u w) :
    wreathHom h (SemidirectProduct.inr wG) = w := by
  rw [wreathHom, SemidirectProduct.lift_inr, vHom_apply, z2hom_apply, z2hom_apply]
  simp [wG, val_zero_two, val_one_two]

private theorem wreathHom_surjective (h : WreathData P e u w) :
    Function.Surjective (wreathHom h) := by
  rw [← MonoidHom.range_eq_top]
  rw [eq_top_iff, ← h.gen]
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨SemidirectProduct.inl eE, wreathHom_inl_e h⟩
  · exact ⟨SemidirectProduct.inr uG, wreathHom_inr_u h⟩
  · exact ⟨SemidirectProduct.inr wG, wreathHom_inr_w h⟩

private theorem card_V2 : Nat.card V2 = 2 := Nat.card_zmod 2

private theorem card_V4 : Nat.card V4 = 4 := by
  rw [V4, Nat.card_fun, Nat.card_fin, card_V2]
  decide

private theorem card_Em : Nat.card Em = 16 := by
  rw [Em, Nat.card_fun, card_V4, card_V2]
  decide

private theorem card_model : Nat.card (Em ⋊[psi] V4) = 64 := by
  rw [SemidirectProduct.card, card_Em, card_V4]

private noncomputable def wreathMulEquiv (h : WreathData P e u w) :
    (Em ⋊[psi] V4) ≃* P :=
  MulEquiv.ofBijective (wreathHom h)
    ((Nat.bijective_iff_surjective_and_card (wreathHom h)).mpr
      ⟨wreathHom_surjective h, by rw [card_model, h.card_eq]⟩)

private theorem wreathMulEquiv_apply (h : WreathData P e u w) (x : Em ⋊[psi] V4) :
    wreathMulEquiv h x = wreathHom h x := rfl

private theorem wreathMulEquiv_inl_e (h : WreathData P e u w) :
    wreathMulEquiv h (SemidirectProduct.inl eE) = e := by
  rw [wreathMulEquiv_apply, wreathHom_inl_e]

private theorem wreathMulEquiv_inr_u (h : WreathData P e u w) :
    wreathMulEquiv h (SemidirectProduct.inr uG) = u := by
  rw [wreathMulEquiv_apply, wreathHom_inr_u]

private theorem wreathMulEquiv_inr_w (h : WreathData P e u w) :
    wreathMulEquiv h (SemidirectProduct.inr wG) = w := by
  rw [wreathMulEquiv_apply, wreathHom_inr_w]

end

theorem nonempty_mulEquiv_of_wreathData {P P' : Type*} [Group P] [Group P'] {e u w : P}
    {e' u' w' : P'} (h : WreathData P e u w) (h' : WreathData P' e' u' w') :
    ∃ φ : P ≃* P', φ e = e' ∧ φ u = u' ∧ φ w = w' := by
  have hsymm_e : (wreathMulEquiv h).symm e = SemidirectProduct.inl eE := by
    apply (wreathMulEquiv h).injective
    rw [MulEquiv.apply_symm_apply, wreathMulEquiv_inl_e h]
  have hsymm_u : (wreathMulEquiv h).symm u = SemidirectProduct.inr uG := by
    apply (wreathMulEquiv h).injective
    rw [MulEquiv.apply_symm_apply, wreathMulEquiv_inr_u h]
  have hsymm_w : (wreathMulEquiv h).symm w = SemidirectProduct.inr wG := by
    apply (wreathMulEquiv h).injective
    rw [MulEquiv.apply_symm_apply, wreathMulEquiv_inr_w h]
  refine ⟨(wreathMulEquiv h).symm.trans (wreathMulEquiv h'), ?_, ?_, ?_⟩
  · rw [MulEquiv.trans_apply, hsymm_e, wreathMulEquiv_inl_e h']
  · rw [MulEquiv.trans_apply, hsymm_u, wreathMulEquiv_inr_u h']
  · rw [MulEquiv.trans_apply, hsymm_w, wreathMulEquiv_inr_w h']

end CFSG.EvenSporadicStandard.HNRecog.Harada
