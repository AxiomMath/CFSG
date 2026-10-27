module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.SectionRank.Ccomm

open Matrix

variable {p : ℕ} [hp : Fact p.Prime]

noncomputable def addAutEquivLinear (V : Type*) [AddCommGroup V] [Module (ZMod p) V] :
    Multiplicative (AddAut V) ≃* (V ≃ₗ[ZMod p] V) where
  toFun a := (Multiplicative.toAdd a).toLinearEquiv fun c x =>
    ZMod.map_smul (Multiplicative.toAdd a) c x
  invFun f := Multiplicative.ofAdd f.toAddEquiv
  left_inv _ := rfl
  right_inv f := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

noncomputable def mulAutEquivGL (n : ℕ) :
    MulAut (Multiplicative (Fin n → ZMod p)) ≃* GL (Fin n) (ZMod p) :=
  ((MulAutMultiplicative (Fin n → ZMod p)).trans
    (addAutEquivLinear (p := p) (Fin n → ZMod p))).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin n → ZMod p)).symm.trans
      Matrix.GeneralLinearGroup.toLin.symm)

theorem mulAutEquivGL_mulVec (n : ℕ) (α : MulAut (Multiplicative (Fin n → ZMod p)))
    (v : Fin n → ZMod p) :
    (mulAutEquivGL n α : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ v =
      Multiplicative.toAdd (α (Multiplicative.ofAdd v)) := by
  have h := congrArg (fun L : LinearMap.GeneralLinearGroup (ZMod p) (Fin n → ZMod p) =>
    (L : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) v)
    (Matrix.GeneralLinearGroup.toLin.apply_symm_apply
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin n → ZMod p)).symm
        (addAutEquivLinear (p := p) (Fin n → ZMod p)
          (MulAutMultiplicative (Fin n → ZMod p) α))))
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply] at h
  exact h

variable {W : Type*} [Group W]

theorem nonempty_mulEquiv_of_elementary [Finite W] (hcomm : ∀ a b : W, a * b = b * a)
    (hpow : ∀ a : W, a ^ p = 1) {n : ℕ} (hcard : Nat.card W = p ^ n) :
    Nonempty (W ≃* Multiplicative (Fin n → ZMod p)) := by
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hcomm }
  let _ : Module (ZMod p) (Additive W) := AddCommGroup.zmodModule (n := p) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hpow, ofMul_one]
  have hF : Module.Finite (ZMod p) (Additive W) := Module.Finite.of_finite
  have hFr : Module.Free (ZMod p) (Additive W) := Module.Free.of_divisionRing _ _
  have h := @Module.natCard_eq_pow_finrank (ZMod p) (Additive W) _ _ _ hF
  have hfin : Module.finrank (ZMod p) (Additive W) =
      Module.finrank (ZMod p) (Fin n → ZMod p) := by
    rw [Nat.card_zmod] at h
    rw [Module.finrank_fin_fun]
    exact Nat.pow_right_injective hp.out.two_le (h.symm.trans hcard)
  exact ⟨AddEquiv.toMultiplicativeRight
    (@LinearEquiv.ofFinrankEq (ZMod p) (Additive W) (Fin n → ZMod p) _ _ _ hFr _ _ _ _ hF _
      hfin).toAddEquiv⟩

noncomputable def elemAutEquivGL {n : ℕ} (e : W ≃* Multiplicative (Fin n → ZMod p)) :
    MulAut W ≃* GL (Fin n) (ZMod p) :=
  (MulAut.congr e).trans (mulAutEquivGL n)

theorem elemAutEquivGL_mulVec {n : ℕ} (e : W ≃* Multiplicative (Fin n → ZMod p))
    (α : MulAut W) (w : W) :
    (elemAutEquivGL e α : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ Multiplicative.toAdd (e w) =
      Multiplicative.toAdd (e (α w)) := by
  rw [elemAutEquivGL, MulEquiv.trans_apply, mulAutEquivGL_mulVec, ofAdd_toAdd]
  simp [MulAut.congr]

theorem elemAutEquivGL_eq_neg_one_iff {n : ℕ} (e : W ≃* Multiplicative (Fin n → ZMod p))
    (α : MulAut W) : elemAutEquivGL e α = -1 ↔ ∀ w : W, α w = w⁻¹ := by
  constructor
  · intro h w
    have h1 := elemAutEquivGL_mulVec e α w
    rw [h, Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec] at h1
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [← h1, map_inv, toAdd_inv]
  · intro h
    apply Units.ext
    rw [Units.val_neg, Units.val_one]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.neg_mulVec, Matrix.one_mulVec]
    obtain ⟨w, rfl⟩ : ∃ w, Multiplicative.toAdd (e w) = v :=
      ⟨e.symm (Multiplicative.ofAdd v), by simp⟩
    rw [elemAutEquivGL_mulVec, h, map_inv, toAdd_inv]

theorem card_mulAut_eq_card_GL {n : ℕ} (e : W ≃* Multiplicative (Fin n → ZMod p)) :
    Nat.card (MulAut W) = Nat.card (GL (Fin n) (ZMod p)) :=
  Nat.card_congr (elemAutEquivGL e).toEquiv

theorem card_GL_zmod (n : ℕ) :
    Nat.card (GL (Fin n) (ZMod p)) = ∏ i : Fin n, (p ^ n - p ^ (i : ℕ)) := by
  rw [Matrix.card_GL_field, ZMod.card]

theorem GL_one_comm {R : Type*} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

end CFSG.SectionRank.Ccomm
