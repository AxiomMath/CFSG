module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEpsInv

public section

open Subgroup CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace IIbSyl

@[expose] def f4mul (x y : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

@[expose] def red (c : ZMod 4 × ZMod 4) : ZMod 2 × ZMod 2 :=
  ((c.1.val : ZMod 2), (c.2.val : ZMod 2))

@[expose] def half (c : ZMod 4 × ZMod 4) : ZMod 2 × ZMod 2 :=
  (((c.1.val / 2 : ℕ) : ZMod 2), ((c.2.val / 2 : ℕ) : ZMod 2))

@[expose] def lift (x : ZMod 2 × ZMod 2) : ZMod 4 × ZMod 4 :=
  ((x.1.val : ZMod 4), (x.2.val : ZMod 4))

@[expose] def dbl (x : ZMod 2 × ZMod 2) : ZMod 4 × ZMod 4 :=
  (((2 * x.1.val : ℕ) : ZMod 4), ((2 * x.2.val : ℕ) : ZMod 4))

@[expose] def rhoFun (r : ZMod 2 × ZMod 2) (c : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 :=
  c + dbl (f4mul (red c) r)

theorem rhoFun_add : ∀ (r : ZMod 2 × ZMod 2) (c d : ZMod 4 × ZMod 4),
    rhoFun r (c + d) = rhoFun r c + rhoFun r d := by decide

theorem rhoFun_rhoFun : ∀ (r : ZMod 2 × ZMod 2) (c : ZMod 4 × ZMod 4),
    rhoFun r (rhoFun r c) = c := by decide

theorem rhoFun_add_left : ∀ (r s : ZMod 2 × ZMod 2) (c : ZMod 4 × ZMod 4),
    rhoFun (r + s) c = rhoFun r (rhoFun s c) := by decide

theorem rhoFun_zero : ∀ c : ZMod 4 × ZMod 4, rhoFun 0 c = c := by decide

abbrev C0 : Type := Multiplicative (ZMod 4 × ZMod 4)

abbrev R0 : Type := Multiplicative (ZMod 2 × ZMod 2)

@[expose] def rhoAut (r : R0) : MulAut C0 where
  toFun c := Multiplicative.ofAdd (rhoFun (Multiplicative.toAdd r) (Multiplicative.toAdd c))
  invFun c := Multiplicative.ofAdd (rhoFun (Multiplicative.toAdd r) (Multiplicative.toAdd c))
  left_inv c := by simp [rhoFun_rhoFun]
  right_inv c := by simp [rhoFun_rhoFun]
  map_mul' c d := by simp [rhoFun_add]

@[expose] def rho : R0 →* MulAut C0 where
  toFun := rhoAut
  map_one' := MulEquiv.ext fun c => by
    change Multiplicative.ofAdd (rhoFun (Multiplicative.toAdd (1 : R0))
      (Multiplicative.toAdd c)) = c
    rw [toAdd_one, rhoFun_zero, ofAdd_toAdd]
  map_mul' r s := MulEquiv.ext fun c => by
    change Multiplicative.ofAdd (rhoFun (Multiplicative.toAdd (r * s))
      (Multiplicative.toAdd c)) = Multiplicative.ofAdd (rhoFun (Multiplicative.toAdd r)
        (Multiplicative.toAdd (Multiplicative.ofAdd (rhoFun (Multiplicative.toAdd s)
          (Multiplicative.toAdd c)))))
    rw [toAdd_mul, rhoFun_add_left, toAdd_ofAdd]

abbrev P0 : Type := C0 ⋊[rho] R0

instance instDecidableEqP0 : DecidableEq P0 := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) (by
    constructor
    · rintro ⟨h1, h2⟩; exact SemidirectProduct.ext h1 h2
    · rintro rfl; exact ⟨rfl, rfl⟩)

instance instFintypeP0 : Fintype P0 := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

@[expose] def psiF (b : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 := if b = 0 then 0 else (1, 0)

@[expose] def thC (c : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 :=
  lift (f4mul (red c) (red c)) + dbl (psiF (red c) + f4mul (half c) (half c))

@[expose] def thetaFun (p : P0) : P0 :=
  ⟨Multiplicative.ofAdd (thC (Multiplicative.toAdd p.left)),
    Multiplicative.ofAdd (f4mul (Multiplicative.toAdd p.right) (Multiplicative.toAdd p.right))⟩

theorem thetaFun_mul : ∀ p q : P0, thetaFun (p * q) = thetaFun p * thetaFun q := by
  decide +kernel

theorem thetaFun_thetaFun : ∀ p : P0, thetaFun (thetaFun p) = p := by decide +kernel

@[expose] def theta : MulAut P0 where
  toFun := thetaFun
  invFun := thetaFun
  left_inv := thetaFun_thetaFun
  right_inv := thetaFun_thetaFun
  map_mul' := thetaFun_mul

theorem theta_mul_theta : theta * theta = 1 := MulEquiv.ext fun p => thetaFun_thetaFun p

@[expose] def psi : Multiplicative (ZMod 2) →* MulAut P0 where
  toFun e := if e = 1 then 1 else theta
  map_one' := by simp
  map_mul' a b := by
    have h : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
    rcases h a with rfl | rfl <;> rcases h b with rfl | rfl
    · simp
    · simp
    · simp
    · have h2 : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
      have h1 : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
      rw [h2]
      simp only [h1, ite_false, ite_true]
      exact theta_mul_theta.symm

end IIbSyl

abbrev IIbSyl : Type := IIbSyl.P0 ⋊[IIbSyl.psi] Multiplicative (ZMod 2)

namespace IIbSyl

instance instDecidableEqIIbSyl : DecidableEq IIbSyl := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) (by
    constructor
    · rintro ⟨h1, h2⟩; exact SemidirectProduct.ext h1 h2
    · rintro rfl; exact ⟨rfl, rfl⟩)

instance instFintypeIIbSyl : Fintype IIbSyl :=
  Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

theorem card_IIbSyl : Nat.card IIbSyl = 128 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

@[expose] def vElt (x y : ZMod 2 × ZMod 2) : IIbSyl :=
  ⟨⟨Multiplicative.ofAdd (dbl x), Multiplicative.ofAdd y⟩, 1⟩

@[expose] def vHom : Multiplicative ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) →* IIbSyl where
  toFun p := vElt (Multiplicative.toAdd p).1 (Multiplicative.toAdd p).2
  map_one' := by decide
  map_mul' := by decide

@[expose] def v0Hom : Multiplicative (ZMod 2 × ZMod 2) →* IIbSyl where
  toFun x := vElt (Multiplicative.toAdd x) 0
  map_one' := by decide
  map_mul' := by decide

@[expose] def rHom : Multiplicative (ZMod 2 × ZMod 2) →* IIbSyl where
  toFun y := vElt 0 (Multiplicative.toAdd y)
  map_one' := by decide
  map_mul' := by decide

@[expose] def V0 : Subgroup IIbSyl := v0Hom.range

@[expose] def R : Subgroup IIbSyl := rHom.range

@[expose] def V : Subgroup IIbSyl := vHom.range

@[expose] def P : Subgroup IIbSyl := (SemidirectProduct.inl : P0 →* IIbSyl).range

@[expose] def chi : IIbSyl →* Multiplicative (ZMod 2) where
  toFun s := Multiplicative.ofAdd (Multiplicative.toAdd s.left.right).2
  map_one' := by decide
  map_mul' := by decide +kernel

@[expose] def S0 : Subgroup IIbSyl := chi.ker

@[expose] def t : IIbSyl := SemidirectProduct.inr (Multiplicative.ofAdd 1)

@[expose] def z0 : IIbSyl := vElt (1, 0) 0

@[expose] def a : IIbSyl := vElt 0 (1, 0)

@[expose] def sigma : IIbSyl := vElt 0 (0, 1)

@[expose] def c1 : IIbSyl := ⟨⟨Multiplicative.ofAdd (1, 0), Multiplicative.ofAdd (1, 0)⟩, 1⟩

end IIbSyl

variable {G : Type} [Group G]

@[expose] def IIbEmb (S₁ S₀ P V₀ R : Subgroup G) (t z₀ a σ c₁ : G) : Prop :=
  ∃ f : IIbSyl →* G, Function.Injective f ∧ f.range = S₁ ∧ IIbSyl.S0.map f = S₀ ∧
    IIbSyl.P.map f = P ∧ IIbSyl.V0.map f = V₀ ∧ IIbSyl.R.map f = R ∧ f IIbSyl.t = t ∧
    f IIbSyl.z0 = z₀ ∧ f IIbSyl.a = a ∧ f IIbSyl.sigma = σ ∧ f IIbSyl.c1 = c₁

structure IIbData (A R T V₀ P : Subgroup G) (t z₀ a σ c₁ : G) : Prop where
  sylowP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀)
  inf_P : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T
  outer : OuterInvol R T V₀ P t z₀ a
  sylow : IsSylowOf 2 (P ⊔ zpowers t) ⊤
  emb : IIbEmb (P ⊔ zpowers t) ((P ⊔ zpowers t) ⊓ rankTwoX A) P V₀ R t z₀ a σ c₁
  sigma_conj : ∀ x : G, x⁻¹ * σ * x ∈ P ⊔ zpowers t →
    x⁻¹ * σ * x ∈ R ⊔ T ∧ x⁻¹ * σ * x ∉ V₀ ⊔ zpowers a
  not_conj : ¬ IsConj t z₀
  good : ∀ x u : G, u ∈ centralizer ((rightConjugate V₀ x : Subgroup G) : Set G) →
    IsPGroup 2 (zpowers u) → u * u ∈ rightConjugate V₀ x

@[expose] def Asc310IIbStep4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (T V₀ : Subgroup G),
    Setting310 A R g T V₀ →
    centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G) →
      ∃ (P : Subgroup G) (t z₀ a σ c₁ : G), IIbData A R T V₀ P t z₀ a σ c₁

@[expose] def Asc310IIbStep56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (T V₀ P : Subgroup G)
    (t z₀ a σ c₁ : G), Setting310 A R g T V₀ →
    centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G) →
    IIbData A R T V₀ P t z₀ a σ c₁ → NativeSporadic.IsSporadic (rankTwoX A) .M12

end CFSG.ComponentClassification.RankTwoAltFive
