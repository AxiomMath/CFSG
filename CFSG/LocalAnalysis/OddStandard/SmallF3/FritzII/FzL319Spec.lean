module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Ev

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

@[expose] def fzW2 : F4c := fzW * fzW

@[expose] def fzRho0 : MulAut FzUT where
  toFun x := ⟨fzW2 * x.a, fzW2 * x.b, fzW * x.c⟩
  invFun x := ⟨fzW * x.a, fzW * x.b, fzW2 * x.c⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

@[expose] def FzInZ (x : FzUT) : Prop := x.a = 0 ∧ x.b = 0

structure FzValidTriple (t s l : MulAut FzUT) : Prop where
  t_sq : ∀ x, t (t x) = x
  t_rho : ∀ x, t (fzRho0 x) = fzRho0 (t x)
  t_Z : ∀ x, FzInZ (t x * x⁻¹)
  t_fix : (Finset.univ.filter fun x : FzUT => t x = x).card = 16
  s_sq : ∀ x, s (s x) = x
  s_rho : ∀ x, s (fzRho0 x) = fzRho0 (s x)
  s_ne : ∃ x, s x ≠ x
  ts : ∀ x, t (s x) = s (t x)
  s_inv : ∀ x, t x = x → s x = x⁻¹
  s_fix : ∀ x, t (s x * x⁻¹) = s x * x⁻¹
  l_sq : ∀ x, l (l x) = x
  l_rho : ∀ x, l (fzRho0 x) = fzRho0 (fzRho0 (l x))
  tl : ∀ x, t (l x) = l (t x)
  sl : ∀ x, s (l x) = l (s x)
  l_Z : ∃ z, FzInZ z ∧ l z ≠ z
  l_Q : ∃ x, t (l x * x⁻¹) ≠ l x * x⁻¹

structure FzValidX (t l : MulAut FzUT) (x₁ : FzUT) : Prop where
  fix : t x₁ = x₁
  x1_four : x₁ ^ 4 = 1
  x2_four : (l x₁) ^ 4 = 1
  comm : x₁ * l x₁ = l x₁ * x₁
  gen : ∀ y, t y = y ↔ ∃ i j : Fin 4, y = x₁ ^ (i : ℕ) * (l x₁) ^ (j : ℕ)

abbrev FzV : Type := ZMod 2 × ZMod 2 × ZMod 2

abbrev FzElt : Type := FzUT × FzV

@[expose] def fzAp (b : ZMod 2) (σ : MulAut FzUT) (q : FzUT) : FzUT := if b = 0 then q else σ q

@[expose] def fzAct (t s l : MulAut FzUT) (v : FzV) (q : FzUT) : FzUT :=
  fzAp v.1 t (fzAp v.2.1 s (fzAp v.2.2 l q))

@[expose] def fzMulC (t s l : MulAut FzUT) (x y : FzElt) : FzElt :=
  (x.1 * fzAct t s l x.2 y.1, x.2 + y.2)

@[expose] def fzOneC : FzElt := (1, 0)

@[expose] def fzInW (t : MulAut FzUT) (x : FzElt) : Prop :=
  t x.1 = x.1 ∧ x.2.2.1 = 0 ∧ x.2.2.2 = 0

inductive FzReach {X : Type} (m : X → X → X) (one : X) (gens : Set X) : X → Prop
  | one : FzReach m one gens one
  | gen {g : X} : g ∈ gens → FzReach m one gens g
  | mul {a b : X} : FzReach m one gens a → FzReach m one gens b → FzReach m one gens (m a b)

structure FzQ8 {X : Type} (m : X → X → X) (one : X) (a b : X) : Prop where
  four : m (m a a) (m a a) = one
  sq : m b b = m a a
  conj : m (m a b) a = b
  ne : m a a ≠ one

structure FzShapeAt {X : Type} (m : X → X → X) (one : X) (a11 a12 a21 a22 a31 a32 y : X) :
    Prop where
  quat₁ : FzQ8 m one a11 a12
  quat₂ : FzQ8 m one a21 a22
  quat₃ : FzQ8 m one a31 a32
  sq_eq : m a31 a31 = m (m a11 a11) (m a21 a21)
  comm₁₂ : ∀ u ∈ ({a11, a12} : Set X), ∀ w ∈ ({a21, a22} : Set X), m u w = m w u
  comm₁₃ : ∀ u ∈ ({a11, a12} : Set X), ∀ w ∈ ({a31, a32} : Set X), m u w = m w u
  comm₂₃ : ∀ u ∈ ({a21, a22} : Set X), ∀ w ∈ ({a31, a32} : Set X), m u w = m w u
  y_sq : m y y = one
  y_a11 : m (m y a11) y = a21
  y_a12 : m (m y a12) y = a22
  y_a31 : m y a31 = m a31 y
  y_a32 : m y a32 = m a32 y
  gen : ∀ e, FzReach m one {a11, a12, a21, a22, a31, a32, y} e

@[expose] def FzShape (t s l : MulAut FzUT) (x₁ : FzUT) : Prop :=
  ∃ r₁ r₃ : FzUT,
    FzShapeAt (fzMulC t s l) fzOneC (x₁, (1, 0, 0)) (r₁, (0, 1, 0)) (l x₁, (1, 0, 0))
      (fzMulC t s l (fzMulC t s l (1, (0, 0, 1)) (r₁, (0, 1, 0))) (1, (0, 0, 1)))
      ((x₁ * l x₁)⁻¹, (1, 0, 0)) (r₃, (0, 1, 0)) (1, (0, 0, 1))

@[expose] def FzNormSpec : Prop :=
  ∀ σ : MulAut FzUT, (∀ x, σ (σ (σ x)) = x) → (∀ x, x ≠ 1 → σ x ≠ x) →
    ∃ β : MulAut FzUT, ∀ x, β (σ x) = fzRho0 (β x)

end CFSG.OddStandard.SmallF3.FritzII
