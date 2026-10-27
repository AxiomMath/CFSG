module

public import Certificates.Data.FzR10
public import Mathlib.Data.Finset.Card

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10

structure FzMul (e : ℕ → ℕ → ℕ) : Prop where
  lt : ∀ x y, x < 512 → y < 512 → e x y < 512
  assoc : ∀ x y z, x < 512 → y < 512 → z < 512 → e (e x y) z = e x (e y z)
  one_r : ∀ x, x < 512 → e x 0 = x
  one_l : ∀ x, x < 512 → e 0 x = x

abbrev fzrS (P : Par) (x : ℕ) : Prop := x < 512 ∧ P.e x P.tI = P.e P.tI x

@[expose] def fzrCent (P : Par) (u : ℕ) : Finset ℕ :=
  (Finset.range 512).filter fun x => P.e x u = P.e u x

@[expose] def fzrH (P : Par) (f₀ f₁ : ℕ → Bool) : Finset ℕ :=
  (Finset.range 512).filter fun x => fzrS P x ∧ f₀ x = false ∧ f₁ x = false

open Classical in
@[expose] noncomputable def fzrKey (P : Par) (θ : ℕ → Prop) (x : ℕ) : ℕ :=
  kord P.e x * 2 + if θ x then 1 else 0

structure FzRules (P : Par) (θ : ℕ → Prop) : Prop where
  mul : FzMul P.e
  tI_lt : P.tI < 512
  sI_lt : P.sI < 512
  gens_lt : ∀ g ∈ P.gens.toList, g < 512
  rho_lt : ∀ x, x < 256 → P.rhoMap x < 512
  th_t : θ P.tI
  th_inv : ∀ x, θ x → x < 512 ∧ x ≠ 0 ∧ P.e x x = 0
  conj : ∀ g x y, g < 512 → x < 512 → y < 512 → P.e y g = P.e g x → (θ x ↔ θ y)
  rho : ∀ x, x < 256 → (θ x ↔ θ (P.rhoMap x))
  forb : ∀ x, x < 512 → P.inTL x = true → x ≠ 0 → P.e x x = 0 → ¬ θ x
  wrule : ∀ x, P.inW x = true → θ x → P.inTZ x = true
  ktl : ∀ x, x < 512 → P.inTL x = true → x ≠ 0 → P.e x x = 0 → θ (P.e P.tI x)
  kout : ∀ sp, (sp = P.sI ∨ sp = P.e P.tI P.sI) → ∀ l, l < 512 → P.inTL l = true →
    P.e (P.e l sp) (P.e l sp) = 0 → (θ (P.e l sp) ↔ θ sp)
  cover : ∀ f : ℕ → Bool, (∀ x y, x < 512 → y < 512 → f (P.e x y) = xor (f x) (f y)) →
    f P.tI = true → ∃ x, x < 512 ∧ θ x ∧ f x = false
  prof : ∀ u, θ u → 32 ≤ (fzrCent P u).card →
    ∃ f₀ f₁ : ℕ → Bool,
      (∀ x y, fzrS P x → fzrS P y → f₀ (P.e x y) = xor (f₀ x) (f₀ y)) ∧
      (∀ x y, fzrS P x → f₀ x = false → fzrS P y → f₀ y = false →
        f₁ (P.e x y) = xor (f₁ x) (f₁ y)) ∧
      f₀ P.tI = false ∧ f₁ P.tI = false ∧
      (fzrH P f₀ f₁).card = (fzrCent P u).card ∧
      ∀ k, ((fzrH P f₀ f₁).filter fun x => fzrKey P θ x = k).card =
        ((fzrCent P u).filter fun x => fzrKey P θ x = k).card

end CFSG.OddStandard.SmallF3.FritzII
