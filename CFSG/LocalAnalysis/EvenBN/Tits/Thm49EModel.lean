module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.E32Orbits

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits.Model

abbrev Cm : Type := ℤˣ × Equiv.Perm (Fin 1755)

@[expose] def tauH : Cm := (-1, 1)

@[expose] def inA (a : Equiv.Perm (Fin 1755)) : Cm := (1, a)

@[expose] def Am : Subgroup Cm := (⊤ : Subgroup ℤˣ).prod titsA

@[expose] def GammaH : Subgroup Cm := Am ⊓ centralizer ({inA titsZ} : Set Cm)

@[expose] def KH (zp : Equiv.Perm (Fin 1755)) : Subgroup Cm :=
  GammaH ⊓ centralizer ({tauH * inA zp} : Set Cm)

@[expose] def MH : Set Cm :=
  {m | m = tauH ∨ ∃ l, IsLong l ∧ l * titsZ = titsZ * l ∧ m = tauH * inA l}

structure F6Facts (zp y0 : Equiv.Perm (Fin 1755)) : Prop where
  z_sq : titsZ * titsZ = 1
  z_mem : titsZ ∈ titsA
  zp_mem : zp ∈ titsA
  zp_long : IsLong zp
  zp_ne : zp ≠ titsZ
  zp_comm : titsZ * zp = zp * titsZ
  prod_not_long : ¬ IsLong (titsZ * zp)
  y0_mem : y0 ∈ titsA
  y0_z : y0 * titsZ * y0⁻¹ = zp
  y0_zp : y0 * zp * y0⁻¹ = titsZ
  swap : ∀ a b : Equiv.Perm (Fin 1755), IsLong a → IsLong b → a ≠ b → a * b = b * a →
    ¬ IsLong (a * b) → ∃ x ∈ titsA, x * a * x⁻¹ = b ∧ x * b * x⁻¹ = a

@[expose] def TOHat (zp y0 : Equiv.Perm (Fin 1755)) : Prop :=
  ∀ s : Cm → Cm,
    (∀ x ∈ GammaH, ∀ y ∈ GammaH, s (x * y) = s x * s y) →
    (∀ x ∈ GammaH, s x ∈ GammaH) →
    (∀ x ∈ GammaH, ∀ y ∈ GammaH, s x = s y → x = y) →
    s tauH = tauH * inA titsZ →
    s (inA titsZ) = inA titsZ →
    s (tauH * inA zp) = tauH * inA zp →
    (∀ m ∈ MH, m ∈ GammaH → s m ∈ MH) →
    ∀ θ : Cm → Cm, (∀ x, θ x = inA y0 * s x * (inA y0)⁻¹) →
      ¬ ∃ d ∈ KH zp, ∀ g ∈ KH zp, θ (θ (θ g)) = d * g * d⁻¹

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
