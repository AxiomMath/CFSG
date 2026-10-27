module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK

structure AutData89 {Kb : Type} [Group Kb] (B Eb : Subgroup (MulAut Kb)) (xb rb sb fb : MulAut Kb)
    (k₁ k₂ : Kb) : Prop where
  r_mem : rb ∈ B ⊓ innAut Kb
  s_mem : sb ∈ B ⊓ innAut Kb
  r4 : rb ^ 4 = 1
  s2 : sb ^ 2 = 1
  srs : sb * rb * sb⁻¹ = rb⁻¹
  r2_ne : rb ^ 2 ≠ 1
  P_gen : ∀ p ∈ B ⊓ innAut Kb, ∃ i j : ℕ, p = rb ^ i * sb ^ j
  x_r : xb * rb * xb⁻¹ = rb⁻¹
  x_s : xb * sb * xb⁻¹ = rb * sb ∨ xb * sb * xb⁻¹ = rb ^ 3 * sb
  f_mem : fb ∈ Eb
  f2 : fb ^ 2 = 1
  f_cent : ∀ p ∈ B ⊓ innAut Kb, fb * p = p * fb
  f_ne_one : fb ≠ 1
  f_ne_z : fb ≠ rb ^ 2
  B_gen : ∀ b ∈ B, ∃ p ∈ B ⊓ innAut Kb, ∃ i j : ℕ, b = p * fb ^ i * xb ^ j
  C_P : ∀ b ∈ B, (∀ p ∈ B ⊓ innAut Kb, b * p = p * b) → ∃ i j : ℕ, b = rb ^ (2 * i) * fb ^ j
  Z_B : ∀ b ∈ B, (∀ b' ∈ B, b * b' = b' * b) → b = 1 ∨ b = rb ^ 2
  xf : xb * fb * xb⁻¹ = rb ^ 2 * fb
  s_E : sb ∈ Eb
  z_E : rb ^ 2 ∈ Eb
  k1_z : MulAut.conj k₁ * rb ^ 2 * (MulAut.conj k₁)⁻¹ = sb
  k1_s : MulAut.conj k₁ * sb * (MulAut.conj k₁)⁻¹ = rb ^ 2
  k1_f : fb * MulAut.conj k₁ = MulAut.conj k₁ * fb
  k2_z : MulAut.conj k₂ * rb ^ 2 * (MulAut.conj k₂)⁻¹ = rb ^ 2
  k2_s : MulAut.conj k₂ * sb * (MulAut.conj k₂)⁻¹ = rb ^ 2 * sb
  k2_f : fb * MulAut.conj k₂ = MulAut.conj k₂ * fb

end CFSG.GH74.GLS.C3.Layer1.P89

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1.P89

@[expose] def B_prop89_autlevel : Prop :=
  ∀ (Kb : Type) [Group Kb] [Finite Kb], HasL2Model Kb (fun q => q = 9) →
    ∀ B : Subgroup (MulAut Kb), IsPGroup 2 ↥B → IsSylowOf 2 (B ⊓ innAut Kb) (innAut Kb) →
      ∀ xb ∈ B, xb ^ 2 = 1 → xb ∉ innAut Kb →
        IsPGL2 ↥(innAut Kb ⊔ zpowers xb) (fun q => q = 9) →
        ∀ Eb : Subgroup (MulAut Kb), Eb ≤ B → Open.IsElemAbelian 2 Eb → 8 ≤ Nat.card ↥Eb →
          ∃ (rb sb fb : MulAut Kb) (k₁ k₂ : Kb), AutData89 B Eb xb rb sb fb k₁ k₂

end CFSG.GH74.GLS
