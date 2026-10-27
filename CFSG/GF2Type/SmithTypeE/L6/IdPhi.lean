module

public import CFSG.GF2Type.SmithTypeE.L6.ModConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LargeExtraspecial.SMod20 (V decode decode_apply)
open CFSG.GF2Type.SmithTypeE.LMod (tvEquiv tvEquiv_decode tvInv_parts)
open CFSG.SmithL6 (tvCols)
open CFSG.SmithE (applyCols)

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Phi (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] V) :
    S.M →* (V ≃ₗ[ZMod 2] V) where
  toFun g := φ.symm.trans (((S.ρ g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).trans φ)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp only [map_mul, Subgroup.coe_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

variable {S : Setting G} {φ : S.Qt ≃ₗ[ZMod 2] V}

theorem Phi_apply (g : S.M) (v : V) :
    Phi S φ g v = φ (((S.ρ g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (φ.symm v)) := rfl

theorem Phi_cl (g : S.M) {y : G} (hy : y ∈ S.QG) :
    Phi S φ g (φ (S.cl y)) = φ (S.cl ((g : G) * y * (g : G)⁻¹)) := by
  rw [Phi_apply, LinearEquiv.symm_apply_apply, S.ρ_cl g hy]

theorem Phi_eq_one_iff (g : S.M) : Phi S φ g = 1 ↔ (g : G) ∈ S.QG := by
  rw [← S.ρ_eq_one_iff]
  constructor
  · intro h
    apply Subtype.ext
    ext w
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => φ.symm (f (φ w))) h
    simpa [Phi_apply] using this
  · intro h
    ext v
    simp [Phi_apply, h]

theorem code_decode {c : Nat} (hc : c < 2 ^ 20) : SMG.code (decode c) = c := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [SMG.testBit_code]
  split_ifs with hi
  · rw [decode_apply]
    cases c.testBit i <;> rfl
  · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num)
      (by omega)))).symm

theorem applyCols_tvCols_lt {k : Nat} (hk : k < 1953) (c : Nat) :
    applyCols (tvCols k) c < 2 ^ 20 :=
  SMG.applyCols_lt (fun m hm => (tvInv_parts hk m (by
    simpa [CFSG.SmithL6.tvCols] using hm)).1) c

theorem acts_iff {x : G} (hx : x ∈ S.M) {k : Nat}
    (hk : k < 1953) :
    (∀ y ∈ S.QG, SMG.code (φ (S.cl (x * y * x⁻¹))) =
      applyCols (tvCols k) (SMG.code (φ (S.cl y)))) ↔ Phi S φ ⟨x, hx⟩ = tvEquiv k := by
  constructor
  · intro h
    ext v : 1
    obtain ⟨y, hy, hyv⟩ := S.exists_cl (φ.symm v)
    have hv : v = φ (S.cl y) := by rw [hyv, LinearEquiv.apply_symm_apply]
    rw [hv, Phi_cl ⟨x, hx⟩ hy, ← decode_code (φ (S.cl (x * y * x⁻¹))), h y hy,
      ← tvEquiv_decode hk, decode_code]
  · intro h y hy
    have e := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (φ (S.cl y))) h
    simp only [Phi_cl ⟨x, hx⟩ hy] at e
    rw [e, ← decode_code (φ (S.cl y)), tvEquiv_decode hk, code_decode (applyCols_tvCols_lt hk _),
      decode_code]

end CFSG.GF2Type.SmithTypeE.L6
