module

public import CFSG.LargeExtraspecial.GLW4Basis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module Matrix QuadraticMap CFSG.LargeExtraspecial.GLR
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

theorem matX_inv (e : Basis (Fin 4) (ZMod 2) C.At) {x : C.Xbar} {g g' : Mat}
    (hx : matX C e x = g) (hg : g' * g = 1) : matX C e x⁻¹ = g' := by
  have h1 : matX C e x * matX C e x⁻¹ = 1 := by rw [← matX_mul, mul_inv_cancel, matX_one]
  rw [hx] at h1
  calc matX C e x⁻¹ = g' * g * matX C e x⁻¹ := by rw [hg, Matrix.one_mul]
    _ = g' := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem conj_eq_of_sp (e : Basis (Fin 4) (ZMod 2) C.At) {s : S.O} (hs : s ∈ S.Mbar)
    (hsX : s ∉ C.Xbar) (hJ : gram C e s = J) {x : C.Xbar} {g g' : Mat} (hx : matX C e x = g)
    (hg : g' * g = 1) (hsp : g'ᵀ * J * g' = J) : (x : S.O) * s * (x : S.O)⁻¹ = s := by
  have hm := matX_inv e hx hg
  have hxM : (x : S.O) ∈ S.Mbar := C.Xbar_le x.2
  refine eq_of_gram_eq e hJ hs hsX (S.Mbar.mul_mem (S.Mbar.mul_mem hxM hs) (S.Mbar.inv_mem hxM))
    (fun h => hsX ?_) hs hsX ?_
  · have := C.Xbar.mul_mem (C.Xbar.mul_mem (C.Xbar.inv_mem x.2) h) x.2
    simpa [mul_assoc] using this
  · rw [gram_conj, hm, hJ, hsp]

theorem commute_of_sp (e : Basis (Fin 4) (ZMod 2) C.At) {s : S.O} (hs : s ∈ S.Mbar)
    (hsX : s ∉ C.Xbar) (hJ : gram C e s = J) {x : C.Xbar} {g g' : Mat} (hx : matX C e x = g)
    (hg : g' * g = 1) (hsp : g'ᵀ * J * g' = J) : (x : S.O) * s = s * (x : S.O) := by
  have h := conj_eq_of_sp e hs hsX hJ hx hg hsp
  calc (x : S.O) * s = (x : S.O) * s * (x : S.O)⁻¹ * (x : S.O) := by group
    _ = s * (x : S.O) := by rw [h]

theorem matX_commutator (e : Basis (Fin 4) (ZMod 2) C.At) {x y : C.Xbar} {g g' k k' : Mat}
    (hx : matX C e x = g) (hg : g' * g = 1) (hy : matX C e y = k) (hk : k' * k = 1) :
    matX C e ⁅x, y⁆ = g * k * g' * k' := by
  rw [commutatorElement_def, matX_mul, matX_mul, matX_mul, hx, hy, matX_inv e hx hg,
    matX_inv e hy hk]

end CFSG.LargeExtraspecial.GLW4
