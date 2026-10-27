module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplFin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsS8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {P : Type} [Group P] {V1 : Subgroup P} {φ : (Fin 5 → ZMod 2) → P}

theorem Sec128Coord.map_zero' (h : Sec128Coord V1 φ) : φ 0 = 1 := by
  have h1 := h.mul 0 0 s8_isEvenVec_zero s8_isEvenVec_zero
  rw [add_zero] at h1
  exact left_eq_mul.mp h1

theorem Sec128Coord.mul_self' (h : Sec128Coord V1 φ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    φ v * φ v = 1 := by
  have h1 := h.mul v v hv hv
  rw [s8_add_self, h.map_zero'] at h1
  exact h1.symm

theorem Sec128Coord.inv_eq' (h : Sec128Coord V1 φ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    (φ v)⁻¹ = φ v :=
  inv_eq_of_mul_eq_one_right (h.mul_self' hv)

theorem Sec128Coord.eq_of_eq' (h : Sec128Coord V1 φ) {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) (hvw : φ v = φ w) : v = w := by
  have h1 : φ (v + w) = 1 := by
    rw [h.mul v w hv hw, hvw]
    exact h.mul_self' hw
  have h2 := h.inj (v + w) (s8_isEvenVec_add hv hw) h1
  funext i
  have h3 := congrFun h2 i
  simp only [Pi.add_apply, Pi.zero_apply] at h3
  revert h3
  generalize v i = x
  generalize w i = y
  revert x y
  decide

theorem Sec128Coord.comm' (h : Sec128Coord V1 φ) {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) : φ v * φ w = φ w * φ v := by
  rw [← h.mul v w hv hw, ← h.mul w v hw hv, add_comm]

theorem Sec128Coord.comm_mem (h : Sec128Coord V1 φ) {x y : P} (hx : x ∈ V1) (hy : y ∈ V1) :
    x * y = y * x := by
  obtain ⟨v, hv, rfl⟩ := h.surj x hx
  obtain ⟨w, hw, rfl⟩ := h.surj y hy
  exact h.comm' hv hw

theorem Sec128Coord.mul_self_mem (h : Sec128Coord V1 φ) {x : P} (hx : x ∈ V1) : x * x = 1 := by
  obtain ⟨v, hv, rfl⟩ := h.surj x hx
  exact h.mul_self' hv

end CFSG.OddStandard.SmallF3.Omega
