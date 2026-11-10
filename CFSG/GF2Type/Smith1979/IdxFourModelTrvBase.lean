
module

public import CFSG.GF2Type.Smith1979.IdxFourModelStab

@[expose] public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol

noncomputable def x0 : V12 ≃ₗ[ZMod 2] V12 := s12e

theorem x0_apply_code (v : V12) : x0 v = vecOf (appN s12Rows (codeOf v)) := by
  have h : x0 v = linOfRows s12Rows v := rfl
  rw [h, vecOf_appN, vecOf_codeOf]

theorem x0_mem_M0 : x0 ∈ M0 := s12e_mem_M0

theorem x0_comm_omegaE : x0 * omegaE = omegaE * x0 := s12e_comm_omegaE

theorem x0_mul_self : x0 * x0 = 1 := by
  refine LinearEquiv.ext fun v => ?_
  have h : mulR s12Rows s12Rows = idR := by decide +kernel
  rw [LinearEquiv.mul_apply]
  change linOfRows s12Rows (linOfRows s12Rows v) = v
  rw [← linOfRows_mulR, h, linOfRows_idR]

theorem theta0_w0 : theta0 w0 = vecOf 192 := by
  have := vecOf_theta0N (n := 3) (by norm_num)
  rw [show theta0N 3 = 192 by decide] at this
  exact this.symm

def W0 : Submodule (ZMod 2) V12 := spanOf [3, 192]

theorem mem_W0_iff (w : V12) :
    w ∈ W0 ↔ codeOf w = 0 ∨ codeOf w = 192 ∨ codeOf w = 3 ∨ codeOf w = 195 := by
  have h := mem_spanList_iff (vs := [3, 192]) (by decide) (codeOf_lt w)
  rw [vecOf_codeOf] at h
  rw [W0, ← h]
  simp [spanList]

theorem w0_mem_W0 : w0 ∈ W0 := by
  rw [mem_W0_iff]
  right; right; left
  unfold w0
  exact codeOf_vecOf (by norm_num)

theorem x0_sub_self_mem_W0 (v : V12) : x0 v - v ∈ W0 := by
  have h : (List.range 4096).all (fun n => (spanList [3, 192]).contains (appN s12Rows n ^^^ n)) =
      true := by decide +kernel
  have h1 := forall_lt_4096 h (codeOf v) (codeOf_lt v)
  rw [List.contains_iff_mem] at h1
  have hlt := appN_lt (okRows_spec okRows_s12Rows).2 (codeOf v)
  have h2 := (mem_spanList_iff (vs := [3, 192]) (by decide) (xor_lt hlt (codeOf_lt v))).1 h1
  rw [vecOf_xor] at h2
  have e : x0 v - v = vecOf (appN s12Rows (codeOf v)) + vecOf (codeOf v) := by
    rw [vec_sub_eq_add, x0_apply_code, vecOf_codeOf]
  rw [e]
  exact h2

theorem x0_sub_self_vecOf {n : ℕ} (hn : n < 4096) :
    x0 (vecOf n) - vecOf n = vecOf (appN s12Rows n ^^^ n) := by
  rw [vec_sub_eq_add, x0_apply_code, codeOf_vecOf hn, vecOf_xor]

theorem exists_x0_sub_self {w : V12} (hw : w ∈ W0) : ∃ v, x0 v - v = w := by
  rw [mem_W0_iff] at hw
  rw [← vecOf_codeOf w]
  rcases hw with h | h | h | h <;> rw [h]
  · exact ⟨vecOf 0, by rw [x0_sub_self_vecOf (by norm_num)]; rfl⟩
  · exact ⟨vecOf 64, by rw [x0_sub_self_vecOf (by norm_num)]; rfl⟩
  · exact ⟨vecOf 1, by rw [x0_sub_self_vecOf (by norm_num)]; rfl⟩
  · exact ⟨vecOf 65, by rw [x0_sub_self_vecOf (by norm_num)]; rfl⟩

theorem q0_eq_zero_of_mem_W0 {w : V12} (hw : w ∈ W0) : q0 w = 0 := by
  rw [mem_W0_iff] at hw
  have : q0b (codeOf w) = false := by
    rcases hw with h | h | h | h <;> rw [h] <;> decide
  have h := q0_vecOf (codeOf w)
  rw [vecOf_codeOf, this] at h
  simpa using h

end CFSG.GF2Type.Smith1979.IdxFour
