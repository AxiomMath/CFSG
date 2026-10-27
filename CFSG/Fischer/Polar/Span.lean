module

public import CFSG.Fischer.Polar.Basic
import all CFSG.Fischer.F4

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native Matrix

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos ptIdx uVec tvTabs

theorem uPts_get (x : Fin 693) : uPts[x.val]! = codeOf (uVec x) := (codeOf_uVec ptsFacts x.2).symm

theorem uPos_normC (w : Fin 6 → F4) : uPos[normC (codeOf w)]! = ptIdx w := by
  rw [uPos_get (by rw [normC_codeOf]; exact codeOf_lt _)]
  unfold ptIdx
  rfl

private theorem code_ω_sq : (F4.ω ^ 2).code.val = 3 := by decide

theorem lineC_eq (x y : Fin 693) : lineC x.val y.val = #[x.val, y.val, ptIdx (uVec x + uVec y),
    ptIdx (uVec x + F4.ω • uVec y), ptIdx (uVec x + F4.ω ^ 2 • uVec y)] := by
  have h2 : scaleC 2 (codeOf (uVec y)) = codeOf (F4.ω • uVec y) := scaleC_codeOf F4.ω (uVec y)
  have h3 : scaleC 3 (codeOf (uVec y)) = codeOf ((F4.ω ^ 2) • uVec y) := by
    have := scaleC_codeOf (F4.ω ^ 2) (uVec y)
    rwa [code_ω_sq] at this
  unfold lineC
  simp only [uPts_get]
  rw [h2, h3, ← codeOf_add, ← codeOf_add, ← codeOf_add, uPos_normC, uPos_normC, uPos_normC]

private theorem add_self_F4 : ∀ a : F4, a + a = 0 := by decide

private theorem F4_cases : ∀ c : F4, c = 0 ∨ c = 1 ∨ c = F4.ω ∨ c = F4.ω ^ 2 := by decide

theorem smul_add_smul_self (c : F4) (v : Fin 6 → F4) : c • v + c • v = 0 := by
  rw [← add_smul, add_self_F4, zero_smul]

theorem uVec_add_smul_ne_zero {x y : Fin 693} (hxy : x ≠ y) (c : F4) :
    uVec x + c • uVec y ≠ 0 := by
  intro h
  have hx : uVec x = c • uVec y := by
    calc uVec x = uVec x + (c • uVec y + c • uVec y) := by rw [smul_add_smul_self, add_zero]
      _ = (uVec x + c • uVec y) + c • uVec y := by rw [add_assoc]
      _ = c • uVec y := by rw [h, zero_add]
  by_cases hc : c = 0
  · rw [hc, zero_smul] at hx
    exact uVec_ne_zero ptsFacts x.2 hx
  · apply hxy
    apply Fin.ext
    rw [← ptIdx_uVec ptsFacts x.2, hx, ptIdx_smul hc, ptIdx_uVec ptsFacts y.2]

theorem hermStd_uVec_add_smul {x y : Fin 693} (h : perp x y) (c : F4) :
    hermStd (uVec x + c • uVec y) (uVec x + c • uVec y) = 0 := by
  have hxy : hermStd (uVec x) (uVec y) = 0 := h
  have hyx : hermStd (uVec y) (uVec x) = 0 := perp_comm.1 h
  rw [hermStd_add_left, hermStd_add_right, hermStd_add_right, hermStd_smul_left,
    hermStd_smul_left, hermStd_smul_right, hermStd_smul_right, uVec_iso ptsFacts x.2,
    uVec_iso ptsFacts y.2, hxy, hyx]
  ring

theorem uVec_ptIdx_add_smul {x y : Fin 693} (hxy : x ≠ y) (h : perp x y) (c : F4) :
    ∃ d : F4, d ≠ 0 ∧ uVec (ptIdx (uVec x + c • uVec y)) = d • (uVec x + c • uVec y) := by
  rw [uVec_ptIdx ptsFacts (uVec_add_smul_ne_zero hxy c) (hermStd_uVec_add_smul h c)]
  exact normV_eq_smul (uVec_add_smul_ne_zero hxy c)

theorem ptIdx_add_smul_lt {x y : Fin 693} (hxy : x ≠ y) (h : perp x y) (c : F4) :
    ptIdx (uVec x + c • uVec y) < 693 :=
  ptIdx_lt ptsFacts (uVec_add_smul_ne_zero hxy c) (hermStd_uVec_add_smul h c)

theorem mem_lineThru_iff {x y : Fin 693} (hxy : x ≠ y) (h : perp x y) (z : Fin 693) :
    z ∈ lineThru x y ↔ z.val ∈ lineC x.val y.val := by
  rw [lineC_eq]
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨a, b, hz⟩
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by
        rintro rfl
        rw [ha, zero_smul, zero_smul, add_zero] at hz
        exact uVec_ne_zero ptsFacts z.2 hz
      right; left
      rw [← ptIdx_uVec ptsFacts z.2, hz, ha, zero_smul, zero_add, ptIdx_smul hb,
        ptIdx_uVec ptsFacts y.2]
    · have hz' : uVec z = a • (uVec x + (a⁻¹ * b) • uVec y) := by
        rw [hz, smul_add, smul_smul, mul_inv_cancel_left₀ ha]
      have hzc : z.val = ptIdx (uVec x + (a⁻¹ * b) • uVec y) := by
        rw [← ptIdx_uVec ptsFacts z.2, hz', ptIdx_smul ha]
      rcases F4_cases (a⁻¹ * b) with hc | hc | hc | hc
      · left
        rw [hzc, hc, zero_smul, add_zero, ptIdx_uVec ptsFacts x.2]
      · right; right; left
        rw [hzc, hc, one_smul]
      · right; right; right; left
        rw [hzc, hc]
      · right; right; right; right
        rw [hzc, hc]
  · have key : ∀ c : F4, z.val = ptIdx (uVec x + c • uVec y) → z ∈ lineThru x y := by
      intro c hz
      obtain ⟨d, -, hd⟩ := uVec_ptIdx_add_smul hxy h c
      refine ⟨d, d * c, ?_⟩
      show uVec z.val = _
      rw [hz, hd, smul_add, smul_smul]
    rintro (hz | hz | hz | hz | hz)
    · refine ⟨1, 0, ?_⟩
      rw [show z = x from Fin.ext hz, one_smul, zero_smul, add_zero]
    · refine ⟨0, 1, ?_⟩
      rw [show z = y from Fin.ext hz, one_smul, zero_smul, zero_add]
    · exact key 1 (by rw [hz, one_smul])
    · exact key F4.ω hz
    · exact key (F4.ω ^ 2) hz

theorem normTab_get {c : ℕ} (hc : c < 4096) : (normTab ())[c]! = normC c := by
  unfold normTab
  rw [getElem!_pos _ c (by simpa using hc), Array.getElem_ofFn]

theorem scaleTab_get (a : ℕ) {c : ℕ} (hc : c < 4096) : (scaleTab a)[c]! = scaleC a c := by
  unfold scaleTab
  rw [getElem!_pos _ c (by simpa using hc), Array.getElem_ofFn]

theorem xor_lt_4096 {a b : ℕ} (ha : a < 4096) (hb : b < 4096) : a ^^^ b < 4096 :=
  Nat.xor_lt_two_pow (n := 12) ha hb

theorem lineF_eq (x y : Fin 693) :
    lineF (normTab ()) (scaleTab 2) (scaleTab 3) x.val y.val = lineC x.val y.val := by
  have hx := codeOf_lt (uVec x)
  have hy := codeOf_lt (uVec y)
  have h2 : scaleC 2 (codeOf (uVec y)) < 4096 := by
    rw [show scaleC 2 (codeOf (uVec y)) = codeOf (F4.ω • uVec y) from scaleC_codeOf F4.ω (uVec y)]
    exact codeOf_lt _
  have h3 : scaleC 3 (codeOf (uVec y)) < 4096 := by
    have := scaleC_codeOf (F4.ω ^ 2) (uVec y)
    rw [code_ω_sq] at this
    rw [this]
    exact codeOf_lt _
  unfold lineF lineC
  simp only [uPts_get]
  rw [scaleTab_get 2 hy, scaleTab_get 3 hy, normTab_get (xor_lt_4096 hx hy),
    normTab_get (xor_lt_4096 hx h2), normTab_get (xor_lt_4096 hx h3)]

theorem lineTab_get {x y : Fin 693} (h : perp x y) :
    (lineTab (perpTab ()))[x.val * 693 + y.val]! = lineC x.val y.val := by
  have hk : x.val * 693 + y.val < 693 * 693 := by have := x.2; have := y.2; nlinarith
  have hdiv : (x.val * 693 + y.val) / 693 = x.val := by have := y.2; omega
  have hmod : (x.val * 693 + y.val) % 693 = y.val := by have := y.2; omega
  unfold lineTab lineTabOf
  rw [getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn]
  simp only [hdiv, hmod]
  rw [ite_eq_left ((perpTab_spec x y).2 h)]
  exact lineF_eq x y

end CFSG.Fischer
