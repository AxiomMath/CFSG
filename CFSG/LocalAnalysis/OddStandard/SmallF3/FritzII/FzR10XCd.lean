module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10XDef

public section

namespace CFSG.OddStandard.SmallF3.FritzII

variable {G : Type} [Group G] {t x1 x2 : G} {W : Subgroup G}

@[expose] noncomputable def fzxCd (t x1 x2 w : G) : FzXW :=
  Function.invFun (fzxElt t x1 x2) w

private theorem fzrAux_conj3 (g a b c : G) :
    g * (a * b * c) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * c * g⁻¹) := by
  simp only [mul_assoc, inv_mul_cancel_left]

theorem fzxCd_elt (hb : FzXBasis t x1 x2 W) (v : FzXW) :
    fzxCd t x1 x2 (fzxElt t x1 x2 v) = v := by
  unfold fzxCd
  exact Function.leftInverse_invFun hb.inj v

theorem fzxElt_cd (hb : FzXBasis t x1 x2 W) {w : G} (hw : w ∈ W) :
    fzxElt t x1 x2 (fzxCd t x1 x2 w) = w := by
  obtain ⟨v, rfl⟩ := hb.surj w hw
  rw [fzxCd_elt hb]

theorem fzxCd_mul (hb : FzXBasis t x1 x2 W) {w w' : G} (hw : w ∈ W) (hw' : w' ∈ W) :
    fzxCd t x1 x2 (w * w') = fzxCd t x1 x2 w + fzxCd t x1 x2 w' := by
  obtain ⟨v, rfl⟩ := hb.surj w hw
  obtain ⟨v', rfl⟩ := hb.surj w' hw'
  rw [← hb.add, fzxCd_elt hb, fzxCd_elt hb, fzxCd_elt hb]

theorem fzxCd_pow (hb : FzXBasis t x1 x2 W) {w : G} (hw : w ∈ W) (n : ℕ) :
    fzxCd t x1 x2 (w ^ n) = n • fzxCd t x1 x2 w := by
  induction n with
  | zero =>
      rw [pow_zero, zero_nsmul]
      rw [show (1 : G) = fzxElt t x1 x2 0 from fzxElt_zero.symm]
      exact fzxCd_elt hb 0
  | succ n ih =>
      rw [pow_succ, fzxCd_mul hb (W.pow_mem hw n) hw, ih, succ_nsmul]

theorem fzxCd_t (hb : FzXBasis t x1 x2 W) : fzxCd t x1 x2 t = (1, 0, 0) := by
  have h := fzxCd_elt hb (1, 0, 0)
  rwa [fzxElt_t] at h

theorem fzxCd_x1 (hb : FzXBasis t x1 x2 W) : fzxCd t x1 x2 x1 = (0, 1, 0) := by
  have h := fzxCd_elt hb (0, 1, 0)
  rwa [fzxElt_x1] at h

theorem fzxCd_x2 (hb : FzXBasis t x1 x2 W) : fzxCd t x1 x2 x2 = (0, 0, 1) := by
  have h := fzxCd_elt hb (0, 0, 1)
  rwa [fzxElt_x2] at h

theorem fzxCd_conj (hb : FzXBasis t x1 x2 W) {g : G} (hg : ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    {w : G} (hw : w ∈ W) :
    fzxCd t x1 x2 (g * w * g⁻¹) =
      fzXMap (fzxCd t x1 x2 (g * t * g⁻¹)) (fzxCd t x1 x2 (g * x1 * g⁻¹))
        (fzxCd t x1 x2 (g * x2 * g⁻¹)) (fzxCd t x1 x2 w) := by
  have ht : t ∈ W := by
    have h := hb.mem (1, 0, 0)
    rwa [fzxElt_t] at h
  have hx1 : x1 ∈ W := by
    have h := hb.mem (0, 1, 0)
    rwa [fzxElt_x1] at h
  have hx2 : x2 ∈ W := by
    have h := hb.mem (0, 0, 1)
    rwa [fzxElt_x2] at h
  set v : FzXW := fzxCd t x1 x2 w with hv
  set c1 : FzXW := fzxCd t x1 x2 (g * t * g⁻¹) with hc1def
  set c2 : FzXW := fzxCd t x1 x2 (g * x1 * g⁻¹) with hc2def
  set c3 : FzXW := fzxCd t x1 x2 (g * x2 * g⁻¹) with hc3def
  have hwv : fzxElt t x1 x2 v = w := by rw [hv]; exact fzxElt_cd hb hw
  have hc1 : fzxElt t x1 x2 c1 = g * t * g⁻¹ := by
    rw [hc1def]; exact fzxElt_cd hb (hg t ht)
  have hc2 : fzxElt t x1 x2 c2 = g * x1 * g⁻¹ := by
    rw [hc2def]; exact fzxElt_cd hb (hg x1 hx1)
  have hc3 : fzxElt t x1 x2 c3 = g * x2 * g⁻¹ := by
    rw [hc3def]; exact fzxElt_cd hb (hg x2 hx2)
  have key : g * w * g⁻¹ =
      fzxElt t x1 x2 c1 ^ v.1.val * fzxElt t x1 x2 c2 ^ v.2.1.val *
        fzxElt t x1 x2 c3 ^ v.2.2.val := by
    rw [← hwv, hc1, hc2, hc3]
    unfold fzxElt
    rw [fzrAux_conj3]
    rw [← conj_pow, ← conj_pow, ← conj_pow]
  rw [key]
  have hA : fzxElt t x1 x2 c1 ^ v.1.val ∈ W := W.pow_mem (hb.mem c1) _
  have hB : fzxElt t x1 x2 c2 ^ v.2.1.val ∈ W := W.pow_mem (hb.mem c2) _
  have hC : fzxElt t x1 x2 c3 ^ v.2.2.val ∈ W := W.pow_mem (hb.mem c3) _
  rw [fzxCd_mul hb (W.mul_mem hA hB) hC, fzxCd_mul hb hA hB,
    fzxCd_pow hb (hb.mem c1) v.1.val, fzxCd_pow hb (hb.mem c2) v.2.1.val,
    fzxCd_pow hb (hb.mem c3) v.2.2.val,
    fzxCd_elt hb, fzxCd_elt hb, fzxCd_elt hb]
  rfl

end CFSG.OddStandard.SmallF3.FritzII
