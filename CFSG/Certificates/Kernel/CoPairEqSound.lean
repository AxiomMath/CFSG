module

public import Certificates.Data.Kernel.CoPairEq
public import CFSG.Certificates.Kernel.CoPairSound

public section

namespace CFSG.KC.CoPair

open CFSG.Monster.Existence.CoPair.Native

theorem bact_lt (T v : Nat) : bact T v < 2 ^ 24 :=
  Nat.xor_lt_two_pow (f24_lt _ _) (Nat.xor_lt_two_pow (f24_lt _ _) (f24_lt _ _))

theorem actXY_xor : ∀ (w : List Nat) (a b : Nat), actXY w (a ^^^ b) = actXY w a ^^^ actXY w b
  | [], _, _ => rfl
  | g :: w, a, b => by
    simp only [actXY]
    rw [actLetters_xor, actXY_xor w]

theorem bword_eq {TX TY : Nat} (hX : ∀ v < 2 ^ 24, bact TX v = actLetters (xWordN ()) v)
    (hY : ∀ v < 2 ^ 24, bact TY v = actLetters (yWordN ()) v) :
    ∀ (w : List Nat) (v : Nat), v < 2 ^ 24 → bword TX TY w v = actXY w v
  | [], _, _ => rfl
  | g :: w, v, hv => by
    change bword TX TY w (bact (Bool.rec (motive := fun _ => Nat) TY TX (Nat.beq g 0)) v) =
      actXY w (actLetters (if g == 0 then xWordN () else yWordN ()) v)
    by_cases hg : g = 0
    · subst hg
      rw [bword_eq hX hY w _ (bact_lt _ _)]
      exact congrArg (actXY w) (hX v hv)
    · have h1 : Nat.beq g 0 = false := by
        cases h : Nat.beq g 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hg
      have h2 : (g == 0) = false := by simpa using hg
      rw [h1, h2, bword_eq hX hY w _ (bact_lt _ _)]
      exact congrArg (actXY w) (hY v hv)

theorem wordTab_eq {M T TX TY : Nat} {w : List Nat}
    (hX : ∀ v < 2 ^ 24, bact TX v = actLetters (xWordN ()) v)
    (hY : ∀ v < 2 ^ 24, bact TY v = actLetters (yWordN ()) v)
    (hr : rowsW M TX TY w = true) (ht : tabOK M T = true) :
    ∀ v < 2 ^ 24, bact T v = actXY w v := by
  have hrow := (allN_iff _ _).1 hr
  intro v hv
  rw [tab_sound ht v hv, expand (actXY w) (actXY_xor w) 24 v hv, actM_eq]
  refine bitsX_congr_g v 24 fun i hi => ?_
  have := hrow i hi
  rw [Nat.beq_eq, show Nat.shiftLeft 1 i = 2 ^ i from Nat.one_shiftLeft i,
    bword_eq hX hY w _ (Nat.pow_lt_pow_right (by decide) hi)] at this
  exact this

theorem eqPt_spec {TA TB Q L SA SB m n i : Nat} (h : eqPt TA TB Q L SA SB m n i = true) :
    r16 (f64 L i) 0 < m ∧ f24 Q (r16 (f64 L i) 0) = bact TA (f24 Q i) ∧
    r16 (f64 L i) 1 < m ∧ f24 Q (r16 (f64 L i) 1) = bact TB (f24 Q i) ∧
    r16 (f64 L i) 2 < n ∧
    r16 (f64 L (r16 (f64 L i) 0)) 2 = f16 SA (r16 (f64 L i) 2) ∧
    r16 (f64 L (r16 (f64 L i) 1)) 2 = f16 SB (r16 (f64 L i) 2) ∧
    (i + 1 < m → f24 Q i < f24 Q (i + 1)) := by
  unfold eqPt at h
  simp only [letB_eq, andB_eq, ifB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, fun hi => by simpa [Nat.succ_eq_add_one, hi] using h7⟩

theorem eqOK_sound {a b : List Nat} {w n : Nat} {D : EqData} (h : eqOK a b w n D = true) :
    actXY a w = w ∧ actXY b w = w ∧
    (∀ i j, i < j → j < D.m → f24 D.Q i < f24 D.Q j) ∧
    (∀ i < D.m, r16 (f64 D.L i) 2 < n) ∧
    (∀ i < D.m, ∃ j < D.m, f24 D.Q j = actXY a (f24 D.Q i) ∧
      r16 (f64 D.L j) 2 = f16 D.SA (r16 (f64 D.L i) 2)) ∧
    (∀ i < D.m, ∃ j < D.m, f24 D.Q j = actXY b (f24 D.Q i) ∧
      r16 (f64 D.L j) 2 = f16 D.SB (r16 (f64 D.L i) 2)) ∧
    (∀ l < n, ∃ i < D.m, r16 (f64 D.L i) 2 = l) := by
  unfold eqOK at h
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hrx, hry, htx, hty, hra, hrb, hta, htb, hw, hwa, hwb, hall, hrep⟩ := h
  have hX := bact_eq hrx htx
  have hY := bact_eq hry hty
  have hA := wordTab_eq hX hY hra hta
  have hB := wordTab_eq hX hY hrb htb
  have hpt := fun i hi => eqPt_spec ((allN_iff _ _).1 hall i hi)
  refine ⟨by rw [← hA w hw, hwa], by rw [← hB w hw, hwb], ?_, fun i hi => (hpt i hi).2.2.2.2.1,
    fun i hi => ?_, fun i hi => ?_, fun l hl => ?_⟩
  · intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hstep := (hpt j (by omega)).2.2.2.2.2.2.2 hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact Nat.lt_trans (ih h' (by omega)) hstep
      · exact hstep
  · obtain ⟨h0, h1, -, -, -, h5, -⟩ := hpt i hi
    exact ⟨_, h0, by rw [h1, hA _ (f24_lt _ _)], h5⟩
  · obtain ⟨-, -, h2, h3, -, -, h6, -⟩ := hpt i hi
    exact ⟨_, h2, by rw [h3, hB _ (f24_lt _ _)], h6⟩
  · have := (allN_iff _ _).1 hrep l hl
    unfold repPt at this
    simp only [letB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact ⟨_, this.1, this.2⟩

theorem eqOK_intro {a b : List Nat} {w n : Nat} {D : EqData}
    (hrx : rowsOK D.MX (xWordN ()) = true) (hry : rowsOK D.MY (yWordN ()) = true)
    (htx : tabOK D.MX D.TX = true) (hty : tabOK D.MY D.TY = true)
    (hra : rowsW D.MA D.TX D.TY a = true) (hrb : rowsW D.MB D.TX D.TY b = true)
    (hta : tabOK D.MA D.TA = true) (htb : tabOK D.MB D.TB = true) (hw : w < 16777216)
    (hwa : bact D.TA w = w) (hwb : bact D.TB w = w)
    (hall : ∀ i < D.m, eqPt D.TA D.TB D.Q D.L D.SA D.SB D.m n i = true)
    (hrep : ∀ j < n, repPt D.L D.R D.m j = true) : eqOK a b w n D = true := by
  unfold eqOK
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
  exact ⟨hrx, hry, htx, hty, hra, hrb, hta, htb, hw, hwa, hwb, (allN_iff _ _).2 hall,
    (allN_iff _ _).2 hrep⟩

end CFSG.KC.CoPair

end
