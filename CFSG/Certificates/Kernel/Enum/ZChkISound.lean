module

public import CFSG.Certificates.Kernel.Enum.ZChkI
public import CFSG.Certificates.Kernel.Enum.ZCSound
public import Mathlib.Tactic.Group

public section

namespace CFSG.KC.EnumSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb

variable {n w : Nat}

noncomputable def wG {A : Type} [Group A] (ga gb : A) (W : Nat) : Nat → A
  | 0 => 1
  | k + 1 => wG ga gb W k * (if Nat.beq (wl W k) 0 then ga else gb)

theorem wperm_prep_word {a b ai bi W len : Nat} {ga gb : Equiv.Perm (Fin n)} (hn : n < 16777216)
    (hw : n ≤ 2 ^ w) (ha : PRep n w a ga) (hb : PRep n w b gb)
    (hlet : ∀ k < len, wl W k < 2) :
    PRep n w (wperm n w (mask w) a b ai bi W len) (wG ga gb W len) := by
  have hlt : ∀ c < 2, ∀ q (hq : q < n), CFSG.KC.Enum.lt w (mask w) a b ai bi c q =
      ((if Nat.beq c 0 then ga else gb) ⟨q, hq⟩ : Nat) := by
    intro c hc q hq
    unfold CFSG.KC.Enum.lt
    simp only [PK.nIf_eq]
    by_cases h0 : Nat.beq c 0 = true
    · rw [if_pos h0, if_pos h0]
      exact ha ⟨q, hq⟩
    · have h1 : Nat.beq c 1 = true := by
        have : c ≠ 0 := fun e => h0 (by rw [e]; rfl)
        rw [show c = 1 by omega]
        rfl
      rw [if_neg h0, if_pos h1, if_neg h0]
      exact hb ⟨q, hq⟩
  have hfold : ∀ k ≤ len, ∀ q (hq : q < n),
      foldN k (fun k q => CFSG.KC.Enum.lt w (mask w) a b ai bi (wl W k) q) q =
        (wG ga gb W k ⟨q, hq⟩ : Nat) := by
    intro k
    induction k with
    | zero => exact fun _ q hq => by rw [PK.foldN_eq]; rfl
    | succ k ih =>
      intro hk q hq
      have e : ∀ (f : Nat → Nat → Nat) (s : Nat), foldN (k + 1) f s = foldN k f (f k s) :=
        fun f s => by
          rw [PK.foldN_eq, PK.foldN_eq, List.range_succ, List.foldr_append, List.foldr_cons,
            List.foldr_nil]
      rw [e, hlt _ (hlet k (by omega)) q hq,
        ih (by omega) _ ((if Nat.beq (wl W k) 0 then ga else gb) ⟨q, hq⟩).2]
      rfl
  have hf := hfold len le_rfl
  intro x
  set F : Nat → Nat := fun p =>
    foldN len (fun k q => CFSG.KC.Enum.lt w (mask w) a b ai bi (wl W k) q) p
  have hF : ∀ y < n, F y < 2 ^ w := fun y hy => by
    change foldN len _ y < 2 ^ w
    rw [hf y hy]
    exact Nat.lt_of_lt_of_le (wG ga gb W len ⟨y, hy⟩).2 hw
  have hc := PF.clog_spec hn
  have h := PF.fld_pmkT n w F hF (clog n) 0
  have e : wperm n w (mask w) a b ai bi W len = pmkT n w F (clog n) 0 := by
    unfold wperm pmk
    rw [PF.strictN_eqP]
  have hx : (x : Nat) < 2 ^ clog n := Nat.lt_of_lt_of_le x.2 hc
  rw [e, PF.pg_of_fld h (by simp only [hx, ↓reduceIte, Nat.zero_add, x.2]; exact hF x x.2)]
  simp only [hx, ↓reduceIte, Nat.zero_add, x.2]
  exact hf x x.2

theorem lChk_fields {T : Nat → Nat} {sh lm rb rm m nw pm iw im nL a ai b bi i : Nat}
    (h : lChk T sh lm rb rm n w m nw pm iw im nL a ai b bi i = true) :
    fld(rget T sh lm rb rm i, nw, im) < nL ∧
      eq3 n w m (rperm T sh lm rb rm pm fld(rget T sh lm rb rm i, nw, im)) a
        (rperm T sh lm rb rm pm i) ai = true ∧
      fld(rget T sh lm rb rm i, Nat.add nw iw, im) < nL ∧
      eq3 n w m (rperm T sh lm rb rm pm fld(rget T sh lm rb rm i, Nat.add nw iw, im)) b
        (rperm T sh lm rb rm pm i) bi = true := by
  unfold lChk at h
  simp only [PK.bAnd_eq, Bool.and_eq_true, PK.strictB_eq, Nat.blt_eq] at h
  obtain ⟨-, h2, h3, h4, h5⟩ := h
  exact ⟨h2, h4, h3, h5⟩

section Chain

variable {T : Nat → Nat} {sh lm rb rm nw pm iw im nL a ai b bi : Nat}
  {ga gb : Equiv.Perm (Fin n)} {U : Nat → Equiv.Perm (Fin n)}

theorem cStep_prep
    (hL : ∀ i < nL, lChk T sh lm rb rm n w (mask w) nw pm iw im nL a ai b bi i = true)
    (hU : ∀ i < nL, PRep n w (rperm T sh lm rb rm pm i) (U i))
    (ha : PRep n w a ga) (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb) (hbi : PRep n w bi gb⁻¹)
    (c : Nat) {i : Nat} (hi : i < nL) :
    fld(rget T sh lm rb rm i, nIf(Nat.beq c 0, nw, Nat.add nw iw), im) < nL ∧
      U fld(rget T sh lm rb rm i, nIf(Nat.beq c 0, nw, Nat.add nw iw), im) =
        (if Nat.beq c 0 then ga else gb) * U i * (if Nat.beq c 0 then ga else gb)⁻¹ := by
  obtain ⟨h1, h2, h3, h4⟩ := lChk_fields (hL i hi)
  cases hc : Nat.beq c 0
  · exact ⟨h3, prep_unique (hU _ h3) (eq3_prep h4 hb (hU i hi) hbi)⟩
  · exact ⟨h1, prep_unique (hU _ h1) (eq3_prep h2 ha (hU i hi) hai)⟩

theorem cIdx_prep {W : Nat}
    (hL : ∀ i < nL, lChk T sh lm rb rm n w (mask w) nw pm iw im nL a ai b bi i = true)
    (hU : ∀ i < nL, PRep n w (rperm T sh lm rb rm pm i) (U i))
    (ha : PRep n w a ga) (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb) (hbi : PRep n w bi gb⁻¹) :
    ∀ k, ∀ i < nL, cIdx T sh lm rb rm nw iw im W k i < nL ∧
      U (cIdx T sh lm rb rm nw iw im W k i) = wG ga gb W k * U i * (wG ga gb W k)⁻¹
  | 0, i, hi => ⟨hi, by
      change U i = 1 * U i * 1⁻¹
      simp⟩
  | k + 1, i, hi => by
    obtain ⟨hs, hse⟩ := cStep_prep hL hU ha hai hb hbi (wl W k) hi
    have e : cIdx T sh lm rb rm nw iw im W (k + 1) i = cIdx T sh lm rb rm nw iw im W k
        fld(rget T sh lm rb rm i, nIf(Nat.beq (wl W k) 0, nw, Nat.add nw iw), im) :=
      PK.strictN_eq _ (cIdx T sh lm rb rm nw iw im W k)
    obtain ⟨ih1, ih2⟩ := cIdx_prep hL hU ha hai hb hbi k _ hs
    refine ⟨by rw [e]; exact ih1, ?_⟩
    rw [e, ih2, hse, wG]
    group

theorem cPow_prep {W len : Nat}
    (hL : ∀ i < nL, lChk T sh lm rb rm n w (mask w) nw pm iw im nL a ai b bi i = true)
    (hU : ∀ i < nL, PRep n w (rperm T sh lm rb rm pm i) (U i))
    (ha : PRep n w a ga) (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb) (hbi : PRep n w bi gb⁻¹) :
    ∀ e, ∀ i < nL, cPow T sh lm rb rm nw iw im W len e i < nL ∧
      U (cPow T sh lm rb rm nw iw im W len e i) =
        wG ga gb W len ^ e * U i * (wG ga gb W len ^ e)⁻¹
  | 0, i, hi => ⟨hi, by
      change U i = _ ^ 0 * U i * (_ ^ 0)⁻¹
      simp⟩
  | e + 1, i, hi => by
    obtain ⟨hs, hse⟩ := cIdx_prep hL hU ha hai hb hbi (W := W) len i hi
    have ee : cPow T sh lm rb rm nw iw im W len (e + 1) i = cPow T sh lm rb rm nw iw im W len e
        (cIdx T sh lm rb rm nw iw im W len i) :=
      PK.strictN_eq _ (cPow T sh lm rb rm nw iw im W len e)
    obtain ⟨ih1, ih2⟩ := cPow_prep hL hU ha hai hb hbi e _ hs
    refine ⟨by rw [ee]; exact ih1, ?_⟩
    rw [ee, ih2, hse, pow_succ]
    group

end Chain

theorem zChkI_sound {T : Nat → Nat} {sh lm rb rm m nw pm iw im W len nE i : Nat}
    (h : zChkI T sh lm rb rm n w m nw pm iw im W len nE i = true) :
    ∃ e, 0 < e ∧ e < nE ∧ ∃ p < n,
      pg w m (rperm T sh lm rb rm pm i)
          (pg w m (rperm T sh lm rb rm pm (cPow T sh lm rb rm nw iw im W len e i)) p) ≠
        pg w m (rperm T sh lm rb rm pm (cPow T sh lm rb rm nw iw im W len e i))
          (pg w m (rperm T sh lm rb rm pm i) p) := by
  unfold zChkI at h
  simp only [PK.bAnd_eq, Bool.and_eq_true, PK.strictB_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨_, h1, h2, _, h3, Nat.ne_of_beq_eq_false (bIf_ft h4)⟩

theorem zRangeI_iff {T : Nat → Nat} {sh lm rb rm m nw pm iw im W len nE lo cnt : Nat} :
    zRangeI T sh lm rb rm n w m nw pm iw im W len nE lo cnt = true ↔
      ∀ k < cnt, zChkI T sh lm rb rm n w m nw pm iw im W len nE (lo + k) = true := by
  unfold zRangeI
  exact PK.allN_iff

theorem zChkI_prep {T : Nat → Nat} {sh lm rb rm nw pm iw im nL a ai b bi W len nE i : Nat}
    {ga gb : Equiv.Perm (Fin n)} {U : Nat → Equiv.Perm (Fin n)}
    (h : zChkI T sh lm rb rm n w (mask w) nw pm iw im W len nE i = true)
    (hL : ∀ i < nL, lChk T sh lm rb rm n w (mask w) nw pm iw im nL a ai b bi i = true)
    (hU : ∀ i < nL, PRep n w (rperm T sh lm rb rm pm i) (U i))
    (ha : PRep n w a ga) (hai : PRep n w ai ga⁻¹) (hb : PRep n w b gb) (hbi : PRep n w bi gb⁻¹)
    (hi : i < nL) :
    ∃ e, 0 < e ∧ e < nE ∧ ∃ j < nL, U j = wG ga gb W len ^ e * U i * (wG ga gb W len ^ e)⁻¹ ∧
      U i * U j ≠ U j * U i := by
  obtain ⟨e, he0, he, p, hp, hne⟩ := zChkI_sound h
  obtain ⟨hj, hUj⟩ := cPow_prep hL hU ha hai hb hbi (W := W) (len := len) e i hi
  refine ⟨e, he0, he, _, hj, hUj, fun hc => hne ?_⟩
  have e1 := congrArg (fun g : Equiv.Perm (Fin n) => ((g ⟨p, hp⟩ : Fin n) : Nat)) hc
  simp only [Equiv.Perm.mul_apply] at e1
  rw [prep_at (hU _ hj) hp, hU i hi, prep_at (hU i hi) hp, hU _ hj]
  exact e1

end CFSG.KC.EnumSound

end
