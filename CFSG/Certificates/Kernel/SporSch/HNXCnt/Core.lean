module

public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Base

public section

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX

theorem core_brecN_true (e t : Nat) : Bool.rec (motive := fun _ => Nat) e t true = t := rfl
theorem core_brecN_false (e t : Nat) : Bool.rec (motive := fun _ => Nat) e t false = e := rfl

theorem core_shr (x k : Nat) : Nat.shiftRight x k = x / 2 ^ k := Nat.shiftRight_eq_div_pow x k
theorem core_shl (x k : Nat) : Nat.shiftLeft x k = x * 2 ^ k := Nat.shiftLeft_eq x k

theorem core_edgeV_eq (T : Nat → Nat) (n MS y pos t : Nat) :
    edgeV T 464 n MS y pos t =
      Bool.rec (motive := fun _ => Nat) 1048576
        (Bool.rec (motive := fun _ => Nat) 1048576
          (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (pp T t) pos))
          (Nat.beq y (spread MS (xv T t)) && Nat.ble (pp T t) pos))
        (Nat.blt t n) := by
  unfold edgeV
  simp only [loopStrictN_eq]
  rfl

theorem core_edgeV_lt {T : Nat → Nat} {n MS y pos t : Nat}
    (h : edgeV T 464 n MS y pos t < 1048576) :
    t < n ∧ y = spread MS (xv T t) ∧ pp T t ≤ pos := by
  rw [core_edgeV_eq] at h
  cases h1 : Nat.blt t n
  · rw [h1] at h; exact absurd h (Nat.lt_irrefl _)
  cases h2 : (Nat.beq y (spread MS (xv T t)) && Nat.ble (pp T t) pos)
  · rw [h1, h2] at h; exact absurd h (Nat.lt_irrefl _)
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h2
  exact ⟨Nat.blt_eq.mp h1, h2.1, h2.2⟩

theorem core_edgeV_val {T : Nat → Nat} {n MS y pos t : Nat}
    (h : t < n ∧ y = spread MS (xv T t) ∧ pp T t ≤ pos) :
    edgeV T 464 n MS y pos t = if pp T t = pos then 1 else 0 := by
  rw [core_edgeV_eq]
  have h1 : Nat.blt t n = true := Nat.blt_eq.mpr h.1
  have h2 : (Nat.beq y (spread MS (xv T t)) && Nat.ble (pp T t) pos) = true := by
    rw [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq]; exact h.2
  rw [h1, h2]
  by_cases h3 : pp T t = pos
  · have : Nat.beq (pp T t) pos = true := Nat.beq_eq.mpr h3
    rw [this, if_pos h3]
  · have : Nat.beq (pp T t) pos = false := by
      cases h4 : Nat.beq (pp T t) pos
      · rfl
      · exact absurd (Nat.beq_eq.mp h4) h3
    rw [this, if_neg h3]

theorem core_posOK {i P Pp : Nat} (h : posOK i P Pp = true) :
    (i = 0 → P = 0) ∧ (0 < i → P ≤ 2 * i ∧ Pp < P) := by
  unfold posOK at h
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    exact ⟨fun _ => Nat.beq_eq.mp h, fun h' => absurd h' (Nat.lt_irrefl 0)⟩
  · have hb : Nat.beq i 0 = false := by
      cases h4 : Nat.beq i 0
      · rfl
      · exact absurd (Nat.beq_eq.mp h4) (Nat.pos_iff_ne_zero.mp hi)
    rw [hb] at h
    change (Nat.ble P (Nat.mul 2 i) && Nat.blt Pp P) = true at h
    rw [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    exact ⟨fun h' => absurd h' (Nat.pos_iff_ne_zero.mp hi), fun _ => h⟩

theorem core_rec (T : Nat → Nat) (b r : Nat) (hr : r < 64) :
    fldW (T b) (Nat.mul 464 r) 464 = getRec T 464 (64 * b + r) := by
  rw [getRec_leaf T b r hr, fldW_eq]
  rfl

theorem core_step_eq (T : Nat → Nat) (n MS YA YB b r st : Nat) (hr : r < 64) :
    coreStep T 464 n MS (T b) YA YB (64 * b) r st =
      Bool.rec (motive := fun _ => Nat) st
        (Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft 1048576 24)
          (Nat.add (pp T (64 * b + r)) (Nat.shiftLeft (Nat.add (Nat.shiftRight st 24)
            (Nat.add (edgeV T 464 n MS (fldW YA (1729 * r) 1729) (2 * (64 * b + r) + 1)
                (qv T 0 (64 * b + r)))
              (edgeV T 464 n MS (fldW YB (1729 * r) 1729) (2 * (64 * b + r) + 2)
                (qv T 1 (64 * b + r))))) 24))
          (posOK (64 * b + r) (pp T (64 * b + r)) (fldW st 0 24) &&
            (Nat.blt (edgeV T 464 n MS (fldW YA (1729 * r) 1729) (2 * (64 * b + r) + 1)
                (qv T 0 (64 * b + r))) 1048576 &&
              Nat.blt (edgeV T 464 n MS (fldW YB (1729 * r) 1729) (2 * (64 * b + r) + 2)
                (qv T 1 (64 * b + r))) 1048576)))
        (Nat.blt (Nat.shiftRight st 24) 1048576) := by
  unfold coreStep
  simp only [loopStrictN_eq]
  rw [core_rec T b r hr]
  rfl

theorem core_pp_lt (T : Nat → Nat) (i : Nat) : pp T i < 2 ^ 24 := by
  unfold pp
  rw [fldW_eq]
  have := Nat.mod_lt (getRec T 464 i / 2 ^ 441) (Nat.two_pow_pos 22)
  have h2 : (2 : Nat) ^ 22 ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by decide)
  omega

theorem core_shr_st (Q S : Nat) (hQ : Q < 2 ^ 24) :
    Nat.shiftRight (Q + 2 ^ 24 * S) 24 = S := by
  rw [core_shr, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 24), Nat.div_eq_of_lt hQ, Nat.zero_add]

theorem core_low_st (Q S : Nat) (hQ : Q < 2 ^ 24) : fldW (Q + 2 ^ 24 * S) 0 24 = Q := by
  rw [fldW_eq, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hQ]

@[expose] noncomputable def core_Q (T : Nat → Nat) (i : Nat) : Nat := if i = 0 then 0 else pp T (i - 1)

theorem core_Q_lt (T : Nat → Nat) (i : Nat) : core_Q T i < 2 ^ 24 := by
  unfold core_Q
  split
  · exact Nat.two_pow_pos 24
  · exact core_pp_lt T _

theorem core_init (T : Nat → Nat) (lo : Nat) : coreInit T 464 lo = core_Q T lo := by
  unfold coreInit core_Q
  by_cases h : lo = 0
  · subst h; rfl
  · have hb : Nat.beq lo 0 = false := by
      cases h4 : Nat.beq lo 0
      · rfl
      · exact absurd (Nat.beq_eq.mp h4) h
    rw [hb, if_neg h]
    rfl

@[expose] noncomputable def core_F (T : Nat → Nat) (n MS YA YB b m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (coreInit T 464 (64 * b))
    (fun r st => coreStep T 464 n MS (T b) YA YB (64 * b) r st) m

theorem core_F_zero (T : Nat → Nat) (n MS YA YB b : Nat) :
    core_F T n MS YA YB b 0 = core_Q T (64 * b) := by
  unfold core_F
  exact core_init T _

theorem core_F_succ (T : Nat → Nat) (n MS YA YB b m : Nat) :
    core_F T n MS YA YB b (m + 1) =
      coreStep T 464 n MS (T b) YA YB (64 * b) m (core_F T n MS YA YB b m) :=
  rfl

theorem core_unfold (T : Nat → Nat) (n MS CM3 M GA GB b c : Nat) :
    coreLeaf T 464 n MS CM3 M GA GB b c =
      Nat.shiftRight (core_F T n MS (mulC CM3 (leafA (T b) 464 c M) GA)
        (mulC CM3 (leafA (T b) 464 c M) GB) b c) 24 := by
  unfold coreLeaf
  simp only [loopStrictN_eq]
  have h6 : Nat.shiftLeft b 6 = 64 * b := by rw [core_shl]; omega
  rw [h6]
  rfl

@[expose] noncomputable def core_ind (T : Nat → Nat) (i : Nat) : Nat :=
  (if pp T (qv T 0 i) = 2 * i + 1 then 1 else 0) + (if pp T (qv T 1 i) = 2 * i + 2 then 1 else 0)

@[expose] def core_Good (T : Nat → Nat) (n MS YA YB b m : Nat) : Prop :=
  core_F T n MS YA YB b m =
      core_Q T (64 * b + m) + 2 ^ 24 * ∑ r ∈ Finset.range m, core_ind T (64 * b + r) ∧
    ∀ r < m, CoreRec T n MS YA YB (64 * b + r) r

theorem core_absorb (T : Nat → Nat) (n MS YA YB b m : Nat) (hm : m < 64)
    (h : 1048576 ≤ core_F T n MS YA YB b m / 2 ^ 24) :
    core_F T n MS YA YB b (m + 1) = core_F T n MS YA YB b m := by
  rw [core_F_succ, core_step_eq _ _ _ _ _ _ _ _ hm]
  have hb : Nat.blt (Nat.shiftRight (core_F T n MS YA YB b m) 24) 1048576 = false := by
    cases h4 : Nat.blt (Nat.shiftRight (core_F T n MS YA YB b m) 24) 1048576
    · rfl
    · rw [Nat.blt_eq, core_shr] at h4; omega
  rw [hb]

theorem core_record {T : Nat → Nat} {n MS YA YB b m : Nat}
    (hpos : posOK (64 * b + m) (pp T (64 * b + m)) (core_Q T (64 * b + m)) = true)
    (h0 : edgeV T 464 n MS (fldW YA (1729 * m) 1729) (2 * (64 * b + m) + 1)
      (qv T 0 (64 * b + m)) < 1048576)
    (h1 : edgeV T 464 n MS (fldW YB (1729 * m) 1729) (2 * (64 * b + m) + 2)
      (qv T 1 (64 * b + m)) < 1048576) :
    CoreRec T n MS YA YB (64 * b + m) m := by
  obtain ⟨p1, p2⟩ := core_posOK hpos
  obtain ⟨a1, a2, a3⟩ := core_edgeV_lt h0
  obtain ⟨b1, b2, b3⟩ := core_edgeV_lt h1
  refine ⟨fun hi => ?_, fun hi => ?_, a1, a2, a3, b1, b2, b3⟩
  · have := p1 hi; rw [hi] at this; exact this
  · have := p2 hi
    have hq : core_Q T (64 * b + m) = pp T (64 * b + m - 1) := by
      unfold core_Q; rw [if_neg (Nat.pos_iff_ne_zero.mp hi)]
    rw [hq] at this
    exact ⟨this.1, this.2⟩

theorem core_good_step (T : Nat → Nat) (n MS YA YB b m : Nat) (hm : m < 64)
    (hg : core_Good T n MS YA YB b m) :
    1048576 ≤ core_F T n MS YA YB b (m + 1) / 2 ^ 24 ∨ core_Good T n MS YA YB b (m + 1) := by
  obtain ⟨hF, hrec⟩ := hg
  have hQ := core_Q_lt T (64 * b + m)
  generalize hS : ∑ r ∈ Finset.range m, core_ind T (64 * b + r) = S at hF
  by_cases hSl : S < 1048576
  · unfold core_Good
    rw [core_F_succ, core_step_eq _ _ _ _ _ _ _ _ hm, hF, core_shr_st _ _ hQ, core_low_st _ _ hQ]
    have hb : Nat.blt S 1048576 = true := Nat.blt_eq.mpr hSl
    simp only [hb, core_brecN_true]
    cases hP : posOK (64 * b + m) (pp T (64 * b + m)) (core_Q T (64 * b + m))
    · left; simp only [Bool.false_and, core_brecN_false, core_shl]; omega
    cases he0 : Nat.blt (edgeV T 464 n MS (fldW YA (1729 * m) 1729) (2 * (64 * b + m) + 1)
        (qv T 0 (64 * b + m))) 1048576
    · left; simp only [Bool.false_and, Bool.and_false, core_brecN_false, core_shl]; omega
    cases he1 : Nat.blt (edgeV T 464 n MS (fldW YB (1729 * m) 1729) (2 * (64 * b + m) + 2)
        (qv T 1 (64 * b + m))) 1048576
    · left; simp only [Bool.and_false, core_brecN_false, core_shl]; omega
    right
    simp only [Bool.and_true, core_brecN_true]
    have r0 := Nat.blt_eq.mp he0
    have r1 := Nat.blt_eq.mp he1
    have hR := core_record hP r0 r1
    refine ⟨?_, fun r hr => ?_⟩
    · rw [core_edgeV_val (core_edgeV_lt r0), core_edgeV_val (core_edgeV_lt r1),
        Finset.sum_range_succ, hS, core_shl]
      have hq : core_Q T (64 * b + (m + 1)) = pp T (64 * b + m) := by
        unfold core_Q; rw [if_neg (by omega)]; rfl
      rw [hq]
      unfold core_ind
      change pp T (64 * b + m) + (S + (_ + _)) * 2 ^ 24 = _
      ring
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | hr
      · exact hrec r hr
      · subst hr; exact hR
  · left
    have hsame := core_absorb T n MS YA YB b m hm (by
      rw [hF, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 24), Nat.div_eq_of_lt hQ]; omega)
    rw [hsame, hF, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 24), Nat.div_eq_of_lt hQ]; omega

theorem core_inv (T : Nat → Nat) (n MS YA YB b : Nat) :
    ∀ m ≤ 64, 1048576 ≤ core_F T n MS YA YB b m / 2 ^ 24 ∨ core_Good T n MS YA YB b m := by
  intro m
  induction m with
  | zero =>
    intro _
    right
    refine ⟨?_, fun r hr => absurd hr (Nat.not_lt_zero _)⟩
    rw [core_F_zero, Finset.sum_range_zero, Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  | succ m ih =>
    intro hm
    rcases ih (by omega) with h | h
    · left; rw [core_absorb T n MS YA YB b m (by omega) h]; exact h
    · exact core_good_step T n MS YA YB b m (by omega) h

theorem coreLeaf_sound {T : Nat → Nat} {n MS CM3 M GA GB b c : Nat} (hc : c ≤ 64)
    (h : coreLeaf T 464 n MS CM3 M GA GB b c < 1048576) :
    (∀ r < c, CoreRec T n MS (mulC CM3 (leafA (T b) 464 c M) GA)
        (mulC CM3 (leafA (T b) 464 c M) GB) (64 * b + r) r) ∧
      coreLeaf T 464 n MS CM3 M GA GB b c =
        ∑ r ∈ Finset.range c,
          ((if pp T (qv T 0 (64 * b + r)) = 2 * (64 * b + r) + 1 then 1 else 0) +
            (if pp T (qv T 1 (64 * b + r)) = 2 * (64 * b + r) + 2 then 1 else 0)) := by
  rw [core_unfold, core_shr] at h ⊢
  rcases core_inv T n MS (mulC CM3 (leafA (T b) 464 c M) GA)
      (mulC CM3 (leafA (T b) 464 c M) GB) b c hc with h' | ⟨hF, hR⟩
  · omega
  · refine ⟨hR, ?_⟩
    rw [hF, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 24),
      Nat.div_eq_of_lt (core_Q_lt T _), Nat.zero_add]
    rfl

theorem coreLeaf_sound' {T : Nat → Nat} {n MS CM3 M GA GB b c : Nat} (hc : c ≤ 64)
    (h : coreLeaf T 464 n MS CM3 M GA GB b c < 1048576) :
    (∀ r < c, CoreRec T n MS (mulC CM3 (leafA (T b) 464 c M) GA)
        (mulC CM3 (leafA (T b) 464 c M) GB) (64 * b + r) r) ∧
      coreLeaf T 464 n MS CM3 M GA GB b c =
        ∑ r ∈ Finset.range c,
          ((if pp T (qv T 0 (64 * b + r)) = 2 * (64 * b + r) + 1 then 1 else 0) +
            (if pp T (qv T 1 (64 * b + r)) = 2 * (64 * b + r) + 2 then 1 else 0)) :=
  coreLeaf_sound hc h

end CFSG.KS.SporSch.HNXP

end
