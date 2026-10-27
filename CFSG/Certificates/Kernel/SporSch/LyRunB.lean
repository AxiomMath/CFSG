module

public import CFSG.Certificates.Kernel.SporSch.LyMatLemmas
public import CFSG.Sporadic.Schreier.LyCheckSylow
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KS.SporSch.LyRB

open CFSG.KC.Enum CFSG.KC.Ord CFSG.KS CFSG.KS.Ord CFSG.KS.SporSch.LyM CFSG.KS.SporSch.LyLoop
open CFSG.Sporadic.He.Native CFSG.Sporadic.LySchreier.Native

theorem diffMod5_eqL {w S T L H CM RM ONE LV HV X Y : Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true) (hY : validM 5 (111 * S) L H Y = true) :
    diffMod5 (unpackL 111 w S X) (unpackL 111 w S Y) = !(Nat.beq X Y) := by
  obtain ⟨-, hS, -, -⟩ := cfacts hc
  have cX := validM_canon hc hX
  have cY := validM_canon hc hY
  by_cases hxy : X = Y
  · subst hxy
    rw [Nat.beq_refl]
    unfold diffMod5
    simp
  · have hb : Nat.beq X Y = false := Bool.eq_false_iff.2 (fun h => hxy (Nat.eq_of_beq_eq_true h))
    rw [hb, Bool.not_false]
    unfold diffMod5
    rw [List.any_eq_true]
    by_contra hne
    apply hxy
    subst hS
    refine canon_ext cX cY fun i hi j hj => ?_
    have h1 := canon_ent cX hi hj
    have h2 := canon_ent cY hi hj
    by_contra hne'
    apply hne
    refine ⟨i, List.mem_range.2 hi, ?_⟩
    rw [List.any_eq_true]
    refine ⟨j, List.mem_range.2 hj, ?_⟩
    rw [unpackL_get hi hj, unpackL_get hi hj, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
    simpa using hne'

theorem runB_succ (p w S d T L H CM RM : Nat) (UG E W : Nat → Nat) (kg c n h cur : Nat) :
    runB p w S d T L H CM RM UG E W kg c (n + 1) h cur =
      runB p w S d T L H CM RM UG E W kg c n (h + 1)
        (foldUp kg (fun k cur => stepB p w S d T L H CM RM UG E W c h k cur) cur) := by
  have e : runB p w S d T L H CM RM UG E W kg c (n + 1) h cur =
      strictN (foldUp kg (fun k cur => stepB p w S d T L H CM RM UG E W c h k cur) cur)
        (fun c' => strictN (Nat.succ h) (fun h' => runB p w S d T L H CM RM UG E W kg c n h' c')) :=
    rfl
  rw [e, strictN_eqP, strictN_eqP]

@[expose] noncomputable def stH (p w S d T L H CM RM : Nat) (UG E W : Nat → Nat) (kg c h cur : Nat) :
    Nat :=
  (List.range kg).foldl (fun s k => stepB p w S d T L H CM RM UG E W c h k s) cur

theorem runB_eq (p w S d T L H CM RM : Nat) (UG E W : Nat → Nat) (kg c : Nat) :
    ∀ n h cur, runB p w S d T L H CM RM UG E W kg c n h cur =
      (List.range' h n).foldl (fun s h => stH p w S d T L H CM RM UG E W kg c h s) cur
  | 0, h, cur => rfl
  | n + 1, h, cur => by
    rw [runB_succ, runB_eq p w S d T L H CM RM UG E W kg c n, foldUp_eqP, List.range'_succ,
      List.foldl_cons]
    rfl

theorem stepB_eq (p w S d T L H CM RM : Nat) (UG E W : Nat → Nat) (c h k cur : Nat) :
    stepB p w S d T L H CM RM UG E W c h k cur =
      if h < cur then
        (if fld(W h, Nat.mul (nat_lit 9) k, nat_lit 511) < cur ∧
            mulR p w S d T L H CM RM (UG k) (E h) = E fld(W h, Nat.mul (nat_lit 9) k, nat_lit 511)
          then cur
        else if fld(W h, Nat.mul (nat_lit 9) k, nat_lit 511) = cur ∧ cur < c ∧
            mulR p w S d T L H CM RM (UG k) (E h) = E cur then cur + 1
        else failC)
      else cur := by
  unfold stepB
  simp only [strictN_eqP, nIf_eqP, bAnd_eqP, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]

theorem failC_val : failC = 1099511627776 := rfl

theorem fld511 (x o : Nat) : fld(x, o, nat_lit 511) ≤ 511 := Nat.and_le_right

theorem stepB_absorb {p w S d T L H CM RM : Nat} {UG E W : Nat → Nat} {c : Nat} (hc : c ≤ 512)
    (h k : Nat) :
    (∀ cur, cur ≤ failC → cur ≤ stepB p w S d T L H CM RM UG E W c h k cur ∧
      stepB p w S d T L H CM RM UG E W c h k cur ≤ failC) ∧
    stepB p w S d T L H CM RM UG E W c h k failC = failC := by
  have hj := fld511 (W h) (Nat.mul 9 k)
  refine ⟨fun cur hcur => ?_, ?_⟩
  · rw [stepB_eq]
    rw [failC_val] at hcur ⊢
    split_ifs <;> omega
  · rw [stepB_eq]
    rw [failC_val]
    split_ifs <;> omega

theorem stH_absorb {p w S d T L H CM RM : Nat} {UG E W : Nat → Nat} {kg c : Nat} (hc : c ≤ 512)
    (h : Nat) :
    (∀ cur, cur ≤ failC → cur ≤ stH p w S d T L H CM RM UG E W kg c h cur ∧
      stH p w S d T L H CM RM UG E W kg c h cur ≤ failC) ∧
    stH p w S d T L H CM RM UG E W kg c h failC = failC := by
  have hf := fold_absorb (fun k s => stepB p w S d T L H CM RM UG E W c h k s) failC
    (fun k => (stepB_absorb hc h k).1) (fun k => (stepB_absorb hc h k).2) (List.range kg)
  refine ⟨fun cur hcur => ⟨(hf cur hcur).1, (hf cur hcur).2.1⟩, ?_⟩
  exact (hf failC (le_refl _)).2.2 rfl

theorem stH_skip {p w S d T L H CM RM : Nat} {UG E W : Nat → Nat} {kg c h cur : Nat}
    (hh : cur ≤ h) : stH p w S d T L H CM RM UG E W kg c h cur = cur := by
  unfold stH
  generalize List.range kg = l
  induction l generalizing cur with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldl_cons, stepB_eq, if_neg (by omega)]
    exact ih hh

theorem range_split (f : Nat → Nat → Nat) (s : Nat) {a b : Nat} (hab : a ≤ b) :
    (List.range b).foldl (fun s x => f x s) s =
      (List.range' a (b - a)).foldl (fun s x => f x s) ((List.range a).foldl (fun s x => f x s) s) := by
  have e : b = a + (b - a) := by omega
  conv_lhs => rw [e, List.range_add, List.foldl_append]
  rw [List.range'_eq_map_range]

theorem mulR_unpack {w S T L H CM RM ONE LV HV X Y : Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true) (hY : validM 5 (111 * S) L H Y = true) :
    mulM 5 111 (unpackL 111 w S X) (unpackL 111 w S Y) =
      unpackL 111 w S (mulR 5 w S 111 T L H CM RM X Y) :=
  (mulR_eqL hc hX hY).1

theorem unpack_inj {w S T L H CM RM ONE LV HV X Y : Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true) (hY : validM 5 (111 * S) L H Y = true)
    (h : unpackL 111 w S X = unpackL 111 w S Y) : X = Y := by
  have e := beq_eqL hc hX hY
  rw [h, beq_self_eq_true] at e
  exact Nat.eq_of_beq_eq_true e.symm

theorem runB_soundL {w S T L H CM RM ONE LV HV kg c cap nS Hh : Nat} {UG E W SO SOI C : Nat → Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hU : ∀ k < kg, validM 5 (111 * S) L H (UG k) = true)
    (hE : ∀ i < c, validM 5 (111 * S) L H (E i) = true) (h0 : E 0 = ONE) (hc512 : c ≤ 512)
    (hsort : ∀ i < c, sortB E SO SOI c i = true)
    (hcap : nS * Hh = cap) (hC0 : C 0 = 1) (hCn : C nS = c)
    (hrun : ∀ q < nS, Nat.beq (runB 5 w S 111 T L H CM RM UG E W kg c Hh (Nat.mul q Hh) (C q))
      (C (Nat.succ q)) = true) {us : Array (Array (Array Nat))}
    (hus : us.size = kg ∧ ∀ k < kg, us[k]! = unpackL 111 w S (UG k)) :
    (sylowBFS us cap).1 =
      Array.ofFn (n := c) fun i => unpackL 111 w S (E i.val) := by
  let sH := fun h s => stH 5 w S 111 T L H CM RM UG E W kg c h s
  let stG := fun t => (List.range t).foldl (fun s h => sH h s) 1
  have hCq : ∀ q ≤ nS, C q = stG (q * Hh) := by
    intro q
    induction q with
    | zero => intro _; rw [hC0, Nat.zero_mul]; rfl
    | succ q ih =>
      intro hq
      have hr := Nat.eq_of_beq_eq_true (hrun q (by omega))
      rw [runB_eq, ih (by omega)] at hr
      rw [← hr]
      have e := range_split (fun h s => sH h s) 1 (a := q * Hh) (b := (q + 1) * Hh)
        (Nat.mul_le_mul_right Hh (Nat.le_succ q))
      have e2 : (q + 1) * Hh - q * Hh = Hh := by rw [Nat.succ_mul]; omega
      rw [e2] at e
      exact e.symm
  have hG : stG cap = c := by
    rw [← hcap, ← hCq nS le_rfl, hCn]
  have hF : c < failC := by rw [failC_val]; omega
  have habs := fun l s hs => fold_absorb (fun h s => sH h s) failC
    (fun h => (stH_absorb hc512 h).1) (fun h => (stH_absorb hc512 h).2) l s hs
  have h1F : (1 : Nat) ≤ failC := by rw [failC_val]; omega
  have hGt : ∀ t ≤ cap, stG t ≤ c ∧ stG t ≠ failC := by
    intro t ht
    have e := range_split (fun h s => sH h s) 1 ht
    have hb := habs (List.range t) 1 h1F
    have ha := habs (List.range' t (cap - t)) (stG t) hb.2.1
    change stG cap = _ at e
    rw [← e, hG] at ha
    exact ⟨ha.1, fun h => absurd (ha.2.2 h) (Nat.ne_of_lt hF)⟩
  have hGs : ∀ t, stG (t + 1) = sH t (stG t) := by
    intro t
    change (List.range (t + 1)).foldl _ 1 = _
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  let stI := fun h k => (List.range k).foldl
    (fun s k => stepB 5 w S 111 T L H CM RM UG E W c h k s) (stG h)
  have hI : ∀ h < cap, ∀ k ≤ kg, stI h k ≤ c ∧ stI h k ≠ failC ∧ stG h ≤ stI h k := by
    intro h hh k hk
    have hgh := hGt h (by omega)
    have hgh1 := hGt (h + 1) (by omega)
    have habsI := fun l s hs => fold_absorb (fun k s => stepB 5 w S 111 T L H CM RM UG E W c h k s)
      failC (fun k => (stepB_absorb hc512 h k).1) (fun k => (stepB_absorb hc512 h k).2) l s hs
    have e := range_split (fun k s => stepB 5 w S 111 T L H CM RM UG E W c h k s) (stG h) hk
    have hb := habsI (List.range k) (stG h) (Nat.le_trans hgh.1 (Nat.le_of_lt hF))
    have ha := habsI (List.range' k (kg - k)) (stI h k) hb.2.1
    have e1 : stG (h + 1) = (List.range' k (kg - k)).foldl
        (fun s x => stepB 5 w S 111 T L H CM RM UG E W c h x s) (stI h k) := by
      rw [hGs]
      exact e
    rw [← e1] at ha
    exact ⟨Nat.le_trans ha.1 hgh1.1, fun hh' => hgh1.2 (ha.2.2 hh'), hb.1⟩
  have hIs : ∀ h k, stI h (k + 1) = stepB 5 w S 111 T L H CM RM UG E W c h k (stI h k) := by
    intro h k
    change (List.range (k + 1)).foldl _ _ = _
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hIk : ∀ h, stI h kg = stG (h + 1) := fun h => (hGs h).symm
  let P := fun i => unpackL 111 w S (E i)
  have hinj := sortB_inj hsort
  have hP : ∀ i < c, ∀ j < c, P i = P j → i = j := fun i hi j hj e =>
    hinj i hi j hj (unpack_inj hc (hE i hi) (hE j hj) e)
  let R : Nat → Std.HashMap Mat Nat × Array Mat × Array Nat × Array Nat × Array (Array Nat) → Prop :=
    fun n s => s.2.1 = (Array.ofFn (n := n) fun i => P i.val) ∧
      ∀ z, (s.1[z]?).isSome = true ↔ ∃ i < n, P i = z
  have hc0 : 0 < c := by
    have := hGt 0 (Nat.zero_le _)
    have h00 : stG 0 = 1 := rfl
    omega
  have hidE : idM 111 = P 0 := by
    change idM 111 = unpackL 111 w S (E 0)
    rw [h0]
    exact (idM_eqL hc).1
  have hmain : ∀ s, R (stG cap) s → s.2.1 = Array.ofFn (n := c) fun i => P i.val := by
    intro s hs
    rw [hs.1, hG]
  refine hmain _ (forIn_range_spec (fun h s => R (stG h) s) cap _ _ ?_ ?_)
  ·
    refine ⟨?_, fun z => ?_⟩
    · change #[idM 111] = Array.ofFn (n := 1) fun i => P i.val
      rw [hidE]
      rfl
    · change ((∅ : Std.HashMap Mat Nat).insert (idM 111) 0)[z]?.isSome = true ↔ ∃ i < 1, P i = z
      rw [Std.HashMap.getElem?_insert]
      constructor
      · intro hz
        by_cases e : (idM 111 == z) = true
        · exact ⟨0, Nat.zero_lt_one, by rw [← hidE]; exact eq_of_beq e⟩
        · rw [if_neg e, Std.HashMap.getElem?_empty] at hz
          exact absurd hz (by decide)
      · rintro ⟨i, hi, hz⟩
        have : i = 0 := by omega
        subst this
        rw [if_pos (by rw [hidE, hz]; exact beq_self_eq_true z)]
        rfl
  ·
    intro h b hh hb
    obtain ⟨hpts, hidx⟩ := hb
    have hgh := hGt h (by omega)
    dsimp only
    split
    · rename_i hlt
      have hlt' : h < stG h := by rw [hpts] at hlt; simpa using hlt
      refine ⟨_, rfl, ?_⟩
      have hx : b.2.1[h]! = P h := by rw [hpts]; exact ofFn_getP P hlt'
      have hfin : ∀ s, R (stI h us.size) s →
          R (stG (h + 1)) (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2) := by
        intro s hs
        rw [hus.1, hIk h] at hs
        exact hs
      refine hfin _ (forIn_range_spec (fun k s => R (stI h k) s) us.size _ _ ⟨hpts, hidx⟩ ?_)
      · intro k s hk hs
        rw [hus.1] at hk
        obtain ⟨hs1, hs2⟩ := hs
        have hIk' := hI h hh k (by omega)
        have hIk1 := hI h hh (k + 1) (by omega)
        have hcur : h < stI h k := Nat.lt_of_lt_of_le hlt' hIk'.2.2
        have hvh : validM 5 (111 * S) L H (E h) = true := hE h (by omega)
        have hy : mulM 5 111 us[k]! b.2.1[h]! =
            unpackL 111 w S (mulR 5 w S 111 T L H CM RM (UG k) (E h)) := by
          rw [hx, hus.2 k hk]
          exact mulR_unpack hc (hU k hk) hvh
        have hstep := hIs h k
        rw [stepB_eq, if_pos hcur] at hstep
        rw [hy]
        split
        ·
          rename_i j hj
          refine ⟨_, rfl, ?_⟩
          have hfound : ∃ i < stI h k, P i = unpackL 111 w S (mulR 5 w S 111 T L H CM RM (UG k) (E h)) :=
            (hs2 _).1 (by rw [hj]; rfl)
          by_cases hA : fld(W h, Nat.mul (nat_lit 9) k, nat_lit 511) < stI h k ∧
              mulR 5 w S 111 T L H CM RM (UG k) (E h) = E fld(W h, Nat.mul (nat_lit 9) k, nat_lit 511)
          · rw [if_pos hA] at hstep
            rw [hstep]
            exact ⟨hs1, hs2⟩
          · rw [if_neg hA] at hstep
            by_cases hB : fld(W h, Nat.mul (nat_lit 9) k, nat_lit 511) = stI h k ∧ stI h k < c ∧
                mulR 5 w S 111 T L H CM RM (UG k) (E h) = E (stI h k)
            · exfalso
              obtain ⟨i, hi, hiz⟩ := hfound
              rw [hB.2.2] at hiz
              have := hP i (by omega) (stI h k) hB.2.1 hiz
              omega
            · rw [if_neg hB] at hstep
              exact absurd hstep hIk1.2.1
        ·
          rename_i hj
          refine ⟨_, rfl, ?_⟩
          have hnot : ¬ ∃ i < stI h k, P i = unpackL 111 w S (mulR 5 w S 111 T L H CM RM (UG k) (E h)) := by
            intro hex
            have := (hs2 _).2 hex
            rw [hj] at this
            exact absurd this (by decide)
          by_cases hA : fld(W h, Nat.mul (nat_lit 9) k, nat_lit 511) < stI h k ∧
              mulR 5 w S 111 T L H CM RM (UG k) (E h) = E fld(W h, Nat.mul (nat_lit 9) k, nat_lit 511)
          · exact absurd ⟨_, hA.1, by rw [hA.2]⟩ hnot
          · rw [if_neg hA] at hstep
            by_cases hB : fld(W h, Nat.mul (nat_lit 9) k, nat_lit 511) = stI h k ∧ stI h k < c ∧
                mulR 5 w S 111 T L H CM RM (UG k) (E h) = E (stI h k)
            · rw [if_pos hB] at hstep
              rw [hstep]
              have hyP : unpackL 111 w S (mulR 5 w S 111 T L H CM RM (UG k) (E h)) = P (stI h k) := by
                rw [hB.2.2]
              refine ⟨?_, fun z => ?_⟩
              · change s.2.1.push _ = _
                rw [hs1, hyP, ofFn_push]
              · change ((s.1.insert _ s.2.1.size)[z]?).isSome = true ↔ _
                rw [Std.HashMap.getElem?_insert]
                by_cases e : (unpackL 111 w S (mulR 5 w S 111 T L H CM RM (UG k) (E h)) == z) = true
                · rw [if_pos e]
                  refine ⟨fun _ => ⟨stI h k, Nat.lt_succ_self _, ?_⟩, fun _ => rfl⟩
                  rw [← hyP]
                  exact eq_of_beq e
                · rw [if_neg e, hs2]
                  constructor
                  · rintro ⟨i, hi, hiz⟩
                    exact ⟨i, by omega, hiz⟩
                  · rintro ⟨i, hi, hiz⟩
                    refine ⟨i, ?_, hiz⟩
                    rcases Nat.lt_or_ge i (stI h k) with h' | h'
                    · exact h'
                    · exfalso
                      have : i = stI h k := by omega
                      subst this
                      apply e
                      rw [hyP, hiz]
                      exact beq_self_eq_true z
            · rw [if_neg hB] at hstep
              exact absurd hstep hIk1.2.1
    · rename_i hge
      refine ⟨_, rfl, ?_⟩
      have hge' : stG h ≤ h := by rw [hpts] at hge; simpa using hge
      rw [hGs]
      change R (stH 5 w S 111 T L H CM RM UG E W kg c h (stG h)) _
      rw [stH_skip hge']
      exact ⟨hpts, hidx⟩

end CFSG.KS.SporSch.LyRB

end
