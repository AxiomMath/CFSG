module

public import Certificates.Data.Kernel.HMathieu.FixTab
public import CFSG.Certificates.Kernel.HMathieu.FixCertSound
public import CFSG.Certificates.Kernel.HMathieu.MatSearch

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

theorem pairwise_of_incB : ∀ l : List Nat, incB l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [incB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_incB (b :: l) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

theorem actK_eq : ∀ (cs : List Nat) (m : Nat), actK cs m = actM cs m
  | [], _ => rfl
  | c :: cs, m => by
    have e : actK (c :: cs) m = Nat.xor (bif Nat.beq (Nat.land m 1) 1 then c else 0)
        (actK cs (Nat.shiftRight m 1)) := rfl
    have hb : (bif Nat.beq (m % 2) 1 then c else 0) = if m % 2 = 1 then c else 0 := by
      cases hq : Nat.beq (m % 2) 1
      · have h : ¬ m % 2 = 1 := by
          rw [← Nat.beq_eq, hq]
          exact Bool.false_ne_true
        simp [h]
      · have h : m % 2 = 1 := by
          rw [← Nat.beq_eq]
          exact hq
        simp [h]
    have h1 : Nat.land m 1 = m % 2 := Nat.and_one_is_mod m
    have h2 : Nat.shiftRight m 1 = m / 2 := by
      have := Nat.shiftRight_eq_div_pow m 1
      simpa using this
    rw [e, actK_eq cs, actM, h1, h2, hb]
    rfl

theorem actK_fun (cs : List Nat) : actK cs = actM cs := funext (actK_eq cs)

theorem fixRow_eq {n : Nat} {M F J : List Nat} (h : fixRowOK n M F J = true) :
    F = (List.range (2 ^ n)).filter fun m => actM M m == m := by
  simp only [fixRowOK, actK_fun, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Nat.beq_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hF, hinc⟩, hJ⟩, hok⟩, hlen⟩ := h
  have hP := pairwise_of_incB F hinc
  have hsub : F ⊆ (List.range (2 ^ n)).filter fun m => actM M m == m := by
    intro x hx
    rw [List.mem_filter, List.mem_range, beq_iff_eq]
    exact hF x hx
  have hle : ((List.range (2 ^ n)).filter fun m => actM M m == m).length ≤ F.length := by
    rw [length_filter_eq_card, hlen]
    exact fix_le_of_imgOK hJ hok
  refine List.Perm.eq_of_pairwise (le := (· < ·)) (fun a b _ _ h1 h2 => absurd (lt_trans h1 h2)
    (lt_irrefl a)) hP (List.pairwise_lt_range.filter _)
    ((List.subperm_of_subset (hP.imp Nat.ne_of_lt) hsub).perm_of_length_le hle)

theorem fixTab_get {n : Nat} : ∀ {Ms Fs Js : List (List Nat)}, fixTabOK n Ms Fs Js = true →
    ∀ i < Ms.length, Fs.getD i [] = (List.range (2 ^ n)).filter fun m => actM (Ms.getD i []) m == m
  | [], [], [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | M :: Ms, F :: Fs, J :: Js, h, i, hi => by
    simp only [fixTabOK, Bool.and_eq_true] at h
    cases i with
    | zero => exact fixRow_eq h.1
    | succ i => exact fixTab_get h.2 i (by simpa using hi)
  | [], [], _ :: _, h, _, _ => by simp [fixTabOK] at h
  | [], _ :: _, _, h, _, _ => by simp [fixTabOK] at h
  | _ :: _, [], _, h, _, _ => by simp [fixTabOK] at h
  | _ :: _, _ :: _, [], h, _, _ => by simp [fixTabOK] at h

variable {P : Type} [Group P] [DecidableEq P]

theorem forallGreedyAll_fixT {R : List P} {D : List (Nat × Nat)}
    (T : GTabs R (cmD D) (mkD D)) (hD : D.length = R.length) {posF : P → Nat}
    (hpos : ∀ x, posF x = R.idxOf x) (M Fs : List (List Nat)) (n : Nat)
    (hFs : ∀ y < R.length, Fs.getD y [] = fixMasks n actM [M.getD y []]) (pred : List P → Bool)
    (predK : List Nat → List Nat → List (List Nat) × List Nat → Bool)
    (hpred : ∀ l, (∀ y ∈ l, y ∈ R) → IndepList l → pred l = predK (l.map R.idxOf)
      ((subprods l).map R.idxOf) (fixSt n (l.map fun x => M.getD (R.idxOf x) []))) (k : Nat)
    (hK : gAllR R.length (fun st y => (M.getD y [] :: st.1, if st.1.isEmpty then Fs.getD y []
        else st.2.filter fun m => actK (M.getD y []) m == m)) predK k [] [R.length]
      (2 ^ R.length - 1) ([], List.range (2 ^ n)) D 0 = true) :
    forallGreedyAll posF R pred k [] = true := by
  simp only [actK_fun] at hK
  rw [forallGreedyAll_eq_gAllS_nil T hpos pred _ predK
    (fun l => fixSt n (l.map fun x => M.getD (R.idxOf x) [])) (fun x l hx _ _ => ?_) hpred k]
  · simp only [List.map_nil, fixSt, fixMasks_nil]
    rw [← gAllR_eq hD _ _ k [] [R.length] _ _ (by simp [startK])]
    exact hK
  · cases l with
    | nil =>
      simp only [fixSt, List.map_cons, List.map_nil, List.isEmpty_nil, if_true]
      rw [hFs _ (List.idxOf_lt_length_iff.2 hx)]
    | cons y l =>
      simp only [fixSt, List.map_cons, List.isEmpty_cons, Bool.false_eq_true, if_false,
        fixMasks_cons']

end CFSG.KC.HMathieu

end
