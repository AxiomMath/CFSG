module

public import CFSG.Certificates.Kernel.Spor.ONVecLib
import CFSG.Certificates.Kernel.ONOut.InvVSound

public section

namespace CFSG.KS.ON

open CFSG.ONSchreier.Native CFSG.Sporadic.Th.Native

@[expose] def dStep (m a q : Nat) (par : Array Nat) : Array Nat :=
  if (decide (a < m) && par[a]! == m) = true then par.set! a q else par

theorem discPar_eq (m : Nat) (α β : Table) : discPar m α β =
    (List.range' 0 m).foldl (fun par q => dStep m (ap β q) q (dStep m (ap α q) q par))
      (Array.replicate m m) := by
  unfold discPar
  simp only [Id.run_bind, Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range',
    CFSG.KS.ONOut.InvV.ite_pure_yield, List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure,
    Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero]
  congr 1
  funext par q
  unfold dStep
  by_cases h1 : (decide (ap α q < m) && par[ap α q]! == m) = true
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]

@[expose] def Hit (α β : Table) (q a : Nat) : Prop := ap α q = a ∨ ap β q = a

@[expose] def ParInv (m : Nat) (α β : Table) (Q : Nat) (par : Array Nat) : Prop :=
  par.size = m ∧ ∀ a < m, (par[a]! = m ∧ ∀ q < Q, ¬ Hit α β q a) ∨
    (par[a]! < Q ∧ Hit α β par[a]! a ∧ ∀ q < par[a]!, ¬ Hit α β q a)

theorem get_set! {par : Array Nat} {j i v : Nat} (hj : j < par.size) :
    (par.set! j v)[i]! = if j = i then v else par[i]! := by
  by_cases e : j = i
  · subst e
    rw [if_pos rfl, Array.getElem!_set!_self _ _ _ hj]
  · rw [if_neg e, Array.getElem!_set!_ne _ _ _ _ e]

theorem size_dStep (m a q : Nat) (par : Array Nat) : (dStep m a q par).size = par.size := by
  unfold dStep
  split <;> simp

theorem dStep_get {m a q : Nat} {par : Array Nat} (hs : par.size = m) {i : Nat} (hi : i < m) :
    (dStep m a q par)[i]! = if a = i ∧ par[i]! = m then q else par[i]! := by
  unfold dStep
  by_cases h : (decide (a < m) && par[a]! == m) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rw [get_set! (by rw [hs]; exact h.1)]
    by_cases e : a = i
    · subst e
      simp [h.2]
    · simp [e]
  · rw [if_neg h]
    by_cases e : a = i ∧ par[i]! = m
    · obtain ⟨rfl, e2⟩ := e
      exact absurd (by simp [hi, e2]) h
    · rw [if_neg e]

theorem parInv_step {m : Nat} {α β : Table} {Q : Nat} {par : Array Nat} (hQ : Q < m)
    (h : ParInv m α β Q par) :
    ParInv m α β (Q + 1) (dStep m (ap β Q) Q (dStep m (ap α Q) Q par)) := by
  obtain ⟨hs, hp⟩ := h
  have hs1 : (dStep m (ap α Q) Q par).size = m := by rw [size_dStep, hs]
  refine ⟨by rw [size_dStep, hs1], fun a ha => ?_⟩
  rw [dStep_get hs1 ha, dStep_get hs ha]
  rcases hp a ha with ⟨e, hn⟩ | ⟨hlt, hh, hl⟩
  · by_cases h1 : ap α Q = a
    · have hq : ¬ Q = m := by omega
      simp only [h1, e, and_self, ite_true, hq, and_false, ite_false]
      exact Or.inr ⟨by omega, Or.inl h1, hn⟩
    · simp only [h1, false_and, ite_false, e, and_true]
      by_cases h2 : ap β Q = a
      · simp only [h2, ite_true]
        exact Or.inr ⟨by omega, Or.inr h2, hn⟩
      · simp only [h2, ite_false]
        refine Or.inl ⟨by first | trivial | exact e, fun q hq hh => ?_⟩
        rcases Nat.lt_or_ge q Q with hq' | hq'
        · exact hn q hq' hh
        · have : q = Q := by omega
          subst this
          rcases hh with hh | hh
          · exact h1 hh
          · exact h2 hh
  · have hne : ¬ par[a]! = m := by omega
    simp only [hne, and_false, ite_false]
    exact Or.inr ⟨by omega, hh, hl⟩

theorem parInv_fold {m : Nat} {α β : Table} :
    ∀ r Q (par : Array Nat), Q + r ≤ m → ParInv m α β Q par →
      ParInv m α β (Q + r) ((List.range' Q r).foldl
        (fun par q => dStep m (ap β q) q (dStep m (ap α q) q par)) par)
  | 0, Q, par, _, h => h
  | r + 1, Q, par, hr, h => by
    have e : Q + (r + 1) = Q + 1 + r := by omega
    rw [List.range'_succ, List.foldl_cons, e]
    exact parInv_fold r (Q + 1) _ (by omega) (parInv_step (by omega) h)

theorem discPar_spec (m : Nat) (α β : Table) : ParInv m α β m (discPar m α β) := by
  rw [discPar_eq]
  have h0 : ParInv m α β 0 (Array.replicate m m) := by
    refine ⟨by simp, fun a ha => Or.inl ⟨?_, fun q hq => absurd hq (Nat.not_lt_zero _)⟩⟩
    rw [getElem!_pos _ a (by simpa using ha)]
    simp
  have := parInv_fold (α := α) (β := β) m 0 _ (by omega) h0
  rwa [Nat.zero_add] at this

theorem discOK_of_hits {m : Nat} {α β : Table}
    (hw : ∀ k, 0 < k → k < m → ∃ q < k, ap α q = k ∨ ap β q = k) :
    discOK m α β (discPar m α β) = true := by
  obtain ⟨-, hp⟩ := discPar_spec m α β
  unfold discOK allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro ⟨k', hk'⟩ _
  dsimp only
  have hk1 : 0 < 1 + k' := by omega
  have hk2 : 1 + k' < m := by omega
  generalize 1 + k' = k at hk1 hk2 ⊢
  obtain ⟨q, hq, hh⟩ := hw k hk1 hk2
  rcases hp k hk2 with ⟨-, hn⟩ | ⟨-, hh', hl⟩
  · exact absurd hh (hn q (by omega))
  · have hle : (discPar m α β)[k]! ≤ q := by
      rcases Nat.lt_or_ge q (discPar m α β)[k]! with hlt | hge
      · exact absurd hh (hl q hlt)
      · exact hge
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
    exact ⟨by omega, hh'⟩

theorem hits_of_ordRun {A B NX : Nat → Nat} {n SL NS : Nat} (hn : 0 < n) (hNS : NS * SL = n)
    (hX0 : NX 0 = 1) (hXN : NX NS = n)
    (hord : ∀ s < NS, Nat.beq (ordRun A B (s * SL) SL (NX s)) (NX (s + 1)) = true) :
    ∀ k, 0 < k → k < n → ∃ q < k, tab A q = k ∨ tab B q = k := by
  obtain ⟨htot, hcnt⟩ := ordRun_facts hn hNS hX0 hXN hord
  intro k hk1 hk2
  have hex : ∃ h, k < ordRun A B 0 (h + 1) 1 ∧ h < n := by
    have e : n - 1 + 1 = n := by omega
    refine ⟨n - 1, ?_, by omega⟩
    rw [e, htot]
    exact hk2
  classical
  obtain ⟨h, ⟨hk, hh⟩, hmin⟩ : ∃ h, (k < ordRun A B 0 (h + 1) 1 ∧ h < n) ∧
      ∀ h' < h, ¬ (k < ordRun A B 0 (h' + 1) 1 ∧ h' < n) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun _ hlt => Nat.find_min hex hlt⟩
  have hlow : ordRun A B 0 h 1 ≤ k := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · rw [h0]
      exact hk1
    · have e1 : h - 1 < h := by omega
      have e2 : h - 1 + 1 = h := by omega
      have hm := hmin (h - 1) e1
      rw [e2] at hm
      have : ¬ k < ordRun A B 0 h 1 := fun hk' => hm ⟨hk', by omega⟩
      omega
  obtain ⟨hlt, -, hstep, hnz, -⟩ := hcnt h hh
  refine ⟨h, by omega, ?_⟩
  rw [hstep] at hk
  generalize ordRun A B 0 h 1 = s at hlt hlow hk hnz
  rw [ordStep_eq, if_pos hlt] at hk hnz
  have h1 : ordImg (tab A h) s ≠ 0 := fun e => by
    rw [if_pos e] at hnz
    exact hnz rfl
  rw [if_neg h1] at hk hnz
  obtain ⟨ha1, -, ha3, ha4⟩ := ordImg_ne h1
  obtain ⟨hb1, -, hb3, hb4⟩ := ordImg_ne hnz
  rcases Nat.lt_or_eq_of_le ha1 with ha | ha
  · have e1 := ha4 ha
    rw [e1] at hb1 hb3 hb4 hk
    rcases Nat.lt_or_eq_of_le hb1 with hb | hb
    · rw [hb4 hb] at hk
      omega
    · exact Or.inr (by omega)
  · have e1 := ha3 ha
    rw [e1] at hb1 hb3 hb4 hk
    rcases Nat.lt_or_eq_of_le hb1 with hb | hb
    · rw [hb4 hb] at hk
      exact Or.inl (by omega)
    · rw [hb3 hb] at hk
      by_cases e : k = s
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)

end CFSG.KS.ON

end
