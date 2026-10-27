module

public import Certificates.Data.Kernel.SporSch.Closure
public import CFSG.Sporadic.Schreier.Co3SecondImageCheckInputs
import all CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Fi22LH.Loops
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Co3
open CFSG.Monster.B.Co2.Native

private def ckInner (n bound : Nat) (gs : Array (Array Nat)) (head : Nat) (e : Array Nat)
    (k : Nat) (s : Array (Array Nat) × Array Nat × Array Nat) :
    Id (ForInStep (Array (Array Nat) × Array Nat × Array Nat)) :=
  if (decide (s.1.size < bound) && !s.1.any fun x => eqA n x (compA n gs[k]! e)) = true then
    pure (ForInStep.yield (s.1.push (compA n gs[k]! e), s.2.1.push head, s.2.2.push k))
  else pure (ForInStep.yield s)

private def ckOuter (n bound : Nat) (gs : Array (Array Nat)) (_ : Nat)
    (s : Array (Array Nat) × Array Nat × Array Nat × Nat) :
    Id (ForInStep (Array (Array Nat) × Array Nat × Array Nat × Nat)) :=
  if (decide (s.2.2.2 < s.1.size) && decide (s.1.size < bound)) = true then
    have r : Array (Array Nat) × Array Nat × Array Nat :=
      forIn (m := Id) [:gs.size] (s.1, s.2.1, s.2.2.1) (ckInner n bound gs s.2.2.2 s.1[s.2.2.2]!)
    pure (ForInStep.yield (r.1, r.2.1, r.2.2, s.2.2.2 + 1))
  else pure (ForInStep.yield s)

private theorem closureK_search_eq (n bound : Nat) (gs : Array (Array Nat)) :
    co3PermClosure n gs bound =
      (have s : Array (Array Nat) × Array Nat × Array Nat × Nat :=
        forIn (m := Id) [:bound] (#[idA n], #[0], #[0], 0) (ckOuter n bound gs)
      (s.1, s.2.1, s.2.2.1)) := rfl

private theorem closureK_firstIdx_eq (c : Nat) (f : Nat → Bool) :
    firstIdx c f = (List.range c).foldr (fun i s => if f i = true then i else s) c := by
  unfold firstIdx
  rw [Raw.Orb.foldN_eq]
  simp only [Raw.Orb.nIf_eq]

private theorem closureK_foldr_least (f : Nat → Bool) (k : Nat) : ∀ d : Nat,
    (∃ i, (i < k ∧ f i = true ∧ ∀ j < i, f j = false) ∧
      (List.range k).foldr (fun i s => if f i = true then i else s) d = i) ∨
    ((∀ i < k, f i = false) ∧
      (List.range k).foldr (fun i s => if f i = true then i else s) d = d) := by
  induction k with
  | zero => intro d; exact Or.inr ⟨fun i hi => absurd hi (Nat.not_lt_zero i), rfl⟩
  | succ k ih =>
    intro d
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]
    rcases ih (if f k = true then k else d) with ⟨i, ⟨hi1, hi2, hi3⟩, hi4⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨i, ⟨by omega, hi2, hi3⟩, hi4⟩
    · by_cases hfk : f k = true
      · rw [if_pos hfk] at h2 ⊢
        exact Or.inl ⟨k, ⟨Nat.lt_succ_self k, hfk, h1⟩, h2⟩
      · rw [if_neg hfk] at h2 ⊢
        refine Or.inr ⟨fun i hi => ?_, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact h1 i hi
        · subst hi
          simpa using hfk

private theorem closureK_firstIdx_spec (c : Nat) (f : Nat → Bool) :
    (firstIdx c f < c ∧ f (firstIdx c f) = true ∧ ∀ j < firstIdx c f, f j = false) ∨
      (firstIdx c f = c ∧ ∀ j < c, f j = false) := by
  rw [closureK_firstIdx_eq]
  rcases closureK_foldr_least f c c with ⟨i, ⟨h1, h2, h3⟩, h4⟩ | ⟨h1, h2⟩
  · rw [h4]
    exact Or.inl ⟨h1, h2, h3⟩
  · exact Or.inr ⟨h2, h1⟩

private theorem closureK_stepC_cases {n w m c PP LP h k x tp r : Nat} {G E : Nat → Nat}
    (htp : pcomp n w m (G k) (E h) = tp) (hr : stepC n w m G E c PP LP h k x = r)
    (hrc : r ≤ c) (hc : c < 1099511627776) :
    h < x ∧ ((∃ j < x, E j = tp ∧ r = x) ∨
      (x < c ∧ E x = tp ∧ (∀ i < x, E i ≠ tp) ∧
        Nat.land (Nat.shiftRight PP (16 * x)) 65535 = h ∧
        Nat.land (Nat.shiftRight LP (8 * x)) 255 = k ∧ r = x + 1)) := by
  have hF : failC = 1099511627776 := rfl
  unfold stepC at hr
  simp only [Raw.Orb.nIf_eq, Raw.Orb.strictN_eq, Raw.Orb.bAnd_eq, htp] at hr
  by_cases hhx : h < x
  · refine ⟨hhx, ?_⟩
    rw [if_pos (by simpa using hhx)] at hr
    have hspec := closureK_firstIdx_spec c (fun j => Nat.beq (E j) tp)
    generalize firstIdx c (fun j => Nat.beq (E j) tp) = j at hr hspec
    by_cases hjx : j < x
    · rw [if_pos (by simpa using hjx)] at hr
      subst hr
      refine Or.inl ⟨j, hjx, ?_, rfl⟩
      rcases hspec with ⟨-, h2, -⟩ | ⟨h1, -⟩
      · exact Nat.eq_of_beq_eq_true h2
      · omega
    · rw [if_neg (by simpa using hjx)] at hr
      by_cases hcond : (j.beq x && (((PP.shiftRight (Nat.mul 16 x)).land 65535).beq h &&
          ((LP.shiftRight (Nat.mul 8 x)).land 255).beq k)) = true
      · rw [if_pos hcond] at hr
        simp only [Bool.and_eq_true, Nat.beq_eq] at hcond
        obtain ⟨rfl, hP, hL⟩ := hcond
        subst hr
        rcases hspec with ⟨h1, h2, h3⟩ | ⟨h1, -⟩
        · refine Or.inr ⟨by omega, Nat.eq_of_beq_eq_true h2, fun i hi he => ?_, hP, hL, rfl⟩
          have h4 := h3 i hi
          simp only [he, Nat.beq_refl] at h4
          exact Bool.noConfusion h4
        · omega
      · rw [if_neg hcond, hF] at hr
        omega
  · rw [if_neg (by simpa using hhx), hF] at hr
    omega

private theorem closureK_stepC_mono {n w m c PP LP h k x : Nat} {G E : Nat → Nat}
    (hc : c < 1099511627776) (hx : x ≤ 1099511627776) :
    x ≤ stepC n w m G E c PP LP h k x ∧ stepC n w m G E c PP LP h k x ≤ 1099511627776 := by
  have hF : failC = 1099511627776 := rfl
  unfold stepC
  simp only [Raw.Orb.nIf_eq, Raw.Orb.strictN_eq, Raw.Orb.bAnd_eq]
  by_cases hhx : h < x
  · rw [if_pos (by simpa using hhx)]
    have hspec := closureK_firstIdx_spec c (fun j => Nat.beq (E j) (pcomp n w m (G k) (E h)))
    generalize firstIdx c (fun j => Nat.beq (E j) (pcomp n w m (G k) (E h))) = j at hspec ⊢
    have hjc : j ≤ c := by rcases hspec with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    by_cases hjx : j < x
    · rw [if_pos (by simpa using hjx)]
      exact ⟨le_rfl, hx⟩
    · rw [if_neg (by simpa using hjx)]
      split
      · omega
      · rw [hF]
        omega
  · rw [if_neg (by simpa using hhx), hF]
    omega

private def ckIn (f : Nat → Nat → Nat) (k x : Nat) : Nat :=
  (List.range k).foldl (fun s j => f j s) x

private def ckOut (f : Nat → Nat → Nat → Nat) (kg q : Nat) : Nat :=
  (List.range q).foldl (fun s h => ckIn (f h) kg s) 1

private theorem closureK_in_succ (f : Nat → Nat → Nat) (k x : Nat) :
    ckIn f (k + 1) x = f k (ckIn f k x) := by
  simp [ckIn, List.range_succ, List.foldl_append]

private theorem closureK_out_succ (f : Nat → Nat → Nat → Nat) (kg q : Nat) :
    ckOut f kg (q + 1) = ckIn (f q) kg (ckOut f kg q) := by
  simp [ckOut, List.range_succ, List.foldl_append]

private theorem closureK_in_mono (f : Nat → Nat → Nat) (F : Nat)
    (hf : ∀ k x, x ≤ F → x ≤ f k x ∧ f k x ≤ F) :
    ∀ k x, x ≤ F → x ≤ ckIn f k x ∧ ckIn f k x ≤ F
  | 0, x, hx => ⟨le_rfl, hx⟩
  | k + 1, x, hx => by
    rw [closureK_in_succ]
    obtain ⟨h1, h2⟩ := closureK_in_mono f F hf k x hx
    obtain ⟨h3, h4⟩ := hf k _ h2
    exact ⟨Nat.le_trans h1 h3, h4⟩

private theorem closureK_in_le_add (f : Nat → Nat → Nat) (F : Nat)
    (hf : ∀ k x, x ≤ F → x ≤ f k x ∧ f k x ≤ F) (k x : Nat) (hx : x ≤ F) :
    ∀ d, ckIn f k x ≤ ckIn f (k + d) x
  | 0 => Nat.le_refl _
  | d + 1 => by
    rw [← Nat.add_assoc, closureK_in_succ]
    exact Nat.le_trans (closureK_in_le_add f F hf k x hx d)
      (hf (k + d) _ (closureK_in_mono f F hf (k + d) x hx).2).1

private theorem closureK_out_mono (f : Nat → Nat → Nat → Nat) (F kg : Nat) (h1 : 1 ≤ F)
    (hf : ∀ h k x, x ≤ F → x ≤ f h k x ∧ f h k x ≤ F) :
    ∀ q, ckOut f kg q ≤ F
  | 0 => h1
  | q + 1 => by
    rw [closureK_out_succ]
    exact (closureK_in_mono (f q) F (hf q) kg _ (closureK_out_mono f F kg h1 hf q)).2

private theorem closureK_out_le_add (f : Nat → Nat → Nat → Nat) (F kg : Nat) (h1 : 1 ≤ F)
    (hf : ∀ h k x, x ≤ F → x ≤ f h k x ∧ f h k x ≤ F) (q : Nat) :
    ∀ d, ckOut f kg q ≤ ckOut f kg (q + d)
  | 0 => Nat.le_refl _
  | d + 1 => by
    rw [← Nat.add_assoc, closureK_out_succ]
    exact Nat.le_trans (closureK_out_le_add f F kg h1 hf q d)
      (closureK_in_mono (f (q + d)) F (hf (q + d)) kg _ (closureK_out_mono f F kg h1 hf (q + d))).1

private noncomputable def ckState (n w PP LP : Nat) (E : Nat → Nat) (m : Nat) :
    Array (Array Nat) × Array Nat × Array Nat :=
  (Array.ofFn (n := m) fun i => unpack n w (E i.val),
    Array.ofFn (n := m) fun i => Nat.land (Nat.shiftRight PP (16 * i.val)) 65535,
    Array.ofFn (n := m) fun i => Nat.land (Nat.shiftRight LP (8 * i.val)) 255)

private theorem closureK_state_size (n w PP LP : Nat) (E : Nat → Nat) (m : Nat) :
    (ckState n w PP LP E m).1.size = m := by
  simp [ckState]

private theorem closureK_state_get (n w PP LP : Nat) (E : Nat → Nat) {m i : Nat} (hi : i < m) :
    (ckState n w PP LP E m).1[i]! = unpack n w (E i) := by
  rw [getElem!_pos _ i (by simpa [ckState] using hi)]
  simp [ckState]

private theorem closureK_state_succ (n w PP LP : Nat) (E : Nat → Nat) (m : Nat) :
    ckState n w PP LP E (m + 1) =
      ((ckState n w PP LP E m).1.push (unpack n w (E m)),
        (ckState n w PP LP E m).2.1.push (Nat.land (Nat.shiftRight PP (16 * m)) 65535),
        (ckState n w PP LP E m).2.2.push (Nat.land (Nat.shiftRight LP (8 * m)) 255)) := by
  simp only [ckState]
  rw [Array.ofFn_succ, Array.ofFn_succ (f := fun i : Fin (m + 1) =>
      Nat.land (Nat.shiftRight PP (16 * i.val)) 65535),
    Array.ofFn_succ (f := fun i : Fin (m + 1) => Nat.land (Nat.shiftRight LP (8 * i.val)) 255)]
  rfl

private theorem closureK_inner_step {n w PP LP bound c h k x r : Nat} {G E : Nat → Nat}
    {gs : Array (Array Nat)} (hn : n < 2 ^ 32) (hw : 0 < w)
    (hE : ∀ i < c, CFSG.KS.Prim.canonK n w (mask w) (n * w) (E i) = true)
    (hgk : gs[k]! = unpack n w (G k)) (hcb : c < bound) (hc : c < 1099511627776) (hx : x ≤ c)
    (hr : stepC n w (mask w) G E c PP LP h k x = r) (hrc : r ≤ c) :
    ckInner n bound gs h (unpack n w (E h)) k (ckState n w PP LP E x) =
      pure (ForInStep.yield (ckState n w PP LP E r)) := by
  obtain ⟨hhx, hcase⟩ := closureK_stepC_cases rfl hr hrc hc
  have hEh := hE h (by omega)
  obtain ⟨-, -, -, hEh4⟩ := CFSG.KS.Prim.canon_facts hEh
  have ht : compA n gs[k]! (unpack n w (E h)) =
      unpack n w (pcomp n w (mask w) (G k) (E h)) := by
    rw [hgk]
    exact CFSG.KS.Prim.compA_unpack hn hEh4
  have hsz := closureK_state_size n w PP LP E x
  unfold ckInner
  rw [ht]
  rcases hcase with ⟨j, hjx, hEj, hrx⟩ | ⟨hxc, hEx, hne, hP, hL, hrx⟩
  · rw [hrx]
    have hj' : j < (ckState n w PP LP E x).1.size := by
      rw [hsz]
      exact hjx
    have hany : ((ckState n w PP LP E x).1.any fun y =>
        eqA n y (unpack n w (pcomp n w (mask w) (G k) (E h)))) = true := by
      rw [Array.any_eq_true]
      refine ⟨j, hj', ?_⟩
      rw [← getElem!_pos _ j hj', closureK_state_get n w PP LP E hjx, hEj]
      exact CFSG.KS.Prim.eqA_self n _
    simp [hany]
  · rw [hrx]
    have hEi : ∀ i < x, E i >>> (n * w) = 0 := fun i hi =>
      (CFSG.KS.Prim.canon_facts (hE i (by omega))).2.2.1
    have hq : pcomp n w (mask w) (G k) (E h) >>> (n * w) = 0 :=
      CFSG.KS.PackFld.pcomp_shr hn hw
    have hany : ((ckState n w PP LP E x).1.any fun y =>
        eqA n y (unpack n w (pcomp n w (mask w) (G k) (E h)))) = false := by
      rw [Array.any_eq_false]
      intro i hi
      have hi' : i < x := by rwa [hsz] at hi
      rw [← getElem!_pos _ i hi, closureK_state_get n w PP LP E hi',
        CFSG.KS.Prim.eqA_false hw (hEi i hi') hq (hne i hi')]
      simp
    have hxb : x < bound := by omega
    have hcond : (decide ((ckState n w PP LP E x).1.size < bound) &&
        !(ckState n w PP LP E x).1.any fun y =>
          eqA n y (unpack n w (pcomp n w (mask w) (G k) (E h)))) = true := by
      rw [hany, hsz]
      simp [hxb]
    rw [if_pos hcond, closureK_state_succ, hP, hL, hEx]

private noncomputable def ckStep (n w : Nat) (G E : Nat → Nat) (c PP LP h k x : Nat) : Nat :=
  stepC n w (mask w) G E c PP LP h k x

private theorem closureK_inner_loop {n w PP LP bound c kg h x0 : Nat} {G E : Nat → Nat}
    {gs : Array (Array Nat)} (hn : n < 2 ^ 32) (hw : 0 < w)
    (hE : ∀ i < c, CFSG.KS.Prim.canonK n w (mask w) (n * w) (E i) = true)
    (hgs : gs.size = kg) (hg : ∀ k < kg, gs[k]! = unpack n w (G k))
    (hcb : c < bound) (hc : c < 1099511627776)
    (hmono : ∀ k ≤ kg, ckIn (ckStep n w G E c PP LP h) k x0 ≤ c) :
    forIn (m := Id) [:gs.size] (ckState n w PP LP E x0)
        (ckInner n bound gs h (unpack n w (E h))) =
      ckState n w PP LP E (ckIn (ckStep n w G E c PP LP h) kg x0) := by
  refine CFSG.KS.Fi22LH.range_loop
    (fun k b => b = ckState n w PP LP E (ckIn (ckStep n w G E c PP LP h) k x0))
    (fun b => b = ckState n w PP LP E (ckIn (ckStep n w G E c PP LP h) kg x0)) _ gs.size _
    ?_ ?_ rfl
  · intro q b hq hb
    subst hb
    have hqk : q < kg := hgs ▸ hq
    have hr : stepC n w (mask w) G E c PP LP h q (ckIn (ckStep n w G E c PP LP h) q x0) =
        ckIn (ckStep n w G E c PP LP h) (q + 1) x0 := (closureK_in_succ _ q x0).symm
    rw [closureK_inner_step hn hw hE (hg q hqk) hcb hc (hmono q hqk.le) hr (hmono (q + 1) hqk)]
    rfl
  · intro b hb
    rwa [hgs] at hb

private def ckFull (st : Array (Array Nat) × Array Nat × Array Nat) (hd : Nat) :
    Array (Array Nat) × Array Nat × Array Nat × Nat :=
  (st.1, st.2.1, st.2.2, hd)

private theorem closureK_outer_loop {n w PP LP bound c kg : Nat} {G E : Nat → Nat}
    {gs : Array (Array Nat)} (hn : n < 2 ^ 32) (hw : 0 < w)
    (hE : ∀ i < c, CFSG.KS.Prim.canonK n w (mask w) (n * w) (E i) = true)
    (hgs : gs.size = kg) (hg : ∀ k < kg, gs[k]! = unpack n w (G k))
    (hcb : c < bound) (hc : c < 1099511627776)
    (hfin : ckOut (ckStep n w G E c PP LP) kg c = c)
    (hinit : ckState n w PP LP E 1 = (#[idA n], #[0], #[0])) :
    forIn (m := Id) [:bound] (#[idA n], #[0], #[0], 0) (ckOuter n bound gs) =
      ckFull (ckState n w PP LP E c) c := by
  have hF1 : ∀ h k x, x ≤ 1099511627776 → x ≤ ckStep n w G E c PP LP h k x ∧
      ckStep n w G E c PP LP h k x ≤ 1099511627776 := fun h k x hx => closureK_stepC_mono hc hx
  have hout : ∀ q, q ≤ c → ckOut (ckStep n w G E c PP LP) kg q ≤ c := by
    intro q hq
    have := closureK_out_le_add (ckStep n w G E c PP LP) 1099511627776 kg (by norm_num) hF1 q
      (c - q)
    rw [Nat.add_sub_cancel' hq, hfin] at this
    exact this
  have hin : ∀ q < c, ∀ k ≤ kg, ckIn (ckStep n w G E c PP LP q) k
      (ckOut (ckStep n w G E c PP LP) kg q) ≤ c := by
    intro q hq k hk
    have hx := closureK_out_mono (ckStep n w G E c PP LP) 1099511627776 kg (by norm_num) hF1 q
    have := closureK_in_le_add (ckStep n w G E c PP LP q) 1099511627776 (hF1 q) k _ hx (kg - k)
    rw [Nat.add_sub_cancel' hk, ← closureK_out_succ] at this
    exact Nat.le_trans this (hout (q + 1) hq)
  have hlt : ∀ q < c, q < ckOut (ckStep n w G E c PP LP) kg q := by
    intro q hq
    rcases Nat.eq_zero_or_pos kg with hkg | hkg
    · subst hkg
      have h1 : ∀ q', ckOut (ckStep n w G E c PP LP) 0 q' = 1 := by
        intro q'
        induction q' with
        | zero => rfl
        | succ q' ih => rw [closureK_out_succ, ih]; rfl
      rw [h1] at hfin ⊢
      omega
    · have hr : stepC n w (mask w) G E c PP LP q 0 (ckOut (ckStep n w G E c PP LP) kg q) =
          ckIn (ckStep n w G E c PP LP q) 1 (ckOut (ckStep n w G E c PP LP) kg q) :=
        (closureK_in_succ _ 0 _).symm
      exact (closureK_stepC_cases rfl hr (hin q hq 1 hkg) hc).1
  refine CFSG.KS.Fi22LH.range_loop
    (fun q b => b = ckFull (ckState n w PP LP E
      (ckOut (ckStep n w G E c PP LP) kg (min q c))) (min q c))
    (fun b => b = ckFull (ckState n w PP LP E c) c) _ bound _ ?_ ?_ ?_
  · intro q b hq hb
    subst hb
    by_cases hqc : q < c
    · rw [Nat.min_eq_left hqc.le]
      have hq1 : min (q + 1) c = q + 1 := Nat.min_eq_left hqc
      have hhd := hlt q hqc
      have hle := hout q hqc.le
      have hinner := closureK_inner_loop hn hw hE hgs hg hcb hc (h := q) (hin q hqc)
      have hcond : (decide (q < (ckState n w PP LP E
          (ckOut (ckStep n w G E c PP LP) kg q)).1.size) &&
          decide ((ckState n w PP LP E (ckOut (ckStep n w G E c PP LP) kg q)).1.size <
            bound)) = true := by
        rw [closureK_state_size]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      have key : ckOuter n bound gs q (ckFull (ckState n w PP LP E
          (ckOut (ckStep n w G E c PP LP) kg q)) q) =
          pure (ForInStep.yield (ckFull (ckState n w PP LP E
            (ckOut (ckStep n w G E c PP LP) kg (q + 1))) (q + 1))) := by
        unfold ckOuter ckFull
        dsimp only
        rw [if_pos hcond, closureK_state_get n w PP LP E hhd]
        simp only [Prod.mk.eta]
        rw [hinner, closureK_out_succ]
      rw [key, hq1]
      rfl
    · have hqc' : c ≤ q := Nat.le_of_not_lt hqc
      have hq1 : min (q + 1) c = c := Nat.min_eq_right (by omega)
      rw [Nat.min_eq_right hqc', hfin]
      have key : ckOuter n bound gs q (ckFull (ckState n w PP LP E c) c) =
          pure (ForInStep.yield (ckFull (ckState n w PP LP E c) c)) := by
        unfold ckOuter ckFull
        dsimp only
        rw [if_neg (by rw [closureK_state_size]; simp)]
      rw [key, hq1, hfin]
      rfl
  · intro b hb
    rw [Nat.min_eq_right hcb.le, hfin] at hb
    exact hb
  · rw [Nat.zero_min]
    show _ = ckFull (ckState n w PP LP E (ckOut (ckStep n w G E c PP LP) kg 0)) 0
    have : ckOut (ckStep n w G E c PP LP) kg 0 = 1 := rfl
    rw [this, hinit]
    rfl

theorem closureK_sound {n w kg c PP LP bound : Nat} {G E : Nat → Nat} {gs : Array (Array Nat)}
    (hg : gs.size = kg ∧ ∀ k < kg, gs[k]! = unpack n w (G k))
    (h : closureK n w G kg E c PP LP bound = true) :
    co3PermClosure n gs bound = (Array.ofFn (n := c) fun i => unpack n w (E i.val),
      Array.ofFn (n := c) fun i => Nat.land (Nat.shiftRight PP (16 * i.val)) 65535,
      Array.ofFn (n := c) fun i => Nat.land (Nat.shiftRight LP (8 * i.val)) 255) := by
  obtain ⟨hgs, hg⟩ := hg
  unfold closureK at h
  simp only [bAnd_iff] at h
  obtain ⟨hsz, hcb, -, -, hc65, hE0, hP0, hL0, -, hEc, hfold⟩ := h
  obtain ⟨hn16, hw'⟩ := CFSG.KS.Prim.szOK_facts hsz
  have hw : 0 < w := CFSG.KS.Prim.w_pos hw'
  have hn : n < 2 ^ 32 := by
    have : (2 : Nat) ^ 32 = 4294967296 := by norm_num
    omega
  have hE : ∀ i < c, CFSG.KS.Prim.canonK n w (mask w) (n * w) (E i) = true :=
    fun i hi => allN_spec hEc i hi
  have hcb' : c < bound := by simpa using hcb
  have hc' : c < 1099511627776 := by
    have : c < 65536 := by simpa using hc65
    omega
  have hfin : ckOut (ckStep n w G E c PP LP) kg c = c := by
    have := Nat.eq_of_beq_eq_true hfold
    simp only [Raw.Orb.foldUp_eq] at this
    exact this
  have hinit : ckState n w PP LP E 1 = (#[idA n], #[0], #[0]) := by
    have e0 : E 0 = pidn n w := Nat.eq_of_beq_eq_true hE0
    have hp0 : Nat.land PP 65535 = 0 := Nat.eq_of_beq_eq_true hP0
    have hl0 : Nat.land LP 255 = 0 := Nat.eq_of_beq_eq_true hL0
    show ckState n w PP LP E (0 + 1) = _
    rw [closureK_state_succ, e0, CFSG.KS.Prim.unpack_pidn hn16 hw']
    simp [ckState]
    exact ⟨hp0, hl0⟩
  rw [closureK_search_eq, closureK_outer_loop hn hw hE hgs hg hcb' hc' hfin hinit]
  rfl

end CFSG.KS.SporSch

end
