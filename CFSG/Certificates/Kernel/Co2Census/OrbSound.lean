module

public import Certificates.Data.Kernel.Co2Census.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CFSG.Certificates.Kernel.Co2InvS.Mat

public section

namespace CFSG.KC.Co2Census

open CFSG.KC.Co2InvS CFSG.KC.Loop

@[expose] def StepRel (step : Nat → Nat → Nat) (ngen : Nat) (x y : Nat) : Prop :=
  ∃ l < ngen, y = step l x

theorem treeK_sound {step : Nat → Nat → Nat} {ngen N : Nat} {P IX : Nat → Nat}
    (h : ∀ i < N, treeK step ngen N P IX i = true) :
    (∀ i < N, rtOf IX i < N ∧ rtOf IX (rtOf IX i) = rtOf IX i ∧
      Relation.ReflTransGen (StepRel step ngen) (P (rtOf IX i)) (P i)) ∧
    ∀ i < N, ∀ j < N, P i = P j → i = j := by
  have hs : ∀ i < N, rtOf IX i < N ∧ rtOf IX (rtOf IX i) = rtOf IX i ∧
      (rtOf IX i = i ∨ (fld20 (IX i) 1 < i ∧ rtOf IX (fld20 (IX i) 1) = rtOf IX i ∧
        fld20 (IX i) 2 < ngen ∧ P i = step (fld20 (IX i) 2) (P (fld20 (IX i) 1)))) ∧
      fld20 (IX i) 3 < N ∧ (i + 1 < N → P (fld20 (IX i) 3) < P (fld20 (IX (i + 1)) 3)) := by
    intro i hi
    have hc := h i hi
    unfold treeK at hc
    simp only [letB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq,
      Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩ := hc
    refine ⟨h1, h2, ?_, h4, fun hlt => ?_⟩
    · rcases h3 with h3 | ⟨⟨⟨h3, h3'⟩, h3''⟩, h3'''⟩
      · exact Or.inl h3
      · exact Or.inr ⟨h3, h3', h3'', h3'''⟩
    · rcases h5 with h5 | h5
      · have hb : Nat.blt (i + 1) N = true := Nat.blt_eq.mpr hlt
        rw [hb] at h5
        exact absurd h5 (by decide)
      · exact h5
  have hreach : ∀ i, i < N → Relation.ReflTransGen (StepRel step ngen) (P (rtOf IX i)) (P i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      obtain ⟨-, -, hpar, -, -⟩ := hs i hi
      rcases hpar with he | ⟨hpa, hrt, hla, hP⟩
      · exact (congrArg (fun x => Relation.ReflTransGen (StepRel step ngen) (P x) (P i)) he).mpr
          Relation.ReflTransGen.refl
      · have hr := ih _ hpa (by omega)
        rw [hrt] at hr
        exact hr.tail ⟨_, hla, hP⟩
  have hmono : ∀ a b, a < b → b < N → P (fld20 (IX a) 3) < P (fld20 (IX b) 3) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      have hstep := (hs b (by omega)).2.2.2.2 hb
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
      · exact lt_trans (ih h' (by omega)) hstep
      · rw [h']
        exact hstep
  have hinj : ∀ a < N, ∀ b < N, fld20 (IX a) 3 = fld20 (IX b) 3 → a = b := by
    intro a ha b hb e
    rcases lt_trichotomy a b with h' | h' | h'
    · exact absurd (congrArg P e) (ne_of_lt (hmono a b h' hb))
    · exact h'
    · exact absurd (congrArg P e).symm (ne_of_lt (hmono b a h' ha))
  have himg : (Finset.range N).image (fun a => fld20 (IX a) 3) = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (hs a (Finset.mem_range.1 ha)).2.2.2.1
    · exact (Finset.card_image_of_injOn fun a ha b hb e =>
        hinj a (Finset.mem_range.1 (Finset.mem_coe.1 ha)) b
          (Finset.mem_range.1 (Finset.mem_coe.1 hb)) e).ge
  have hsurj : ∀ i < N, ∃ a < N, fld20 (IX a) 3 = i := by
    intro i hi
    have hm : i ∈ (Finset.range N).image (fun a => fld20 (IX a) 3) := by
      rw [himg]
      exact Finset.mem_range.2 hi
    obtain ⟨a, ha, e⟩ := Finset.mem_image.1 hm
    exact ⟨a, Finset.mem_range.1 ha, e⟩
  refine ⟨fun i hi => ⟨(hs i hi).1, (hs i hi).2.1, hreach i hi⟩, fun i hi j hj e => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hsurj i hi
  obtain ⟨b, hb, rfl⟩ := hsurj j hj
  rcases lt_trichotomy a b with h' | h' | h'
  · exact absurd e (ne_of_lt (hmono a b h' hb))
  · rw [h']
  · exact absurd e.symm (ne_of_lt (hmono b a h' ha))

theorem closK_sound {step : Nat → Nat → Nat} {ngen N : Nat} {P IX : Nat → Nat}
    (h : ∀ i < N, closK step ngen N P IX i = true) :
    ∀ i < N, ∀ l < ngen, ∃ j < N, rtOf IX j = rtOf IX i ∧ step l (P i) = P j := by
  intro i hi l hl
  have hc := h i hi
  unfold closK at hc
  rw [letB_eq, List.all_eq_true] at hc
  have h2 := hc l (List.mem_range.2 hl)
  rw [letB_eq] at h2
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h2
  exact ⟨_, h2.1.1, h2.1.2, h2.2⟩

theorem posK_sound {test : Nat → Bool} {X P POS : Nat → Nat} {N m : Nat}
    (h : ∀ j < m, posK test X P POS N j = true) :
    ∀ j < m, test (X j) = true → POS j < N ∧ P (POS j) = X j := by
  intro j hj ht
  have hp := h j hj
  unfold posK at hp
  rw [ht] at hp
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hp
  exact hp

theorem rec_sum' (G : Nat → Nat) (k : Nat) :
    Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 => Nat.add (G l) ih2) k =
      ∑ l ∈ Finset.range k, G l := by
  induction k with
  | zero => rw [Finset.sum_range_zero]; rfl
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact Nat.add_comm _ _

theorem sumBelow_eq' (m hi : Nat) (f : Nat → Nat) :
    sumBelow m hi f = ∑ i ∈ Finset.range (64 * hi), if i < m then f i else 0 := by
  induction hi with
  | zero => rw [Nat.mul_zero, Finset.sum_range_zero]; rfl
  | succ h ih =>
    change Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 +
        sumBelow m h f = _
    rw [rec_sum', ih, Nat.mul_succ, Finset.sum_range_add,
      Nat.add_comm (Finset.sum (Finset.range 64) _)]
    refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
    have e6 : (2 : Nat) ^ 6 = 64 := rfl
    have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
      change h <<< 6 + l = 64 * h + l
      rw [Nat.shiftLeft_eq, e6]
      omega
    simp only [e, nIf_eq', Nat.blt_eq]

theorem rootCount_eq {IX : Nat → Nat} {N hi : Nat} (hN : N ≤ 64 * hi) (k : Nat) :
    rootCount IX N hi k = ((Finset.range N).filter fun i => rtOf IX i = k).card := by
  unfold rootCount
  rw [sumBelow_eq', Finset.card_filter, ← Finset.sum_filter]
  have hs : (Finset.range (64 * hi)).filter (fun i => i < N) = Finset.range N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases h : Nat.beq (rtOf IX i) k
  · have hne : rtOf IX i ≠ k := fun e => by
      rw [e, Nat.beq_refl] at h
      exact Bool.noConfusion h
    rw [if_neg hne]
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]

end CFSG.KC.Co2Census

end
