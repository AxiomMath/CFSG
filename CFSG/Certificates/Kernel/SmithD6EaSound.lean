module

public import Certificates.Data.Kernel.SmithD6.EaK
public import CFSG.Certificates.Kernel.PkTreeSound

public section

namespace CFSG.KD.SmithD6Ea

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab
  CFSG.KD.SmithD6ST CFSG.KD.SmithD6Reps

theorem isNilL_sound {ps : List Nat} (h : isNilL ps = true) : ps = [] := by
  cases ps
  · rfl
  · exact absurd h (by simp [isNilL])

theorem eaGo_sound : ∀ (l ps : List Nat), eaGo l ps = true → ps = l.filter eaInK
  | [], ps, h => isNilL_sound h
  | k :: l, ps, h => by
    have e : eaGo (k :: l) ps = bIf(eaInK k,
        List.rec (motive := fun _ => Bool) false (fun h t _ => bAnd(Nat.beq h k, eaGo l t)) ps,
        eaGo l ps) := rfl
    rw [e] at h
    cases hk : eaInK k
    · rw [List.filter_cons_of_neg (by simp [hk])]
      exact eaGo_sound l ps (pkIf_false h hk)
    · rw [List.filter_cons_of_pos hk]
      have h2 := pkIf_true h hk
      cases ps with
      | nil => exact absurd h2 (by simp)
      | cons a t =>
        obtain ⟨ha, ht⟩ := pkAnd_true h2
        rw [Nat.eq_of_beq_eq_true ha, eaGo_sound l t ht]

@[expose] def eaF (k : Nat) : Nat := packL (eaRestr (pairK k))

theorem eaF4Go_sound : ∀ (ks : List Nat) (prev : Nat), eaF4Go ks prev = true →
    (∀ k ∈ ks, lineTree.memB k = true ∧ eaInK k = true ∧ prev < eaF k) ∧
      (ks.map eaF).Pairwise (· < ·)
  | [], _, _ => ⟨by simp, by simp⟩
  | k :: ks, prev, h => by
    simp only [eaF4Go, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hm, hi⟩, hp⟩, hr⟩ := h
    obtain ⟨h1, h2⟩ := eaF4Go_sound ks _ hr
    refine ⟨?_, ?_⟩
    · intro k' hk'
      rcases List.mem_cons.1 hk' with rfl | hk'
      · exact ⟨hm, hi, hp⟩
      · obtain ⟨a, b, c⟩ := h1 k' hk'
        exact ⟨a, b, lt_trans hp c⟩
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨?_, h2⟩
      intro y hy
      obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hy
      exact (h1 k' hk').2.2

theorem eaIncr_sound : ∀ (l : List Nat) (prev : Nat), eaIncr l prev = true →
    (∀ k ∈ l, prev < k) ∧ l.Pairwise (· < ·)
  | [], _, _ => ⟨by simp, by simp⟩
  | k :: l, prev, h => by
    simp only [eaIncr, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := eaIncr_sound l k h.2
    refine ⟨?_, List.pairwise_cons.2 ⟨h1, h2⟩⟩
    intro k' hk'
    rcases List.mem_cons.1 hk' with rfl | hk'
    · exact h.1
    · exact lt_trans h.1 (h1 k' hk')

end CFSG.KD.SmithD6Ea

end
