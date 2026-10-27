module

public import Certificates.Data.Kernel.Co2CenTree
public import CFSG.Certificates.Kernel.Co2J.Sound

public section

namespace CFSG.KC.Co2Cen

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.TabMatGrp CFSG.KLie.CT CFSG.KC.M1F2
  CFSG.KC.Co2Syl CFSG.KC.Co2J

section Tree

variable {PE PM PS : Nat → Nat} {PT : Nat → Nat → Nat} {MK : Nat → Nat} {N : Nat}

theorem edgeN_spec {m X g t : Nat} (h : edgeN PE N m X g t = true) (hm : m ≤ t) :
    t < N ∧ PE t = mulT X g := by
  unfold edgeN at h
  rw [implK_eq, notK_eq, blt_false (Nat.not_lt.2 hm), Bool.not_false, if_pos rfl, andK_eq,
    Bool.and_eq_true] at h
  exact ⟨blt_iff.1 h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem recN_spec {s : Nat} (h : recN PE PM PS PT MK N s = true) :
    (∀ j < 5, PM s ≤ PT s j → PT s j < N ∧ PE (PT s j) = mulT (PE s) (MK j)) ∧
    s < PM s ∧ PM s ≤ N ∧
    rowK (PM s) (PT s 0) (PT s 1) (PT s 2) (PT s 3) (PT s 4) = nextN PM N s ∧
    sortN PE PS N s = true := by
  unfold recN at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
  obtain ⟨e0, e1, e2, e3, e4, hm, hm', hr, hs⟩ := h
  refine ⟨fun j hj hle => ?_, blt_iff.1 hm, Nat.le_of_ble_eq_true hm', Nat.eq_of_beq_eq_true hr,
    hs⟩
  interval_cases j
  · exact edgeN_spec e0 hle
  · exact edgeN_spec e1 hle
  · exact edgeN_spec e2 hle
  · exact edgeN_spec e3 hle
  · exact edgeN_spec e4 hle

structure TreeN (PE PM PS : Nat → Nat) (PT : Nat → Nat → Nat) (MK : Nat → Nat) (N : Nat) :
    Prop where
  ok : ∀ s < N, recN PE PM PS PT MK N s = true
  small : N < BAD
  zero : PE 0 = IDT
  one : PM 0 = 1

theorem treeNK_spec (h : treeNK PE PM PS PT MK N = true) : TreeN PE PM PS PT MK N := by
  unfold treeNK at h
  simp only [andK_eq, Bool.and_eq_true] at h
  exact ⟨allK_spec h.2.2.2, blt_iff.1 h.1, Nat.eq_of_beq_eq_true h.2.1,
    Nat.eq_of_beq_eq_true h.2.2.1⟩

@[expose] noncomputable def MfN (PM : Nat → Nat) (N k : Nat) : Nat := if k < N then PM k else N

theorem MfN_succ (k : Nat) : MfN PM N (k + 1) = nextN PM N k := by
  unfold MfN nextN
  rw [selN_eq]
  by_cases h : k + 1 < N
  · rw [iteT h, blt_iff.2 h, iteT rfl]
  · rw [iteF h, blt_false h, iteF Bool.false_ne_true]

theorem MfN_lt (hR : TreeN PE PM PS PT MK N) (k : Nat) : MfN PM N k < BAD := by
  unfold MfN
  split
  · exact lt_of_le_of_lt (recN_spec (hR.ok k ‹_›)).2.2.1 hR.small
  · exact hR.small

theorem treeN_mem (hR : TreeN PE PM PS PT MK N) :
    ∀ t < N, PE t < 2 ^ 100 ∧ MatP 10 (PE t) ∈ genT MK := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    rw [hR.zero, MatP_IDT]
    exact ⟨IDT_lt, (genT MK).one_mem⟩
  have hP0 : MfN PM N 0 ≤ t := by
    unfold MfN
    rw [iteT (by omega : 0 < N), hR.one]
    omega
  have hkP : MfN PM N (Nat.findGreatest (fun k => MfN PM N k ≤ t) N) ≤ t :=
    Nat.findGreatest_spec (P := fun k => MfN PM N k ≤ t) (Nat.zero_le N) hP0
  have hkN := Nat.findGreatest_le (P := fun k => MfN PM N k ≤ t) N
  generalize hk : Nat.findGreatest (fun k => MfN PM N k ≤ t) N = k at hkP hkN
  have hkN' : k < N := by
    rcases Nat.lt_or_ge k N with h | h
    · exact h
    · have e : k = N := le_antisymm hkN h
      rw [e] at hkP
      unfold MfN at hkP
      rw [iteF (Nat.lt_irrefl N)] at hkP
      omega
  have hk1 : t < MfN PM N (k + 1) := by
    have := Nat.findGreatest_is_greatest (P := fun k => MfN PM N k ≤ t) (k := k + 1)
      (by rw [hk]; exact Nat.lt_succ_self k) (Nat.succ_le_of_lt hkN')
    exact Nat.lt_of_not_le this
  obtain ⟨hedge, hkm, -, hrow, -⟩ := recN_spec (hR.ok k hkN')
  have e1 : MfN PM N k = PM k := iteT hkN'
  rw [← MfN_succ] at hrow
  have hb : rowK (PM k) (PT k 0) (PT k 1) (PT k 2) (PT k 3) (PT k 4) < BAD := by
    rw [hrow]
    exact MfN_lt hR (k + 1)
  obtain ⟨-, hcov⟩ := rowK_cover hb
  rw [hrow] at hcov
  have hmt : PM k ≤ t := by
    rw [← e1]
    exact hkP
  obtain ⟨j, hj, hjt⟩ : ∃ j < 5, PT k j = t := by
    rcases hcov t hmt hk1 with e | e | e | e | e
    · exact ⟨0, by omega, e.symm⟩
    · exact ⟨1, by omega, e.symm⟩
    · exact ⟨2, by omega, e.symm⟩
    · exact ⟨3, by omega, e.symm⟩
    · exact ⟨4, by omega, e.symm⟩
  obtain ⟨-, he⟩ := hedge j hj (by rw [hjt]; exact hmt)
  rw [hjt] at he
  rw [he, MatP_mulT]
  exact ⟨mulT_lt _ _, (genT MK).mul_mem (ih k (by omega) hkN').2 (genT_mem MK hj)⟩

theorem treeN_inj (hR : TreeN PE PM PS PT MK N) :
    ∀ a < N, ∀ b < N, MatP 10 (PE a) = MatP 10 (PE b) → a = b := by
  have hs : ∀ i < N, PS i < N := by
    intro i hi
    have h := (recN_spec (hR.ok i hi)).2.2.2.2
    unfold sortN at h
    rw [andK_eq, Bool.and_eq_true] at h
    exact blt_iff.1 h.1
  have hlt : ∀ i, i + 1 < N → PE (PS i) < PE (PS (i + 1)) := by
    intro i hi
    have h := (recN_spec (hR.ok i (by omega))).2.2.2.2
    unfold sortN at h
    rw [andK_eq, Bool.and_eq_true, implK_eq, blt_iff.2 hi, iteT rfl] at h
    exact blt_iff.1 h.2
  intro a ha b hb e
  exact sorted_inj (σ := PS) (f := PE) hs hlt a ha b hb
    (MatP_inj e (treeN_mem hR a ha).1 (treeN_mem hR b hb).1)

noncomputable def entN (hR : TreeN PE PM PS PT MK N) (k : Fin N) : genT MK :=
  ⟨MatP 10 (PE k), (treeN_mem hR k k.2).2⟩

theorem entN_inj (hR : TreeN PE PM PS PT MK N) : Function.Injective (entN hR) :=
  fun a b e => Fin.ext (treeN_inj hR a a.2 b b.2 (congrArg Subtype.val e))

theorem treeN_card (hR : TreeN PE PM PS PT MK N) : N ≤ Nat.card (genT MK) := by
  simpa using Nat.card_le_card_of_injective _ (entN_inj hR)

end Tree

end CFSG.KC.Co2Cen

end
