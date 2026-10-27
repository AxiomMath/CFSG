module

public import CFSG.Certificates.Kernel.LocalQTPipeCosetBfs
public import CFSG.Certificates.Kernel.LocalQTPipeCosetTab

public section

namespace CFSG.KC.LQT.PPC

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.PPB
open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem qpK_eq (TF : Nat → Nat) (qp : List (Nat × Nat)) : qpK TF qp = qp.map fun p => TF p.1 := by
  induction qp with
  | nil => rfl
  | cons p t ih =>
    have e : qpK TF (p :: t) = TF p.1 :: qpK TF t := rfl
    rw [e, ih, List.map_cons]

theorem repsAt_spec {N W : Nat} {RC : List Nat} {RPK RIK QPK QGK DPK : Nat} {REPS OML : List Nat}
    {i : Nat} (h : repsAt N W RC RPK RIK QPK QGK DPK REPS OML i = true) :
    imgW W RPK i < N ∧ getK REPS (imgW W RIK i) = imgW W RPK i ∧
    (getK OML (imgW W RIK i)).testBit i = true ∧
    ((i = imgW W RPK i ∧ imgW W DPK i = 0) ∨
      (i ≠ imgW W RPK i ∧ imgW W QGK i < RC.length ∧
        imgW W (getK RC (imgW W QGK i)) (imgW W QPK i) = i ∧
        (getK OML (imgW W RIK i)).testBit (imgW W QPK i) = true ∧
        imgW W DPK (imgW W QPK i) < imgW W DPK i)) := by
  unfold repsAt at h
  simp only [letB_eq, andB_iff, blt_iff, beq_iff, bitK_eq] at h
  obtain ⟨h1, h2, h3, _, h5⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  by_cases hir : i = imgW W RPK i
  · have hb : Nat.beq i (imgW W RPK i) = true := beq_iff.2 hir
    rw [hb] at h5
    change Nat.beq (imgW W DPK i) 0 = true at h5
    exact Or.inl ⟨hir, beq_iff.1 h5⟩
  · have hb : Nat.beq i (imgW W RPK i) = false :=
      Bool.eq_false_iff.2 (fun h => hir (beq_iff.1 h))
    rw [hb] at h5
    change andB ((imgW W QGK i).blt (lenA RC))
        (andB ((imgW W (getK RC (imgW W QGK i)) (imgW W QPK i)).beq i)
          (andB ((getK OML (imgW W RIK i)).testBit (imgW W QPK i))
            ((imgW W DPK (imgW W QPK i)).blt (imgW W DPK i)))) = true at h5
    simp only [letB_eq, andB_iff, blt_iff, beq_iff, bitK_eq, lenA_eq] at h5
    obtain ⟨a1, a2, a3, a4⟩ := h5
    exact Or.inr ⟨hir, a1, a2, a3, a4⟩

theorem getK_testBit_lt {l : List Nat} {a j : Nat} (h : (getK l a).testBit j = true) :
    a < l.length := by
  by_contra hn
  rw [getK_eq, List.getD_eq_default _ _ (by omega)] at h
  simp at h

theorem mem_le_sum {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons y t ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem reps_sound {N W : Nat} (hN : 0 < N) {qp : List (Nat × Nat)} {TF : Nat → Nat}
    {tab : Nat → Array Nat} (hT : ∀ p ∈ qp, TabP N W (TF p.1) (tab p.1)) {repR : Array Nat}
    {RPK RIK QPK QGK DPK : Nat} {REPS OML : List Nat} (hRP : Rep N W RPK repR)
    (hrs : repsSumK N REPS OML = true)
    (hall : ∀ i < N, repsAt N W (qpK TF qp) RPK RIK QPK QGK DPK REPS OML i = true) :
    (∀ i < N, repR.getD i 0 ∈ REPS) ∧
      ∀ i < N, Reach (qp.map fun p => tab p.1) (repR.getD i 0) i := by
  unfold repsSumK at hrs
  rw [andB_iff, andB_iff, beq_iff, beq_iff, sumL_eq, lenA_eq, lenA_eq] at hrs
  obtain ⟨hsum0, hlen, _⟩ := hrs
  have hsum : OML.sum = 2 ^ N - 1 := by
    rw [hsum0]; exact (by rw [show Nat.shiftLeft 1 N = 2 ^ N from shiftLeft_one N]; rfl)
  have hrd : ∀ i < N, imgW W RPK i = repR.getD i 0 := fun i hi => (hRP.2 i hi).2
  have hcover : ∀ i < N, ∃ m ∈ OML, m.testBit i = true := by
    intro i hi
    have := (repsAt_spec (hall i hi)).2.2.1
    have hl := getK_testBit_lt this
    refine ⟨getK OML (imgW W RIK i), ?_, this⟩
    rw [getK_eq, List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  have hdisj := mask_disjoint N OML hcover hsum
  rw [List.pairwise_iff_getElem] at hdisj
  have hbit_lt : ∀ {a q : Nat}, (getK OML a).testBit q = true → q < N := by
    intro a q h
    have hl := getK_testBit_lt h
    by_contra hq
    have hle : getK OML a ≤ OML.sum := by
      rw [getK_eq, List.getD_eq_getElem _ _ hl]
      exact mem_le_sum (List.getElem_mem hl)
    have hlt : getK OML a < 2 ^ N := by
      have : 0 < 2 ^ N := Nat.two_pow_pos N
      omega
    rw [testBit_lt hlt (by omega)] at h
    simp at h
  have same : ∀ a b j : Nat, (getK OML a).testBit j = true → (getK OML b).testBit j = true →
      a = b := by
    intro a b j h1 h2
    have ha := getK_testBit_lt h1
    have hb := getK_testBit_lt h2
    by_contra hne
    rw [getK_eq, List.getD_eq_getElem _ _ ha] at h1
    rw [getK_eq, List.getD_eq_getElem _ _ hb] at h2
    have key : ∀ a b (ha : a < OML.length) (hb : b < OML.length), a < b →
        OML[a].testBit j = true → OML[b].testBit j = true → False := by
      intro a b ha hb hab h1 h2
      have := congrArg (fun z => z.testBit j) (hdisj a b ha hb hab)
      simp only [Nat.testBit_and, Nat.zero_testBit, h1, h2] at this
      simp at this
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key a b ha hb h h1 h2
    · exact key b a hb ha h h2 h1
  constructor
  · intro i hi
    have hs := repsAt_spec (hall i hi)
    have hl := getK_testBit_lt hs.2.2.1
    rw [← hrd i hi, ← hs.2.1, getK_eq, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  · have claim : ∀ d, ∀ i < N, imgW W DPK i = d →
        Reach (qp.map fun p => tab p.1) (imgW W RPK i) i := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro i hi hd
        have hs := repsAt_spec (hall i hi)
        rcases hs.2.2.2 with ⟨hir, _⟩ | ⟨hir, hgi, hq, hbq, hdep⟩
        · rw [← hir]; exact Reach.base
        · have hqN : imgW W QPK i < N := hbit_lt hbq
          have hsq := repsAt_spec (hall _ hqN)
          have hidx := same _ _ _ hbq hsq.2.2.1
          have hrq : imgW W RPK (imgW W QPK i) = imgW W RPK i := by
            rw [← hs.2.1, ← hsq.2.1, hidx]
          have hih := ih _ (by omega) _ hqN rfl
          rw [hrq] at hih
          rw [qpK_eq, List.length_map] at hgi
          rw [qpK_eq] at hq
          have hget : getK (qp.map fun p => TF p.1) (imgW W QGK i) = TF (qp[imgW W QGK i]).1 := by
            rw [getK_eq, List.getD_eq_getElem _ _ (by simpa using hgi)]
            simp
          rw [hget] at hq
          have hp := hT _ (List.getElem_mem hgi)
          have hq2 : arrImg (tab (qp[imgW W QGK i]).1) (imgW W QPK i) = i := by
            have := (hp.1.2 _ hqN).2
            rw [hq] at this
            exact this.symm
          have := Reach.step (tab (qp[imgW W QGK i]).1)
            (List.mem_map.2 ⟨_, List.getElem_mem hgi, rfl⟩) hih
          rwa [hq2] at this
    intro i hi
    rw [← hrd i hi]
    exact claim _ i hi rfl

end CFSG.KC.LQT.PPC
