module

public import Certificates.Data.Kernel.LocalQT.RankQ
public import CFSG.Certificates.Kernel.LocalQTRankBSound

public section

namespace CFSG.KC.LQT.RB

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BW.Cl CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem letRQ_eq (y : Nat) (k : Nat → Bool) : letRQ y k = k y := by
  cases y <;> rfl

theorem rowRQ_spec {W g N : Nat} {PT CT QT : Nat → Nat}
    (hq : ∀ i < N, rowRQ W g N PT CT QT i = true) {i : Nat} (hi : i < N) :
    (∀ j < g, imgW W (QT (fieldT W CT j)) i < N ∧
      imgW W (QT (fieldT W CT j)) i = fieldT W CT (Nat.add (Nat.mul i (Nat.add g g)) j)) ∧
    (i = 0 → ∀ k < N, mulRQ W QT i k = k) ∧
    (i ≠ 0 → fieldT W PT i < i ∧ genIdxT W g (Nat.add g g) PT CT i < g ∧ ∀ k < N,
      mulRQ W QT i k = imgW W (QT (fieldT W CT (genIdxT W g (Nat.add g g) PT CT i)))
        (mulRQ W QT (fieldT W PT i) k)) := by
  have hr := hq i hi
  rw [rowRQ, letRQ_eq, andB_eq, Bool.and_eq_true] at hr
  obtain ⟨hs, hr⟩ := hr
  refine ⟨fun j hj => ?_, fun h0 k hk => ?_, fun h0 => ?_⟩
  · have h := allR_true hs j hj
    simp only [Nat.zero_add] at h
    rw [letRQ_eq, andB_eq, Bool.and_eq_true] at h
    exact ⟨P.blt_iff.1 h.1, P.beq_iff.1 h.2⟩
  · subst h0
    have hb : Nat.beq 0 0 = true := rfl
    rw [hb] at hr
    change imgW W (QT 0) k = k
    exact P.beq_iff.1 (by simpa using allR_true hr k hk)
  · have hb : Nat.beq i 0 = false := by
      cases h : Nat.beq i 0
      · rfl
      · exact absurd (P.beq_iff.1 h) h0
    rw [hb] at hr
    change andB _ _ = true at hr
    rw [andB_eq, Bool.and_eq_true, letRQ_eq, andB_eq, Bool.and_eq_true, letRQ_eq, letRQ_eq] at hr
    obtain ⟨hp, hj, he⟩ := hr
    refine ⟨P.blt_iff.1 hp, P.blt_iff.1 hj, fun k hk => ?_⟩
    change imgW W (QT i) k = _
    rw [P.beq_iff.1 he]
    exact imgW_ofFnW (fun _ _ => imgW_lt _ _ _) hk

theorem rowRQ_lt {W g N : Nat} {PT CT QT : Nat → Nat}
    (hq : ∀ i < N, rowRQ W g N PT CT QT i = true) : ∀ i < N, ∀ k < N, mulRQ W QT i k < N := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi k hk
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [(rowRQ_spec hq hi).2.1 rfl k hk]
      exact hk
    · obtain ⟨hp, hj, he⟩ := (rowRQ_spec hq hi).2.2 (by omega)
      rw [he k hk]
      exact ((rowRQ_spec hq (ih _ hp (by omega) k hk)).1 _ hj).1

theorem rowRQ_step {W g N : Nat} {PT CT QT : Nat → Nat}
    (hq : ∀ i < N, rowRQ W g N PT CT QT i = true) {i : Nat} (hi : i < N) (h0 : i ≠ 0) :
    fieldT W PT i < i ∧ ∀ k < N, mulRQ W QT i k =
      fieldT W CT (Nat.add (Nat.mul (mulRQ W QT (fieldT W PT i) k) (Nat.add g g))
        (genIdxT W g (Nat.add g g) PT CT i)) := by
  obtain ⟨hp, hj, he⟩ := (rowRQ_spec hq hi).2.2 h0
  refine ⟨hp, fun k hk => ?_⟩
  rw [he k hk]
  exact ((rowRQ_spec hq (rowRQ_lt hq _ (by omega) k hk)).1 _ hj).2

theorem mulRQ_of_rowRQ {W g N : Nat} {PT CT QT : Nat → Nat}
    (hq : ∀ i < N, rowRQ W g N PT CT QT i = true) :
    ∀ f i, i < f → i < N → ∀ k < N,
      mulT W g f PT CT i k = mulRQ W QT i k ∧ mulRQ W QT i k < N := by
  intro f
  induction f with
  | zero => intro i hi; omega
  | succ f ih =>
    intro i hif hiN k hk
    refine ⟨?_, rowRQ_lt hq i hiN k hk⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · change k = imgW W (QT 0) k
      exact ((rowRQ_spec hq hiN).2.1 rfl k hk).symm
    · have hb : Nat.beq i 0 = false := by
        cases h : Nat.beq i 0
        · rfl
        · exact absurd (P.beq_iff.1 h) (by omega)
      obtain ⟨hp', hs⟩ := rowRQ_step hq hiN (by omega)
      have ih' := (ih (fieldT W PT i) (by omega) (by omega) k hk).1
      have e : mulT W g (f + 1) PT CT i k = fieldT W CT (Nat.add (Nat.mul
          (mulT W g f PT CT (fieldT W PT i) k) (Nat.add g g)) (genIdxT W g (Nat.add g g) PT CT i)) := by
        change Bool.rec (motive := fun _ => Nat) _ k (Nat.beq i 0) = _
        rw [hb]
        rfl
      rw [e, ih', hs k hk]

theorem branchF_congr {N : Nat} {m1 m2 : Nat → Nat → Nat}
    (hm : ∀ a < N, ∀ b < N, m1 a b = m2 a b ∧ m1 a b < N) {invs : List Nat}
    (hinv : ∀ c ∈ invs, c < N) {z : Nat} (hz : z < N) (d c : Nat) (hc : c < N) :
    branchF m1 invs z d c = branchF m2 invs z d c := by
  have h0 : 0 < N := by omega
  have hS : ∀ s ∈ appK [0, z] (mapW (m1 c) [0, z]), s < N := by
    rw [appK_eq, mapW_eq]
    intro s hs
    simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact h0
    · exact hz
    · exact (hm c hc 0 h0).2
    · exact (hm c hc z hz).2
  have hL : ∀ l ∈ [c, z], l < N := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact hc
    · exact hz
  have hd := dfs_congr hm hinv d [c, z] _ hL hS
  rw [← dfsW_eq, ← dfsW_eq] at hd
  have hmap : mapW (m1 c) [0, z] = mapW (m2 c) [0, z] := by
    rw [mapW_eq, mapW_eq]
    simp only [List.map_cons, List.map_nil, (hm c hc 0 h0).1, (hm c hc z hz).1]
  unfold branchF
  rw [hd, hmap, (hm c hc z hz).1, (hm z hz c hc).1]

theorem rankBP_of_rankBQ {W g N : Nat} {PT CT QT : Nat → Nat}
    (hq : ∀ i < N, rowRQ W g N PT CT QT i = true) {d zi lo len : Nat} (hz : zi < N)
    (h : rankBQ W N QT d zi lo len = true) : rankBP W g N PT CT d zi lo len = true := by
  have hm : ∀ a < N, ∀ b < N, mulT W g N PT CT a b = mulRQ W QT a b ∧ mulT W g N PT CT a b < N := by
    intro a ha b hb
    obtain ⟨e, hlt⟩ := mulRQ_of_rowRQ hq N a ha ha b hb
    exact ⟨e, e ▸ hlt⟩
  have hI : invsB N (mulT W g N PT CT) = invsB N (mulRQ W QT) := by
    unfold invsB
    rw [filterN_eq, filterN_eq]
    apply List.filter_congr
    intro i hi
    rw [(hm i (List.mem_range.1 hi) i (List.mem_range.1 hi)).1]
  have hinv : ∀ c ∈ invsB N (mulRQ W QT), c < N := by
    intro c hc
    unfold invsB at hc
    rw [filterN_eq, List.mem_filter, List.mem_range] at hc
    exact hc.1
  change allL (sliceK (invsB N (mulT W g N PT CT)) lo len)
    (branchF (mulT W g N PT CT) (invsB N (mulT W g N PT CT)) zi d) = true
  change allL (sliceK (invsB N (mulRQ W QT)) lo len)
    (branchF (mulRQ W QT) (invsB N (mulRQ W QT)) zi d) = true at h
  rw [hI]
  rw [allL_eq, List.all_eq_true] at h ⊢
  intro c hc
  have hcm : c ∈ invsB N (mulRQ W QT) :=
    List.mem_of_mem_drop (List.mem_of_mem_take (by rw [sliceK] at hc; exact hc))
  rw [branchF_congr hm hinv hz d c (hinv c hcm)]
  exact h c hc

theorem rankBQ_sound {n w : Nat} (hw : n ≤ 2 ^ w) (W : Nat) (B ta tb : List Nat)
    (prog qp : List (Nat × Nat)) (d k fuel dd zi K L PK CK RP RC : Nat) (PT CT QT : Nat → Nat)
    (h : rankBH n w W B ta tb prog qp k fuel dd zi K L PK CK RP RC PT CT = true)
    (hq : ∀ i < 2 ^ k, rowRQ W qp.length (2 ^ k) PT CT QT i = true) (hz : zi < 2 ^ k)
    (hp : ∀ j < K, rankBQ W (2 ^ k) QT d zi (j * L) L = true) :
    RankCert.RankCertS n B (slpTabsA ta.toArray tb.toArray prog) qp (d + 1)
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.1
      (bfsEnumB n B (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.1]!)
        (qp.map fun p => (slpTabsA ta.toArray tb.toArray prog)[p.2]!) fuel).2.2 k :=
  rankB_sound hw W B ta tb prog qp d k fuel dd zi K L PK CK RP RC PT CT h
    fun j hj => rankBP_of_rankBQ hq hz (hp j hj)

end CFSG.KC.LQT.RB

end
