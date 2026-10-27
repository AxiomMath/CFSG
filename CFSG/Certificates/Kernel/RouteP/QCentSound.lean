module

public import CFSG.Certificates.Kernel.RouteP.MemSBits
public import CFSG.Certificates.Kernel.PopF
public import Certificates.Data.Kernel.RouteP.QCentSet

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.Fi24Net
  CFSG.KC.RouteP CFSG.KS.Fi24Net CFSG.KC.PopF

theorem memS_land (a b N : Nat) : memS (Nat.land a b) N = (memS a N && memS b N) := by
  unfold memS
  rw [nland, Nat.testBit_and]

theorem pos_lt {N : Nat} (hN : N < 920808) : N % 3 * 524288 + N / 3 < 1572864 := by
  have := Nat.mod_lt N (by decide : 3 > 0)
  have h2 : N % 3 * 524288 ≤ 2 * 524288 := Nat.mul_le_mul_right _ (by omega)
  omega

theorem memS_ones {N : Nat} (hN : N < 920808) : memS (ones (nat_lit 1572864)) N = true := by
  unfold memS
  rw [testBit_onesW]
  exact decide_eq_true (pos_lt hN)

theorem memS_mk3 {a b c : Nat} (ha : Small a) (hb : Small b) {N : Nat} (hN : N < 920808) :
    memS (mk3 a b c) N =
      (if N % 3 = 0 then a.testBit (N / 3) else if N % 3 = 1 then b.testBit (N / 3)
        else c.testBit (N / 3)) := by
  unfold memS
  rw [testBit_mk3 ha hb]
  have h3 : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2 := by omega
  rcases h3 with h | h | h
  · have e : N % 3 * 524288 + N / 3 = N / 3 := by omega
    rw [e, if_pos (by omega), if_pos h]
  · have e : N % 3 * 524288 + N / 3 - 524288 = N / 3 := by omega
    rw [if_neg (by omega), if_pos (by omega), e, if_neg (by omega), if_pos h]
  · have e : N % 3 * 524288 + N / 3 - 1048576 = N / 3 := by omega
    rw [if_neg (by omega), if_neg (by omega), e, if_neg (by omega), if_neg (by omega)]

theorem small_zero : Small 0 := fun q _ => Nat.zero_testBit q

theorem small_full : Small full := fun q hq => by
  rw [testBit_full, decide_eq_false (by omega)]

theorem idPl_testBit {k : Nat} (hk : k < 19) (p : Nat) :
    (idPlane (nat_lit 524288) k).testBit p = (decide (p < 524288) && p.testBit k) :=
  idPlane_testBit (k := 19) hk p

theorem small_idPl {k : Nat} (hk : k < 19) : Small (idPlane (nat_lit 524288) k) := fun q hq => by
  rw [idPl_testBit hk, decide_eq_false (by omega)]
  rfl

theorem memS_sepS {k N : Nat} (hk : k < 21) (hN : N < 920808) :
    memS (sepS k) N = if k < 19 then (N / 3).testBit k else decide (N % 3 = k - 19) := by
  have hp : N / 3 < 524288 := by omega
  have r19 : (nat_lit 19 : Nat) = 19 := rfl
  by_cases h : k < 19
  · have e : sepS k = mk3 (idPlane (nat_lit 524288) k) (idPlane (nat_lit 524288) k)
        (idPlane (nat_lit 524288) k) := by
      unfold sepS
      rw [r19, Nat.blt_eq.mpr h]
    rw [e, memS_mk3 (small_idPl h) (small_idPl h) hN, if_pos h, idPl_testBit h,
      decide_eq_true hp, Bool.true_and]
    split_ifs <;> rfl
  · rw [if_neg h]
    by_cases h19 : k = 19
    · subst h19
      have e : sepS 19 = mk3 full 0 0 := rfl
      rw [e, memS_mk3 small_full small_zero hN]
      rcases (by omega : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2) with h3 | h3 | h3 <;>
        simp [h3, testBit_full, hp]
    · have hk20 : k = 20 := by omega
      subst hk20
      have e : sepS 20 = mk3 0 full 0 := rfl
      rw [e, memS_mk3 small_zero small_full hN]
      rcases (by omega : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2) with h3 | h3 | h3 <;>
        simp [h3, testBit_full, hp]

theorem eq_of_sepS {N M : Nat} (hN : N < 920808) (hM : M < 920808)
    (h : ∀ k < 21, memS (sepS k) N = memS (sepS k) M) : N = M := by
  have hs : N % 3 = M % 3 := by
    have a := h 19 (by decide)
    have b := h 20 (by decide)
    rw [memS_sepS (by decide) hN, memS_sepS (by decide) hM] at a b
    simp only [show ¬ (19 < 19) by decide, show ¬ (20 < 19) by decide, if_false] at a b
    have h3 := Nat.mod_lt N (by decide : 3 > 0)
    have h4 := Nat.mod_lt M (by decide : 3 > 0)
    by_cases e0 : N % 3 = 0
    · rw [decide_eq_true e0] at a
      exact e0.trans (of_decide_eq_true a.symm).symm
    · by_cases e1 : N % 3 = 1
      · rw [decide_eq_true e1] at b
        exact e1.trans (of_decide_eq_true b.symm).symm
      · rw [decide_eq_false e0] at a
        rw [decide_eq_false e1] at b
        have := of_decide_eq_false a.symm
        have := of_decide_eq_false b.symm
        omega
  have hf : N / 3 = M / 3 := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 19
    · have a := h k (by omega)
      rw [memS_sepS (by omega) hN, memS_sepS (by omega) hM, if_pos hk, if_pos hk] at a
      exact a
    · have t1 : N / 3 < 2 ^ k :=
        lt_of_lt_of_le (by omega : N / 3 < 2 ^ 19) (Nat.pow_le_pow_right (by decide) (by omega))
      have t2 : M / 3 < 2 ^ k :=
        lt_of_lt_of_le (by omega : M / 3 < 2 ^ 19) (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow t1, Nat.testBit_lt_two_pow t2]
  omega

theorem fixR_succ (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) (n : Nat) :
    fixR NW KA KB z (n + 1) = Nat.land (fixR NW KA KB z n) (eqS (sepS n) (imgS NW KA KB z (sepS n))) := by
  change strictN (fixR NW KA KB z n) (fun t => Nat.land t (eqS (sepS n) (imgS NW KA KB z (sepS n)))) = _
  exact strictN_eq' _ _

theorem memS_fixR (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) {N : Nat} (hN : N < 920808) :
    ∀ n, memS (fixR NW KA KB z n) N = true ↔
      ∀ k < n, memS (sepS k) N = memS (imgS NW KA KB z (sepS k)) N
  | 0 => by
    change memS ptsS N = true ↔ _
    rw [memS_ptsS hN]
    exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | n + 1 => by
    rw [fixR_succ, memS_land, Bool.and_eq_true, memS_fixR NW KA KB z hN n]
    unfold eqS
    rw [memS_xor, memS_xor, memS_ones hN]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1 k hk
      · revert h2
        cases memS (sepS k) N <;> cases memS (imgS NW KA KB z (sepS k)) N <;> simp
    · intro h
      refine ⟨fun k hk => h k (by omega), ?_⟩
      rw [h n (by omega)]
      cases memS (imgS NW KA KB z (sepS n)) N <;> rfl

theorem memS_fixS {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {z : Int} (hz : LOK NW KA KB z) {N : Nat}
    (hN : N < 920808) : memS (fixS NW KA KB z) N = true ↔ eL NW KA KB z N = N := by
  unfold fixS
  rw [show (nat_lit 21 : Nat) = 21 from rfl, memS_fixR NW KA KB z hN]
  obtain ⟨M, hM, hMN⟩ := eL_surj hz hN
  constructor
  · intro h
    have hNM : N = M := eq_of_sepS hN hM fun k hk => by
      rw [h k hk, ← hMN, memS_imgS hz _ hM]
    rw [← hNM] at hMN
    exact hMN
  · intro h k _
    conv_rhs => rw [← h]
    rw [memS_imgS hz _ hN]

theorem ptCount_eq (s : Nat) : ptCount s = ((List.range 920808).filter (memS s)).length := by
  rw [← pcount_pts]
  unfold ptCount
  rw [show (nat_lit 21 : Nat) = 21 from rfl, CFSG.KS.PopF.pcF_eq (by decide), length_filter_range,
    pcount_eq, show (2 ^ 21 : Nat) = 1572864 + 524288 from rfl, cnt_add,
    cnt_zero_fun 524288 (fun i _ => by
      rw [nland, Nat.testBit_and, testBit_ptsS, decide_eq_false (by omega)]
      simp), Nat.add_zero]

theorem qcentSetOK_spec {NWP : Nat → Nat → Nat} {KAP KBP : Nat → Nat} {NWO : Nat → Nat → Nat}
    {KAO KBO : Nat → Nat} {NWQ : Nat → Nat → Nat} {KAQ KBQ : Nat → Nat} {zg qg : List Int}
    (h : qcentSetOK NWP KAP KBP NWO KAO KBO NWQ KAQ KBQ zg qg = true) :
    closedS NWQ KAQ KBQ qg (closeS NWQ KAQ KBQ qg 5 (single 749820)) = true ∧
      ((List.range 920808).filter (memS (Nat.land (fixS NWO KAO KBO 48)
        (closeS NWP KAP KBP zg 33 (single 1479))))).length = 3511 ∧
      ((List.range 920808).filter (memS (Nat.land (fixS NWO KAO KBO 48)
        (imgS NWO KAO KBO (-10) (closeS NWP KAP KBP zg 33 (single 1479)))))).length = 695 ∧
      ((List.range 920808).filter (memS (closeS NWQ KAQ KBQ qg 5 (single 749820)))).length = 693 ∧
      memS (closeS NWQ KAQ KBQ qg 5 (single 749820)) 99705 = false ∧
      ∀ N < 920808, memS (imgS NWO KAO KBO (-10) (closeS NWP KAP KBP zg 33 (single 1479))) N = true →
        memS (closeS NWP KAP KBP zg 33 (single 1479)) N = true →
        memS (fixS NWO KAO KBO 48) N = true →
        N = 99705 ∨ memS (closeS NWQ KAQ KBQ qg 5 (single 749820)) N = true := by
  unfold qcentSetOK at h
  simp only [letB_eq'] at h
  set G0 := closeS NWP KAP KBP zg 33 (single 1479)
  set F := fixS NWO KAO KBO 48
  set T := imgS NWO KAO KBO (-10) G0
  set Oq := closeS NWQ KAQ KBQ qg 5 (single 749820)
  unfold qcentCore at h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h⟩ := andB_true h
  obtain ⟨h4, h⟩ := andB_true h
  obtain ⟨h5, h6⟩ := andB_true h
  rw [letB_eq'] at h6
  have e2 := Nat.eq_of_beq_eq_true h2
  have e3 := Nat.eq_of_beq_eq_true h3
  have e4 := Nat.eq_of_beq_eq_true h4
  have e5 := Nat.eq_of_beq_eq_true h5
  have e6 := Nat.eq_of_beq_eq_true h6
  rw [ptCount_eq] at e2 e3 e4
  have hx : (99705 : Nat) < 920808 := by decide
  refine ⟨h1, e2, e3, e4, ?_, ?_⟩
  · have := congrArg (fun s => memS s 99705) e5
    simp only [memS_land, memS_single hx hx, decide_true, Bool.and_true] at this
    exact this.trans (Nat.zero_testBit _)
  · intro N hN hT hG hF
    have := congrArg (fun s => memS s N) e6
    simp only [memS_land, memS_lor, hT, hG, hF, Bool.true_and, memS_single hx hN] at this
    rcases Bool.or_eq_true_iff.1 this with h | h
    · exact Or.inr h
    · exact Or.inl (of_decide_eq_true h)

end CFSG.KS.RouteP

end
