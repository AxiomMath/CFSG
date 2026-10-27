module

public import Certificates.Data.Kernel.M24G.Todd
public import CFSG.Certificates.Kernel.M24G.ImgSound
public import CFSG.Certificates.Kernel.M24G.ListsSound
public import CFSG.Certificates.Kernel.O8PopcProved

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G CFSG.KC.O8

set_option exponentiation.threshold 4096

theorem testBit_packBits : ∀ (l : List Bool) (w : Nat), (packBits l).testBit w = l.getD w false
  | [], w => by simp [packBits]
  | b :: l, 0 => by
    rw [packBits, Nat.testBit_zero, List.getD_cons_zero]
    cases b <;> simp
  | b :: l, w + 1 => by
    rw [packBits, Nat.testBit_add_one, List.getD_cons_succ]
    have e : ((if b then 1 else 0) + 2 * packBits l) / 2 = packBits l := by split <;> omega
    rw [e, testBit_packBits l w]

theorem packBits_lt : ∀ l : List Bool, packBits l < 2 ^ l.length
  | [] => by simp [packBits]
  | b :: l => by
    have := packBits_lt l
    rw [packBits, List.length_cons, Nat.pow_succ]
    split <;> omega

theorem getD_lt {α : Type} (l : List α) (d : α) {n : Nat} (h : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_map_lt {β : Type} (f : Nat → β) {V : List Nat} {w : Nat} (hw : w < V.length)
    (d : β) : (V.map f).getD w d = f (V.getD w 0) := by
  rw [getD_lt _ _ (by simpa using hw), List.getElem_map, getD_lt _ _ hw]

theorem getD_range {n w : Nat} (hw : w < n) : (List.range n).getD w 0 = w := by
  rw [getD_lt _ _ (by simpa using hw), List.getElem_range]

def xorBits : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, a => a.testBit 0 ^^ xorBits k (a / 2)

theorem toddEven_eq : ∀ k a, Native.toddEven k a = !xorBits k a
  | 0, a => rfl
  | k + 1, a => by
    have ih := toddEven_eq k (a / 2)
    unfold Native.toddEven at ih ⊢
    rw [Native.toddPopc, xorBits, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one (Native.toddPopc k (a / 2)) with h' | h' <;>
      simp only [h, h', beq_iff_eq] at ih ⊢ <;>
      cases hx : xorBits k (a / 2) <;> simp_all <;> omega

theorem and_div_two (u v : Nat) : (u &&& v) / 2 = u / 2 &&& v / 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, ← Nat.testBit_add_one, ← Nat.testBit_add_one, ← Nat.testBit_add_one,
    Nat.testBit_and]

theorem testBit_actM_colsOf : ∀ (n : Nat) (V : List Nat) (u w : Nat), w < V.length →
    (Native.actM (colsOf n V) u).testBit w = xorBits n (u &&& V.getD w 0)
  | 0, V, u, w, _ => by simp [colsOf, Native.actM, xorBits]
  | n + 1, V, u, w, hw => by
    have ih := testBit_actM_colsOf n (V.map (· / 2)) (u / 2) w (by simpa using hw)
    rw [getD_map_lt _ hw] at ih
    rw [colsOf, Native.actM, Nat.testBit_xor, ih, xorBits, and_div_two, Nat.testBit_and]
    congr 1
    by_cases hu : u % 2 = 1
    · have h1 : u.testBit 0 = true := by simp [Nat.testBit_zero, hu]
      rw [if_pos hu, testBit_packBits, getD_map_lt _ hw, h1, Bool.true_and]
    · have h1 : u.testBit 0 = false := by simp [Nat.testBit_zero, hu]
      rw [if_neg hu, Nat.zero_testBit, h1, Bool.false_and]

theorem actM_lt {N : Nat} : ∀ (cs : List Nat), (∀ c ∈ cs, c < 2 ^ N) → ∀ u,
    Native.actM cs u < 2 ^ N
  | [], _, u => by
    rw [Native.actM]
    exact Nat.two_pow_pos N
  | c :: cs, h, u => by
    rw [Native.actM]
    refine Nat.xor_lt_two_pow ?_ (actM_lt cs (fun x hx => h x (List.mem_cons_of_mem c hx)) _)
    split
    · exact h c List.mem_cons_self
    · exact Nat.two_pow_pos N

theorem colsOf_lt : ∀ (n : Nat) (V : List Nat), ∀ c ∈ colsOf n V, c < 2 ^ V.length
  | 0, V, c, hc => by simp [colsOf] at hc
  | n + 1, V, c, hc => by
    rw [colsOf, List.mem_cons] at hc
    rcases hc with rfl | hc
    · have := packBits_lt (V.map fun v => v.testBit 0)
      rwa [List.length_map] at this
    · have := colsOf_lt n (V.map (· / 2)) c hc
      rwa [List.length_map] at this

theorem testBit_nzMask (u w : Nat) : ∀ CS : List (List Nat),
    (nzMask CS u).testBit w = CS.any fun cs => (Native.actM cs u).testBit w
  | [] => by simp [nzMask]
  | cs :: CS => by
    have ih := testBit_nzMask u w CS
    unfold nzMask at ih ⊢
    rw [List.foldr_cons, Nat.testBit_or, ih, List.any_cons]

theorem nzMask_lt {N : Nat} (u : Nat) : ∀ CS : List (List Nat),
    (∀ cs ∈ CS, ∀ c ∈ cs, c < 2 ^ N) → nzMask CS u < 2 ^ N
  | [], _ => Nat.two_pow_pos N
  | cs :: CS, h => by
    have ih := nzMask_lt u CS fun x hx => h x (List.mem_cons_of_mem cs hx)
    unfold nzMask at ih ⊢
    rw [List.foldr_cons]
    exact Nat.or_lt_two_pow (actM_lt cs (h cs List.mem_cons_self) u) ih

theorem lTabs_lt : ∀ a ∈ Native.lTabs, ∀ x ∈ a.toList, x < 24 := by decide

theorem toddVals_length : ∀ V ∈ toddVals, V.length = 2048 := by
  intro V hV
  rw [toddVals, List.mem_cons] at hV
  rcases hV with h | h
  · rw [h, List.length_range]
  · obtain ⟨a, -, ha⟩ := List.mem_map.1 h
    rw [← ha, List.length_map, List.length_range]

theorem cols_lt : ∀ cs ∈ toddVals.map (colsOf 11), ∀ c ∈ cs, c < 2 ^ 2048 := by
  intro cs hcs c hc
  obtain ⟨V, hV, rfl⟩ := List.mem_map.1 hcs
  have := colsOf_lt 11 V c hc
  rwa [toddVals_length V hV] at this

theorem kerMask_lt (u : Nat) : kerMask (toddVals.map (colsOf 11)) u < 2 ^ 2048 :=
  Nat.xor_lt_two_pow (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos) (nzMask_lt u _ cols_lt)

theorem tab_getElem! (a : Array Nat) {w : Nat} (hw : w < 2048) :
    ((Array.range 2048).map (Native.toddAct a))[w]! = Native.toddAct a w := by
  rw [getElem!_pos _ _ (by simpa using hw)]
  simp

theorem toddOrth_eq (u x : Nat) : Native.toddOrth u x = !xorBits 11 (u &&& x) :=
  toddEven_eq 11 _

theorem testBit_kerMask (u : Nat) {w : Nat} (hw : w < 2048) :
    (kerMask (toddVals.map (colsOf 11)) u).testBit w =
      Native.toddKerT (Native.toddActTabs ()) u w := by
  unfold kerMask full2048
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, testBit_nzMask, List.any_map]
  simp only [decide_eq_true hw, Bool.true_xor]
  unfold Native.toddKerT Native.toddActTabs
  rw [List.all_map, toddOrth_eq]
  have hl : ∀ a ∈ Native.lTabs,
      (Native.actM (colsOf 11 ((List.range 2048).map (toddActF (imgTab a.toList)))) u).testBit w =
        !Native.toddOrth u ((Array.range 2048).map (Native.toddAct a))[w]! := by
    intro a ha
    rw [testBit_actM_colsOf _ _ _ _ (by simpa using hw), getD_map_lt _ (by simpa using hw),
      getD_range hw, tab_getElem! a hw, toddOrth_eq, Bool.not_not]
    unfold toddActF Native.toddAct
    rw [img_eq_imgF a (lTabs_lt a ha)]
  have h0 := testBit_actM_colsOf 11 (List.range 2048) u w (by simpa using hw)
  rw [getD_range hw] at h0
  unfold toddVals
  simp only [List.any_cons, List.any_map, Function.comp_apply]
  rw [h0]
  revert hl
  simp only [Native.lTabs, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, List.any_cons, List.any_nil, List.all_cons, List.all_nil, Function.comp_apply]
  rintro ⟨h1, h2, h3, h4⟩
  rw [h1, h2, h3, h4]
  cases xorBits 11 (u &&& w) <;> simp

theorem testBit_badMask (br : List Nat) {w : Nat} (hw : w < 2048) :
    (badMask br).testBit w = !Native.toddOctsKer br w := by
  rw [badMask, testBit_packBits, getD_map_lt _ (by simpa using hw), getD_range hw]

theorem count_gen {n N K : Nat} (hnN : n ≤ N) (hK : K < 2 ^ n) (p : Nat → Bool)
    (hp : ∀ w < n, K.testBit w = p w) :
    ((List.range n).filter p).length = ((List.range N).filter fun v => K.testBit v).length := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnN
  rw [List.range_add, List.filter_append, List.length_append]
  have e : ((List.range m).map (n + ·)).filter (fun v => K.testBit v) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hK
      (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp
  rw [e, List.length_nil, Nat.add_zero,
    List.filter_congr fun w hw => (hp w (List.mem_range.1 hw)).symm]

theorem count_eq {K : Nat} (hK : K < 2 ^ 2048) (p : Nat → Bool)
    (hp : ∀ w < 2048, K.testBit w = p w) :
    ((List.range 2048).filter p).length = popcM swarK K :=
  (count_gen (N := 4096) (by decide) hK p hp).trans (popcM_swarK_proved
    (Nat.lt_of_lt_of_le hK (Nat.pow_le_pow_right (by decide) (by decide)))).symm

theorem all_eq {K B : Nat} (hK : K < 2 ^ 2048) (p q : Nat → Bool)
    (hp : ∀ w < 2048, K.testBit w = p w) (hq : ∀ w < 2048, B.testBit w = !q w) :
    ((List.range 2048).all fun w => !(p w) || q w) = (K &&& B == 0) := by
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro w
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hw : w < 2048
    · have := h w (List.mem_range.2 hw)
      rw [hp w hw, hq w hw]
      cases hpw : p w <;> cases hqw : q w <;> simp_all
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hK
        (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp
  · intro h w hw
    have hw' := List.mem_range.1 hw
    have := congrArg (fun x => x.testBit w) h
    simp only [Nat.testBit_and, Nat.zero_testBit, hp w hw', hq w hw'] at this
    cases hpw : p w <;> cases hqw : q w <;> simp_all

theorem toddUniqRow_eq (u : Nat) :
    Native.toddUniqRow (Native.toddActTabs ()) (Native.octsT Native.baseTrio) u =
      uniqRowF (toddVals.map (colsOf 11)) (badMask (Native.octsT Native.baseTrio)) u := by
  unfold Native.toddUniqRow uniqRowF
  rw [count_eq (kerMask_lt u) _ fun w hw => testBit_kerMask u hw,
    all_eq (kerMask_lt u) _ _ (fun w hw => testBit_kerMask u hw)
      (fun w hw => testBit_badMask _ hw)]

theorem toddUniqCheck_eq : Native.toddUniqCheck () = toddUniqF := by
  unfold Native.toddUniqCheck Native.toddUniqLoop toddUniqF uniqLoopF
  simp only [toddUniqRow_eq]

theorem toddIntCheck_eq :
    Native.toddIntCheck () = toddIntCk (Native.trioList ()) (Native.sextList ()) := rfl

theorem toddSextCheck_of {SL : List (List Nat)} (hS : Native.sextList () = SL.toArray)
    (h : toddSextCk SL = true) : Native.toddSextCheck () = true := by
  unfold toddSextCk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0, hlen⟩, hall⟩ := h
  unfold Native.toddSextCheck Native.toddSextLoop Native.allLt
  rw [hS, ← hlen]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨h0, ?_⟩
  rw [← hall]
  exact range_all_eq_allIdx SL (fun q s => q == 0 ||
    ((List.range 2048).filter (Native.toddOctsKer (Native.octsS SL.toArray[0]!))).any
      fun w => !(Native.toddOctsKer (Native.octsS s) w))

end CFSG.KC.M24G
