module

public import CFSG.Certificates.Kernel.Misc.HypSoundLine
public import Certificates.Data.Kernel.Misc.Hyp

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
  CFSG.KC.Misc.O73 CFSG.KS.TW

private theorem fl_get_of_lt {S : Nat} (hS : S < 2 ^ 693) (p : Nat) :
    (fl S)[p]! = S.testBit p := by
  by_cases hp : p < 693
  · exact fl_get S hp
  · have hb : S.testBit p = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hS
        (Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.1 hp)))
    rw [hb, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by rw [fl_size]; exact Nat.le_of_not_lt hp)]
    rfl

private theorem length_filter_cons (a : Nat) (l : List Nat) (p : Nat → Bool) :
    ((a :: l).filter p).length = (if p a = true then 1 else 0) + (l.filter p).length := by
  rw [List.filter_cons]
  by_cases h : p a = true <;> simp [h] <;> omega

private theorem filter_lineL_length (UP PP : Nat) (R x y : Nat) :
    ((lineL UP PP x y).filter (fun p => R.testBit p)).length =
      (if R.testBit x = true then 1 else 0) + (if R.testBit y = true then 1 else 0) +
      (if R.testBit (lnP1 UP PP x y) = true then 1 else 0) +
      (if R.testBit (lnP2 UP PP x y) = true then 1 else 0) +
      (if R.testBit (lnP3 UP PP x y) = true then 1 else 0) := by
  simp only [lineL]
  rw [length_filter_cons, length_filter_cons, length_filter_cons, length_filter_cons,
    length_filter_cons]
  simp only [List.filter_nil, List.length_nil, Nat.add_zero]
  ac_rfl

private theorem cnt5_line3 (UP PP : Nat) (R x y : Nat) :
    rootLK.cnt5 R x y (line3 UP PP x y) =
      (if R.testBit x = true then 1 else 0) + (if R.testBit y = true then 1 else 0) +
      (if R.testBit (lnP1 UP PP x y) = true then 1 else 0) +
      (if R.testBit (lnP2 UP PP x y) = true then 1 else 0) +
      (if R.testBit (lnP3 UP PP x y) = true then 1 else 0) := by
  unfold rootLK.cnt5
  rw [land_shiftRight_one_eq, land_shiftRight_one_eq, land_shiftRight_one_eq,
    land_shiftRight_one_eq, land_shiftRight_one_eq, line3_a, line3_b, line3_c]
  simp only [Nat.add_eq]
  ac_rfl

private theorem filter_lineL_fl (UP PP x y : Nat) {S : Nat} (hS : S < 2 ^ 693) :
    ((lineL UP PP x y).filter (fun p => (fl S)[p]!)).length =
      rootLK.cnt5 S x y (line3 UP PP x y) := by
  have hfun : (fun p => (fl S)[p]!) = (fun p => S.testBit p) := by
    funext p
    exact fl_get_of_lt hS p
  rw [hfun, filter_lineL_length, cnt5_line3]

private theorem rootLK_bits {UP PP : Nat} {HS : Nat → Nat} {PL : Nat → List Nat}
    (hrL : ∀ k < 21, rootLK UP PP HS PL (33 * k) 33 = true) {off : Nat}
    (hoff : off = 0 ∨ off = 1408 ∨ off = 2816) :
    ∀ x < 693, ∀ y ∈ PL x, x < y →
      (rootLK.cnt5 (HS off) x y (line3 UP PP x y) = 0 ∨
        rootLK.cnt5 (HS off) x y (line3 UP PP x y) = 2) := by
  intro x hx y hy hxy
  have hk : x / 33 < 21 := by omega
  have h1 := hrL (x / 33) hk
  unfold rootLK at h1
  simp only [letB_eq] at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (x % 33) (by omega)
  have e : 33 * (x / 33) + x % 33 = x := by omega
  have hbx : Nat.blt x 693 = true := Nat.blt_eq.mpr hx
  have hby : Nat.blt x y = true := Nat.blt_eq.mpr hxy
  simp only [Nat.add_eq, impB_eq] at h2
  rw [e] at h2
  rw [hbx, Bool.not_true, Bool.false_or] at h2
  rw [allL_lqt_iff] at h2
  have h3 := h2 y hy
  rw [hby, Bool.not_true, Bool.false_or] at h3
  rw [allL_lqt_iff] at h3
  have h4 := h3 (HS off) (by rcases hoff with rfl | rfl | rfl <;> simp)
  simp only [letB_eq, orB_eq, Bool.or_eq_true, Nat.beq_eq] at h4
  exact h4

private theorem rootCK_img {TP HS ML : Nat → Nat} (hrC : rootCK TP HS ML = true) {off : Nat}
    (hoff : off = 0 ∨ off = 1408 ∨ off = 2816) {i : Nat} (hi : i < 126) :
    imgP (TP (fd 10 (ML off) i)) (ML off) = HS off := by
  unfold rootCK at hrC
  rw [allL_lqt_iff] at hrC
  have h1 := hrC off (by rcases hoff with rfl | rfl | rfl <;> simp)
  simp only [letB_eq, allN_lqt_iff, Nat.beq_eq, at'_eq] at h1
  exact h1 i hi

private theorem genK_of_tabK {UP : Nat} {TP : Nat → Nat}
    (htab : ∀ k < 21, tabK UP TP (33 * k) 33 = true) {f : Nat} (hf : f < 693) :
    genK UP (at' 12 UP f) (TP f) = true := by
  have h1 := htab (f / 33) (by omega)
  unfold tabK at h1
  simp only [letB_eq] at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (f % 33) (by omega)
  have e : 33 * (f / 33) + f % 33 = f := by omega
  have hb : Nat.blt f 693 = true := Nat.blt_eq.mpr hf
  simp only [Nat.add_eq, impB_eq] at h2
  rw [e] at h2
  rw [hb, Bool.not_true, Bool.false_or] at h2
  exact h2

private theorem rootOKG_of {UL : List Nat} {UP PP : Nat} {PB TP HS ML : Nat → Nat}
    {PL : Nat → List Nat} (hp : ptsK UL UP = true) (hpos : posK UL UP PP = true)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) (hpl : plK PB PL = true)
    (htab : ∀ k < 21, tabK UP TP (33 * k) 33 = true) {off : Nat}
    (hoff : off = 0 ∨ off = 1408 ∨ off = 2816) (hmem : listsP (HS off) (ML off) = true)
    (hrL : ∀ k < 21, rootLK UP PP HS PL (33 * k) 33 = true) (hrC : rootCK TP HS ML = true) :
    rootOKG UL.toArray (perpTabG UL.toArray)
      (lineTabG UL.toArray (perpTabG UL.toArray)) (fl (HS off)) = true := by
  obtain ⟨hRlt, hRmem⟩ := listsP_spec hmem
  have H := Pts.of hp hpos
  have hP : ∀ x < 693, ∀ y < 693,
      ((perpTabG UL.toArray)[x]!)[y]! = bitK (PB x) y :=
    perpTabG_get rfl hp hpos hperp
  unfold rootOKG
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [beq_iff_eq]
    exact fl_size (HS off)
  · rw [allIn_iff']
    intro x _ hx
    rw [allIn_iff']
    intro y _ hy
    by_cases hxy : x < y
    · have hd : decide (x < y) = true := decide_eq_true hxy
      rw [hd, Bool.true_and]
      by_cases hpx : ((perpTabG UL.toArray)[x]!)[y]! = true
      · rw [hpx, Bool.not_true, Bool.false_or]
        have hbit : bitK (PB x) y = true := by rw [← hP x hx y hy]; exact hpx
        have hrel : relB PB x y = true := hbit
        have hyPL : y ∈ PL x := (mem_PL_iff hperp hpl hx).2 ⟨hy, hrel⟩
        have hc := rootLK_bits hrL hoff x hx y hyPL hxy
        have hlen : ((lineTabG UL.toArray (perpTabG UL.toArray))[x * 693 + y]!.toList.filter
              (fun p => (fl (HS off))[p]!)).length =
            rootLK.cnt5 (HS off) x y (line3 UP PP x y) := by
          rw [lineTabG_perp H hP hx hy, if_pos hbit, List.toList_toArray]
          exact filter_lineL_fl UP PP x y hRlt
        rw [hlen, Bool.or_eq_true, beq_iff_eq, beq_iff_eq]
        exact hc
      · have hpx' : ((perpTabG UL.toArray)[x]!)[y]! = false := by
          cases h : ((perpTabG UL.toArray)[x]!)[y]! <;> simp_all
        rw [hpx', Bool.not_false, Bool.true_or]
    · have hd : decide (x < y) = false := decide_eq_false hxy
      rw [hd, Bool.false_and, Bool.not_false, Bool.true_or]
  · rw [List.all_eq_true]
    intro x hxmem
    rw [mem_members_fl] at hxmem
    obtain ⟨hxlt, hxbit⟩ := hxmem
    obtain ⟨i, hi, hxi⟩ := (hRmem x).1 hxbit
    have himg : imgP (TP x) (ML off) = HS off := by
      have h := rootCK_img hrC hoff hi
      rwa [hxi] at h
    have hperm : IsPermN 693 (fd 10 (TP x)) :=
      (genK_spec (genK_of_tabK htab hxlt)).2.1
    have hgtest : ∀ q, (HS off).testBit q = true ↔
        ∃ j < 126, fd 10 (TP x) (fd 10 (ML off) j) = q := by
      intro q
      rw [← himg]
      exact testBit_imgP (TP x) (ML off) q
    have hbit_eq : ∀ q < 693, (HS off).testBit (fd 10 (TP x) q) = (HS off).testBit q := by
      intro q hq
      rw [Bool.eq_iff_iff, hgtest (fd 10 (TP x) q), hRmem q]
      constructor
      · rintro ⟨j, hj, hgj⟩
        have hfj : fd 10 (ML off) j < 693 :=
          lt_of_testBit hRlt ((hRmem _).2 ⟨j, hj, rfl⟩)
        exact ⟨j, hj, hperm.2 (fd 10 (ML off) j) hfj q hq hgj⟩
      · rintro ⟨j, hj, hfj⟩
        exact ⟨j, hj, by rw [hfj]⟩
    rw [allIn_iff']
    intro q _ hq
    have hap : ap ((tvTabsG UL.toArray)[x]!) q = fd 10 (TP x) q :=
      ((tvTabs_TR H htab hxlt).2 q hq).1
    rw [hap, beq_iff_eq, fl_get_of_lt hRlt q, fl_get_of_lt hRlt (fd 10 (TP x) q)]
    exact (hbit_eq q hq).symm

theorem root_sound {UL : List Nat} {UP PP : Nat} {PB TP HS ML : Nat → Nat} {PL : Nat → List Nat}
    (hp : ptsK UL UP = true) (hpos : posK UL UP PP = true)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) (hpl : plK PB PL = true)
    (htab : ∀ k < 21, tabK UP TP (33 * k) 33 = true)
    (hmemK : ∀ k < 4224, listsP (HS k) (ML k) = true)
    (hr1 : HS 0 = rootK UP 1) (hr2 : HS 1408 = rootK UP 2) (hr3 : HS 2816 = rootK UP 3)
    (hrL : ∀ k < 21, rootLK UP PP HS PL (33 * k) 33 = true) (hrC : rootCK TP HS ML = true) :
    rootOKG UL.toArray (perpTabG UL.toArray) (lineTabG UL.toArray (perpTabG UL.toArray))
        (rootFlagsG UL.toArray 1) = true ∧
      rootOKG UL.toArray (perpTabG UL.toArray) (lineTabG UL.toArray (perpTabG UL.toArray))
        (rootFlagsG UL.toArray 2) = true ∧
      rootOKG UL.toArray (perpTabG UL.toArray) (lineTabG UL.toArray (perpTabG UL.toArray))
        (rootFlagsG UL.toArray 3) = true := by
  have H := Pts.of hp hpos
  refine ⟨?_, ?_, ?_⟩
  · rw [rootFlagsG_eq H 1, ← hr1]
    exact rootOKG_of hp hpos hperp hpl htab (Or.inl rfl) (hmemK 0 (by omega)) hrL hrC
  · rw [rootFlagsG_eq H 2, ← hr2]
    exact rootOKG_of hp hpos hperp hpl htab (Or.inr (Or.inl rfl)) (hmemK 1408 (by omega)) hrL hrC
  · rw [rootFlagsG_eq H 3, ← hr3]
    exact rootOKG_of hp hpos hperp hpl htab (Or.inr (Or.inr rfl)) (hmemK 2816 (by omega)) hrL hrC

end CFSG.KC.Misc.Hyp

end
