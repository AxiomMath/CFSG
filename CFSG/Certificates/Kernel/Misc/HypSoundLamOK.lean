module

public import CFSG.Certificates.Kernel.Misc.HypSoundLine
public import Certificates.Data.Kernel.Misc.Hyp

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
  CFSG.KC.Misc.O73 CFSG.KS.TW

private theorem hypLamOK_facts {UP PP : Nat} {PB LB : Nat → Nat} {PL : Nat → List Nat}
    {selL : List Nat} (h : lamOKK UP PP PB LB PL selL = true) :
    selL.length = 5 ∧
    (∀ s ∈ selL, s < 693 ∧ s ≠ 0 ∧ bitK (PB 0) s = true) ∧
    (∀ j < 1024, bitK (LB j) 0 = true ∧
      Nat.land (LB j) (Nat.xor (PB 0) (Nat.sub (Nat.shiftLeft 1 693) 1)) = 0) ∧
    (∀ y ∈ PL 0, y ≠ 0 → ∀ j < 1024,
      Nat.land (Nat.sub (lineB UP PP 0 y) 1) (LB j) ≠ 0) := by
  unfold lamOKK at h
  simp only [letB_eq, andB_eq, allL_lqt_iff, allN_lqt_iff, impB_eq, notB_eq,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_false', Nat.beq_eq,
    Nat.blt_eq, lenN_misc_eq, nat_beq_eq_false_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  intro y hy hy0
  rcases h4 y hy with h0 | h0
  · exact absurd h0 hy0
  · exact h0

private theorem hypLamOK_testBit_eq_false_of_land_eq_zero {a b z : Nat} (h : Nat.land a b = 0)
    (ha : a.testBit z = true) : b.testBit z = false := by
  have hc := congrArg (fun n => n.testBit z) h
  rw [Nat.land_eq, Nat.testBit_and, Nat.zero_testBit] at hc
  simpa [ha] using hc

private theorem hypLamOK_testBit_xor_mask {P z n : Nat} (hz : z < n) :
    (Nat.xor P (Nat.sub (Nat.shiftLeft 1 n) 1)).testBit z = !(P.testBit z) := by
  have hmask : (Nat.sub (Nat.shiftLeft 1 n) 1).testBit z = true := by
    have e : Nat.shiftLeft 1 n = 2 ^ n := Nat.one_shiftLeft n
    rw [e]
    have h2 : (Nat.sub (2 ^ n) 1).testBit z = decide (z < n) :=
      Nat.testBit_two_pow_sub_one n z
    rw [h2]
    simp [hz]
  rw [Nat.xor_eq, Nat.testBit_xor, hmask]
  cases P.testBit z <;> rfl

private theorem hypLamOK_testBit_of_land_mask {L P n z : Nat}
    (h : Nat.land L (Nat.xor P (Nat.sub (Nat.shiftLeft 1 n) 1)) = 0)
    (hz : z < n) (hL : L.testBit z = true) : P.testBit z = true := by
  have h1 := hypLamOK_testBit_eq_false_of_land_eq_zero h hL
  rw [hypLamOK_testBit_xor_mask hz] at h1
  cases hp : P.testBit z
  · rw [hp] at h1; exact absurd h1 (by simp)
  · rfl

private theorem hypLamOK_exists_testBit_land {a b : Nat} (h : Nat.land a b ≠ 0) :
    ∃ z, a.testBit z = true ∧ b.testBit z = true := by
  obtain ⟨z, hz⟩ := Nat.exists_testBit_of_ne_zero h
  rw [Nat.land_eq, Nat.testBit_and, Bool.and_eq_true] at hz
  exact ⟨z, hz.1, hz.2⟩

private theorem hypLamOK_allIn_not_or {T S : Nat}
    (h : Nat.land T (Nat.xor S (Nat.sub (Nat.shiftLeft 1 693) 1)) = 0) :
    allIn 0 693 (fun z => !(fl T)[z]! || (fl S)[z]!) = true := by
  rw [allIn_iff']
  intro z _ hz
  cases hb : (fl T)[z]!
  · simp [hb]
  · have hS : (fl S)[z]! = true := by
      rw [fl_get T hz] at hb
      rw [fl_get S hz]
      exact hypLamOK_testBit_of_land_mask h hz hb
    simp [hb, hS]

private theorem hypLamOK_line_any {UL : List Nat} {UP PP : Nat} {PB LB : Nat → Nat}
    {PL : Nat → List Nat} {j : Nat} (H : Pts UL UP PP)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true)
    (hpl : plK PB PL = true)
    (hl : ∀ k < 21, linesK UP PP PB PL (33 * k) 33 = true)
    (hPbit : ∀ x < 693, ∀ y < 693, ((perpTabG UL.toArray)[x]!)[y]! = bitK (PB x) y)
    (hline : ∀ y ∈ PL 0, y ≠ 0 →
      Nat.land (Nat.sub (lineB UP PP 0 y) 1) (LB j) ≠ 0)
    {y : Nat} (hy : y < 693) (hy0 : y ≠ 0) (hpy : (fl (PB 0))[y]! = true) :
    ((lineTabG UL.toArray (perpTabG UL.toArray))[y]!).any
      (fun z => z != 0 && (fl (LB j))[z]!) = true := by
  have hty : (PB 0).testBit y = true := by rwa [fl_get (PB 0) hy] at hpy
  have hrel : relB PB 0 y = true := by rw [relB, bitK_eq_testBit]; exact hty
  have hmem : y ∈ PL 0 := (mem_PL_iff hperp hpl (by norm_num)).2 ⟨hy, hrel⟩
  obtain ⟨z, hz1, hz2⟩ := hypLamOK_exists_testBit_land (hline y hmem hy0)
  have hlineB0 : (lineB UP PP 0 y).testBit 0 = true := by
    rw [lineB_testBit]; simp [lineL]
  have hsub1 : (Nat.sub (lineB UP PP 0 y) 1).testBit z =
      (decide (z ≠ 0) && (lineB UP PP 0 y).testBit z) :=
    testBit_sub_one_of_odd hlineB0 z
  have hz0 : z ≠ 0 := by
    intro h0
    have h2 := hz1
    rw [hsub1, h0] at h2
    simp at h2
  have hlineBz : (lineB UP PP 0 y).testBit z = true := by
    have h2 := hz1
    rw [hsub1] at h2
    simpa [hz0] using h2
  have hzmem : z ∈ lineL UP PP 0 y := (lineB_testBit UP PP 0 y z).1 hlineBz
  have hzlt : z < 693 :=
    ((mem_lineL_iff hperp hpl hl (by norm_num) hy (Nat.pos_of_ne_zero hy0) hrel z).1
      hzmem).1
  have hpb0 : bitK (PB 0) y = true := by rw [bitK_eq_testBit]; exact hty
  have hLT : (lineTabG UL.toArray (perpTabG UL.toArray))[y]! =
      (lineL UP PP 0 y).toArray := by
    have h0 := lineTabG_perp H hPbit (x := 0) (y := y) (by norm_num) hy
    rw [Nat.zero_mul, Nat.zero_add] at h0
    simpa [hpb0] using h0
  rw [hLT, List.any_toArray, List.any_eq_true]
  refine ⟨z, hzmem, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · simpa [bne_iff_ne] using hz0
  · rw [fl_get (LB j) hzlt]; exact hz2

theorem lamOKG_of {UL selL : List Nat} {UP PP : Nat} {PB LB : Nat → Nat} {PL : Nat → List Nat}
    (hp : ptsK UL UP = true) (hpos : posK UL UP PP = true)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) (hpl : plK PB PL = true)
    (hl : ∀ k < 21, linesK UP PP PB PL (33 * k) 33 = true)
    (hlamOK : lamOKK UP PP PB LB PL selL = true) :
    selL.length = 5 ∧ (∀ s ∈ selL, s < 693) ∧
      lamOKG selL.toArray (perpTabG UL.toArray) (lineTabG UL.toArray (perpTabG UL.toArray))
        (Array.ofFn (n := 1024) fun j => fl (LB j)) = true := by
  obtain ⟨hlen, hsel, hLB, hline⟩ := hypLamOK_facts hlamOK
  have H := Pts.of hp hpos
  have hPbit : ∀ x < 693, ∀ y < 693,
      ((perpTabG UL.toArray)[x]!)[y]! = bitK (PB x) y :=
    fun x hx y hy => perpTabG_get rfl hp hpos hperp x hx y hy
  have hp0 : (perpTabG UL.toArray)[0]! = fl (PB 0) := by
    have hperpsize : (perpTabG UL.toArray).size = 693 := by simp [perpTabG]
    have hsz : ((perpTabG UL.toArray)[0]!).size = 693 := by
      rw [getElem!_pos _ _ (by rw [hperpsize]; norm_num)]
      simp [perpTabG, Array.getElem_ofFn]
    apply flags_eq hsz
    intro p hp'
    rw [hPbit 0 (by norm_num) p hp', bitK_eq_testBit]
  refine ⟨hlen, fun s hs => (hsel s hs).1, ?_⟩
  unfold lamOKG
  dsimp only
  rw [hp0]
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [List.size_toArray, hlen]
  · rw [allIn_iff']
    intro i _ hi
    have hiL : i < selL.length := by omega
    have hseli : selL.toArray[i]! = selL[i]'hiL := by
      rw [list_toArray_getElem!]
      exact (List.getElem_eq_getD (h := hiL) 0).symm
    obtain ⟨hlt, hne, hbit⟩ := hsel (selL[i]'hiL) (List.getElem_mem hiL)
    rw [hseli]
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa using hlt
    · simpa [bne_iff_ne] using hne
    · rw [fl_get (PB 0) hlt, ← bitK_eq_testBit]; exact hbit
  · simp
  · rw [allIn_iff']
    intro j _ hj
    have hflj : (Array.ofFn (n := 1024) fun i : Fin 1024 => fl (LB i))[j]! = fl (LB j) := by
      rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; simpa using hj), Array.getElem_ofFn]
    rw [hflj]
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [fl_get (LB j) (by norm_num), ← bitK_eq_testBit]
      exact (hLB j hj).1
    · exact hypLamOK_allIn_not_or (hLB j hj).2
    · rw [allIn_iff']
      intro y _ hy
      by_cases hpy : (fl (PB 0))[y]! = false
      · simp [hpy]
      · have hpyT : (fl (PB 0))[y]! = true := by
          cases h : (fl (PB 0))[y]!
          · exact absurd h hpy
          · rfl
        rw [hpyT]
        by_cases hy0 : y = 0
        · subst hy0; simp
        · rw [Bool.or_eq_true]
          right
          exact hypLamOK_line_any H hperp hpl hl hPbit
            (fun y hy hy0 => hline y hy hy0 j hj) hy hy0 hpyT

end CFSG.KC.Misc.Hyp

end
