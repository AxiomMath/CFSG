module

public import CFSG.Certificates.Kernel.Misc.HypSoundSearchRun
public import CFSG.Certificates.Kernel.Misc.LinesSpec
import CFSG.Certificates.Kernel.Misc.LinesNative
public import CFSG.Certificates.Kernel.Misc.HypNative

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
  CFSG.KC.Misc.O73 CFSG.KS.TW

private theorem rec_cons_map (l : List Nat) (f : Nat → Nat) :
    List.rec (motive := fun _ => List Nat) [] (fun y _ ih => List.cons (f y) ih) l = l.map f := by
  induction l with
  | nil => rfl
  | cons y t ih =>
    show List.cons (f y)
      (List.rec (motive := fun _ => List Nat) [] (fun y _ ih => List.cons (f y) ih) t) =
      List.cons (f y) (List.map f t)
    rw [ih]

private theorem liK_spec {LB LI : Nat → Nat} (h : ∀ k < 16, liK LB LI (64 * k) 64 = true) :
    (∀ j < 1024, LB j < 2 ^ 693) ∧
    ∀ p < 693, ∀ j < 1024, (liAt LI p).testBit j = (LB j).testBit p := by
  have key : ∀ j < 1024, LB j < 2 ^ 693 ∧
      ∀ p < 693, Bool.rec (motive := fun _ => Bool) (notB (bitK (LB j) p)) (bitK (LB j) p)
        (bitK (liAt LI p) j) = true := by
    intro j hj
    have hk : j / 64 < 16 := by omega
    have h1 := h (j / 64) hk
    unfold liK at h1
    rw [allN_lqt_iff] at h1
    have h2 := h1 (j % 64) (by omega)
    simp only [letB_eq] at h2
    rw [show Nat.add (64 * (j / 64)) (j % 64) = j from Nat.div_add_mod j 64] at h2
    have hjb : Nat.blt j 1024 = true := Nat.blt_eq.mpr hj
    simp only [impB_eq, letB_eq, andB_eq, Bool.and_eq_true, hjb, Bool.not_true,
      Bool.false_or] at h2
    exact ⟨Nat.blt_eq.mp h2.1, allN_lqt_iff.mp h2.2⟩
  refine ⟨fun j hj => (key j hj).1, fun p hp j hj => ?_⟩
  have h5 := (key j hj).2 p hp
  rw [bitK_eq_testBit, bitK_eq_testBit] at h5
  cases hb1 : (liAt LI p).testBit j <;> cases hb2 : (LB j).testBit p <;> simp_all

private theorem nlK_spec {GI : Nat → Nat} {PL NL : Nat → List Nat}
    (h : ∀ k < 21, nlK GI PL NL (33 * k) 33 = true) :
    ∀ x < 693, NL x = (PL x).map (fun y => y + 1024 * fd 10 (GI x) y) := by
  intro x hx
  have hk : x / 33 < 21 := by omega
  have h1 := h (x / 33) hk
  unfold nlK at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (x % 33) (by omega)
  simp only [letB_eq] at h2
  rw [show Nat.add (33 * (x / 33)) (x % 33) = x from Nat.div_add_mod x 33] at h2
  have hxb : Nat.blt x 693 = true := Nat.blt_eq.mpr hx
  simp only [impB_eq, letB_eq, hxb, Bool.not_true, Bool.false_or] at h2
  rw [eqLN_eq, decide_eq_true_eq] at h2
  rw [h2, rec_cons_map]
  congr 1
  funext y
  simp [at'_eq]

set_option maxRecDepth 100000 in
private theorem hypSearchCtx {UL : List Nat} {sel : Array Nat} {UP PP : Nat}
    {PB LB LI GI : Nat → Nat} {PL NL : Nat → List Nat}
    (hp : ptsK UL UP = true) (hpos : posK UL UP PP = true)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) (hpl : plK PB PL = true)
    (hlamT : lamTabG UL.toArray sel = Array.ofFn (n := 1024) fun j => fl (LB j))
    (hli : ∀ k < 16, liK LB LI (64 * k) 64 = true)
    (hgi : ∀ x < 693, TR 693 ((wordInvsG UL.toArray (gWordsG UL.toArray))[x]!) (fd 10 (GI x)))
    (hnl : ∀ k < 21, nlK GI PL NL (33 * k) 33 = true) :
    SearchCtx
      (mkCtxG UL.toArray (perpTabG UL.toArray) (gWordsG UL.toArray) (lamTabG UL.toArray sel))
      PB LB LI GI PL NL := by
  have hliSpec := liK_spec hli
  have hnlSpec := nlK_spec hnl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change (perpTabG UL.toArray)[x]! = fl (PB x)
    apply flags_eq
    · rw [getElem!_pos _ x (by simp [perpTabG]; exact hx)]
      simp [perpTabG]
    · intro p hp'
      rw [perpTabG_get (U := UL.toArray) rfl hp hpos hperp x hx p hp', bitK_eq_testBit]
  · intro x hx
    exact (perpK_spec hperp x hx).1
  · intro x hx
    have hP : ∀ x < 693, ∀ y < 693, ((perpTabG UL.toArray)[x]!)[y]! = relB PB x y :=
      fun x hx y hy => by
        rw [relB]
        exact perpTabG_get (U := UL.toArray) rfl hp hpos hperp x hx y hy
    change (perpLists (perpTabG UL.toArray))[x]! = (PL x).toArray
    exact perpLists_get (perpTabG UL.toArray) (relB PB) PL hP
      (fun x hx y => mem_PL_iff hperp hpl hx)
      (fun x hx => (plK_spec hpl x hx).2.1) x hx
  · intro x hx y
    rw [mem_PL_iff hperp hpl hx, relB, bitK_eq_testBit]
  · change (lamTabG UL.toArray sel).size = 1024
    rw [hlamT]
    simp
  · intro j hj
    change (lamTabG UL.toArray sel)[j]! = fl (LB j)
    rw [hlamT, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro j hj
    exact hliSpec.1 j hj
  · intro p hp'
    change (Array.ofFn (n := 693) (fun q => filterRange
      (fun j => ((lamTabG UL.toArray sel)[j]!)[q.val]!) 1024 []))[p]! =
      filterRange (fun j => ((lamTabG UL.toArray sel)[j]!)[p]!) 1024 []
    rw [getElem!_pos _ p (by simpa using hp'), Array.getElem_ofFn]
  · intro p hp' j hj
    exact hliSpec.2 p hp' j hj
  · intro x hx
    change TR 693 ((wordInvsG UL.toArray (gWordsG UL.toArray))[x]!) (fd 10 (GI x))
    exact hgi x hx
  · intro x hx
    exact hnlSpec x hx

private theorem searchK_extract {PB LB HS LI : Nat → Nat} {NL : Nat → List Nat} {RES j : Nat}
    (h : searchK PB LB HS LI NL RES j 1 = true) (hj : j < 1024) :
    (Nat.beq (at' 13 RES j) 0 = true →
      runK PB LB LI NL 40 (LB j) (PB 0 &&& (LB j ^^^ (2 ^ 693 - 1))) = 1) ∧
    (Nat.beq (at' 13 RES j) 0 = false →
      at' 13 RES j < 4225 ∧
      runK PB LB LI NL 40 (LB j) (PB 0 &&& (LB j ^^^ (2 ^ 693 - 1))) =
        2 + HS (at' 13 RES j - 1)) := by
  unfold searchK at h
  rw [letB_eq, allN_lqt_iff] at h
  have h0 := h 0 (by omega)
  have e : Nat.add j 0 = j := rfl
  simp only [e, letB_eq] at h0
  have hjb : Nat.blt j 1024 = true := Nat.blt_eq.mpr hj
  simp only [impB_eq, letB_eq, hjb, Bool.not_true, Bool.false_or, Nat.beq_eq] at h0
  constructor
  · intro hb
    rw [hb] at h0
    exact Nat.beq_eq.mp h0
  · intro hb
    rw [hb] at h0
    simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, Nat.pred_eq_sub_one] at h0
    exact ⟨Nat.blt_eq.mp h0.1, h0.2⟩

theorem search_sound {UL : List Nat} {sel : Array Nat} {xw yw : List Int} {UP PP RES : Nat}
    {PB HS LB LI GI : Nat → Nat} {PL NL : Nat → List Nat}
    (hp : ptsK UL UP = true) (hpos : posK UL UP PP = true)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) (hpl : plK PB PL = true)
    (hH : hypUnionG UL.toArray xw yw = Array.ofFn (n := 4224) fun j => fl (HS j))
    (hHSlt : ∀ j < 4224, HS j < 2 ^ 693)
    (hdistS : ∀ j < 4224, ∀ j' < 4224, HS j = HS j' → j = j')
    (hlamT : lamTabG UL.toArray sel = Array.ofFn (n := 1024) fun j => fl (LB j))
    (hli : ∀ k < 16, liK LB LI (64 * k) 64 = true)
    (hgi : ∀ x < 693, TR 693 ((wordInvsG UL.toArray (gWordsG UL.toArray))[x]!) (fd 10 (GI x)))
    (hnl : ∀ k < 21, nlK GI PL NL (33 * k) 33 = true)
    (hs : ∀ j < 1024, searchK PB LB HS LI NL RES j 1 = true) :
    searchOK (mkCtxG UL.toArray (perpTabG UL.toArray) (gWordsG UL.toArray) (lamTabG UL.toArray sel))
      (hypUnionG UL.toArray xw yw) (famIndex (hypUnionG UL.toArray xw yw)) 40 = true := by
  have hC := hypSearchCtx hp hpos hperp hpl hlamT hli hgi hnl
  have hHsz : (hypUnionG UL.toArray xw yw).size = 4224 := by rw [hH]; simp
  have hHget : ∀ j < 4224, (hypUnionG UL.toArray xw yw)[j]! = fl (HS j) := by
    intro j hj
    rw [hH, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  unfold searchOK
  rw [allIn_iff']
  intro j _ hj
  dsimp only
  rw [hC.lam j hj, hC.P 0 (by norm_num)]
  have hE : (Array.ofFn (n := 693) fun p : Fin 693 =>
      (fl (PB 0))[p.val]! && !(fl (LB j))[p.val]!) =
      fl (PB 0 &&& (LB j ^^^ (2 ^ 693 - 1))) := by
    apply ofFn_congr'
    intro p
    rw [fl_get (PB 0) p.isLt, fl_get (LB j) p.isLt, Nat.testBit_and, Nat.testBit_xor,
      Nat.testBit_two_pow_sub_one]
    have hp' : decide (p.val < 693) = true := decide_eq_true p.isLt
    rw [hp']
    cases (PB 0).testBit p.val <;> cases (LB j).testBit p.val <;> rfl
  rw [hE]
  have hXlt : PB 0 &&& (LB j ^^^ (2 ^ 693 - 1)) < 2 ^ 693 :=
    Nat.and_lt_two_pow (PB 0) (Nat.xor_lt_two_pow (hC.LB_lt j hj) (by
      have := Nat.two_pow_pos 693; omega))
  have hsme := runK_match hC 40 (LB j) (PB 0 &&& (LB j ^^^ (2 ^ 693 - 1)))
    (hC.LB_lt j hj) hXlt
  have hext := searchK_extract (PB := PB) (LB := LB) (HS := HS) (LI := LI) (NL := NL)
    (RES := RES) (j := j) (hs j hj) hj
  by_cases hbe : Nat.beq (at' 13 RES j) 0 = true
  · have hv := hext.1 hbe
    have hr : hsearch (mkCtxG UL.toArray (perpTabG UL.toArray) (gWordsG UL.toArray)
        (lamTabG UL.toArray sel)) 40 (fl (LB j))
        (fl (PB 0 &&& (LB j ^^^ (2 ^ 693 - 1)))) = some [] := hsme.1 hv
    rw [hr]
    simp
  · have hbe' : Nat.beq (at' 13 RES j) 0 = false := by
      cases hb : Nat.beq (at' 13 RES j) 0
      · rfl
      · exact absurd hb hbe
    obtain ⟨helt, hv⟩ := hext.2 hbe'
    have hee : at' 13 RES j ≠ 0 := by
      intro h0; rw [h0] at hbe'; simp at hbe'
    have hsub : at' 13 RES j - 1 < 4224 := by omega
    have hr : hsearch (mkCtxG UL.toArray (perpTabG UL.toArray) (gWordsG UL.toArray)
        (lamTabG UL.toArray sel)) 40 (fl (LB j))
        (fl (PB 0 &&& (LB j ^^^ (2 ^ 693 - 1)))) = some [fl (HS (at' 13 RES j - 1))] :=
      hsme.2 (HS (at' 13 RES j - 1)) hv
    rw [hr]
    simp only [List.length_cons, List.length_nil, Nat.le_refl, decide_true, List.all_cons,
      List.all_nil, Bool.true_and]
    rw [show findIn (famIndex (hypUnionG UL.toArray xw yw)) 4224
        (packList (members (fl (HS (at' 13 RES j - 1))))) = at' 13 RES j - 1 from by
      rw [show findIn = fun (ix : Std.HashMap (Array UInt64) Nat) (n : Nat) (key : Array UInt64) =>
          ix.getD key n from rfl]
      exact famIndex_getD_key hHsz hHget hHSlt hdistS hsub]
    rw [hHget (at' 13 RES j - 1) hsub]
    simp [hsub]

end CFSG.KC.Misc.Hyp

end
