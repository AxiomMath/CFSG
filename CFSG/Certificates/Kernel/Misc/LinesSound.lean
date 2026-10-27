module

public import CFSG.Certificates.Kernel.Misc.LinesPerp
import CFSG.Certificates.Kernel.Misc.LinesAlg
import CFSG.Certificates.Kernel.Misc.LinesSpec
import CFSG.Certificates.Kernel.Misc.LinesOKList

public section

set_option maxRecDepth 100000

namespace CFSG.KC.Misc.Lines

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46

@[expose] def lineFG (U : Array Nat) (NT S2 S3 : Array Nat) (x y : Nat) : Array Nat :=
  let cx := U[x]!
  let cy := U[y]!
  #[x, y, (uPosG U)[NT[cx ^^^ cy]!]!, (uPosG U)[NT[cx ^^^ S2[cy]!]!]!,
    (uPosG U)[NT[cx ^^^ S3[cy]!]!]!]

@[expose] def lineTabG (U : Array Nat) (P : Array Flags) : Array (Array Nat) :=
  Array.ofFn (n := 693 * 693) fun k =>
    if (P[k.val / 693]!)[k.val % 693]! then
      lineFG U (normTab ()) (scaleTab 2) (scaleTab 3) (k.val / 693) (k.val % 693)
    else #[]

@[expose] def perpPerpOKG (U : Array Nat) (P : Array Flags) (pl : Array (Array Nat))
    (LT : Array (Array Nat)) : Bool :=
  let D := pl[0]!
  allIn 0 693 fun q => (P[0]!)[q]! ||
    (let N := D.filter fun w => (P[w]!)[q]!
     N.size == 45 &&
       N.any (fun a => N.any fun b => a != b && (P[a]!)[b]! &&
         LT[a * 693 + b]!.any fun c => c != a && c != b && N.contains c) &&
       N.all (fun a => N.all fun b =>
         a == b || !(P[a]!)[b]! || N.any fun w => (P[w]!)[a]! != (P[w]!)[b]!) &&
       allIn 0 693 fun q' => (P[0]!)[q']! || !(D.all fun w => (P[w]!)[q]! == (P[w]!)[q']!) ||
         q' == q || q' == ap (tvTabsG U)[0]! q)

@[expose] def polarLinesG (U : Array Nat) : Bool :=
  let P := perpTabG U
  let LT := lineTabG U P
  let pl := perpLists P
  let L := lineList P LT
  allIn 0 693 (fun p => pl[p]!.size == 181) && linesOK P pl LT &&
    lineListOK P LT L (lineIdx L) && twinsOK P pl LT && perpPerpOKG U P pl LT

theorem polarLines_eq : polarLinesCertificate () = polarLinesG uPts := rfl

private theorem lineFG_eq {UL : List Nat} {UP PP : Nat} (H : Pts UL UP PP) {x y : Nat}
    (hx : x < 693) (hy : y < 693) :
    lineFG UL.toArray (normTab ()) (scaleTab 2) (scaleTab 3) x y =
      (lineL UP PP x y).toArray := by
  have hx4 := H.lt x hx
  have hy4 := H.lt y hy
  unfold lineFG
  dsimp only
  rw [list_toArray_getElem! UL x, list_toArray_getElem! UL y, scaleTab_get 2 hy4,
    scaleTab_get 3 hy4,
    normTab_get (xor_lt_4096 hx4 hy4), normTab_get (xor_lt_4096 hx4 (scaleC_lt 2 _)),
    normTab_get (xor_lt_4096 hx4 (scaleC_lt 3 _)), H.uPosG_get (normC_lt _),
    H.uPosG_get (normC_lt _), H.uPosG_get (normC_lt _)]
  simp only [lineL, lnP1, lnP2, lnP3, H.fd12 x hx, H.fd12 y hy]

private theorem lineTabG_get {UL : List Nat} {UP PP : Nat} {PB : Nat → Nat} (H : Pts UL UP PP)
    {P : Array Flags} (hP : ∀ x < 693, ∀ y < 693, (P[x]!)[y]! = relB PB x y) :
    ∀ x < 693, ∀ y < 693, (lineTabG UL.toArray P)[x * 693 + y]! =
      if relB PB x y = true then (lineL UP PP x y).toArray else #[] := by
  intro x hx y hy
  unfold lineTabG
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
  have e1 : (x * 693 + y) / 693 = x := by omega
  have e2 : (x * 693 + y) % 693 = y := by omega
  simp only [e1, e2, hP x hx y hy]
  by_cases h : relB PB x y = true
  · rw [if_pos h, if_pos h]
    exact lineFG_eq H hx hy
  · rw [if_neg h, if_neg h]

theorem lines_sound {U : Array Nat} {UL : List Nat} {UP PP : Nat} {PB : Nat → Nat}
    {PL : Nat → List Nat} (hU : U = UL.toArray) (hp : ptsK UL UP = true)
    (hpos : posK UL UP PP = true) (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true)
    (hpl : plK PB PL = true) (hl : ∀ k < 21, linesK UP PP PB PL (33 * k) 33 = true)
    (hc : Nat.beq (lineCnt UP PP PL 0 693) 6237 = true) (ht : twinsK UP PP PB PL = true)
    (hpp : ∀ k < 21, ppK UP PP PB PL (33 * k) 33 = true) :
    polarLinesG U = true := by
  have _hc := hc
  subst hU
  have H := Pts.of hp hpos
  have hplK := plK_spec hpl
  have G : Geom (relB PB) PL (lineL UP PP) :=
    { rel := polarRel_of_kernel H hperp hpl hl
      plmem := fun x hx y => mem_PL_iff hperp hpl hx
      plsorted := fun x hx => (hplK x hx).2.1
      pllen := fun x hx => (hplK x hx).1
      lmem := fun x hx y hy hne hr z => mem_lineL_Ln H hperp hpl hl hx hy hne hr z
      lnodup := fun x hx y hy hxy hr => nodup_lineL hperp hpl hl hx hy hxy hr
      llen := fun x y => rfl }
  have hP : ∀ x < 693, ∀ y < 693, ((perpTabG UL.toArray)[x]!)[y]! = relB PB x y :=
    fun x hx y hy => perpTabG_get rfl hp hpos hperp x hx y hy
  have T : Tabs (perpTabG UL.toArray) (perpLists (perpTabG UL.toArray))
      (lineTabG UL.toArray (perpTabG UL.toArray)) (relB PB) PL (lineL UP PP) :=
    { P_get := hP
      pl_get := perpLists_get _ (relB PB) PL hP G.plmem G.plsorted
      LT_get := lineTabG_get H hP }
  have hL := lineList_data T G
  unfold polarLinesG
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨plSizes_of T G, linesOK_of T G⟩, lineListOK_of T G hL⟩,
    twinsOK_of T G (twinsK_spec H hperp hpl ht)⟩, ?_⟩
  show perpPerpOKT ((tvTabsG UL.toArray)[0]!) _ _ _ = true
  exact perpPerpOKT_of T G _ (t0 UP PP) (fun q hq => ap_tvTabsG_zero H hq)
    (ppK_spec hperp hpl hpp)

end CFSG.KC.Misc.Lines

end
