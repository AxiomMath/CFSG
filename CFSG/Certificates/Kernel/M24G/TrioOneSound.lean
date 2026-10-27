module

public import Certificates.Data.Kernel.M24G.TrioOne
public import CFSG.Certificates.Kernel.M24G.ImgSound
public import CFSG.Certificates.Kernel.M24G.ListsSound

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

theorem compose_toArray (a b : List Nat) :
    Native.compose a.toArray b.toArray = (composeL a b).toArray := by
  apply Array.toList_inj.1
  simp [Native.compose, composeL, toArray_getElem!_eq_getD]

theorem foldl_toArray {β : Type} (f : Array Nat → β → Array Nat) (g : List Nat → β → List Nat)
    (hfg : ∀ x b, f x.toArray b = (g x b).toArray) :
    ∀ (l : List β) (x : List Nat), l.foldl f x.toArray = (l.foldl g x).toArray
  | [], _ => rfl
  | b :: l, x => by
    rw [List.foldl_cons, List.foldl_cons, hfg]
    exact foldl_toArray f g hfg l _

theorem prodTab_eq (s : Nat) : Native.prodTab s = (prodL s).toArray := by
  unfold Native.prodTab prodL
  have e : Native.r121IdTab = Native.r121IdTab.toList.toArray := rfl
  rw [e]
  refine foldl_toArray _ _ (fun x j => ?_) _ _
  split
  · rw [← compose_toArray]
  · rfl

theorem toArray_beq (l : List Nat) (A : Array Nat) : (l.toArray == A) = (l == A.toList) := by
  rcases A with ⟨A⟩
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, List.toList_toArray]
  exact ⟨fun h => by simpa using congrArg Array.toList h, fun h => by rw [h]⟩

theorem groupCheck_of (h : groupL = true) : Native.groupCheck () = true := by
  unfold groupL at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := h
  unfold Native.groupCheck Native.genTabCheck Native.mulTabCheck Native.distinctTabCheck
  simp only [prodTab_eq, compose_toArray, toArray_beq, toArray_getElem!_eq_getD, Bool.and_eq_true,
    List.toList_toArray]
  exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem prodL_lt (hg : groupL = true) {s : Nat} (hs : s < 64) : ∀ x ∈ prodL s, x < 24 := by
  unfold groupL at hg
  simp only [Bool.and_eq_true] at hg
  have h5 := (range_all_iff _ _).1 hg.2 s hs
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h5
  exact h5.2

theorem img_prod (hg : groupL = true) {s : Nat} (hs : s < 63) (o : Nat) :
    Native.img (Native.prodTab (s + 1)) o = imgF (imgTab (prodL (s + 1))) o := by
  have hlt : ∀ x ∈ (prodL (s + 1)).toArray.toList, x < 24 := by
    rw [List.toList_toArray]
    exact prodL_lt hg (by omega)
  rw [prodTab_eq, img_eq_imgF _ hlt, List.toList_toArray]

theorem exists_wit {bs : List (Nat × Nat × Nat)} {SL : List (List Nat)} {tr : Nat × Nat × Nat}
    {ws : List Nat} {b : Nat × Nat × Nat} (hw : fixWitOK bs SL tr ws = true)
    (hs : b ∈ fixingL bs tr) : ∃ q, witOK b SL tr q = true := by
  unfold fixWitOK at hw
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hw
  obtain ⟨hlen, hall⟩ := hw
  obtain ⟨i, hi, hsi⟩ := List.getElem_of_mem hs
  have hz : i < ((fixingL bs tr).zip ws).length := by
    rw [List.length_zip]
    omega
  have h := hall _ (List.getElem_mem hz)
  simp only [List.getElem_zip] at h
  exact ⟨_, hsi ▸ h⟩

theorem trio_ok (hg : groupL = true) {SL : List (List Nat)} (hSl : SL.length = 1771)
    (tr : Nat × Nat × Nat) (ws : List Nat) (hw : fixWitOK prodBs SL tr ws = true)
    (row0 : List Nat)
    (hrow0 : ∀ q < 1771, Native.trioIn Native.baseTrio (SL.getD q []) = true → q ∈ row0) :
    (((List.range 63).map fun s => Native.prodTab (s + 1)).filter
        (fun t => (Native.octsT tr).all fun o => Native.img t o == o)).all
      (fun t => !(((List.range 1771).filter fun q => Native.trioIn tr (SL.getD q [])).all
          fun q => (SL.getD q []).all fun x => (SL.getD q []).contains (Native.img t x)) ||
        row0.any fun q =>
          ((List.range 1771).filter fun q => Native.trioIn tr (SL.getD q [])).contains q) =
      true := by
  rw [List.filter_map, List.all_map, List.all_eq_true]
  intro s hs
  obtain ⟨hs63, hfix⟩ := List.mem_filter.1 hs
  have hs63' := List.mem_range.1 hs63
  simp only [Function.comp_apply, img_prod hg hs63'] at hfix ⊢
  have hb : imgTab (prodL (s + 1)) ∈ prodBs := List.mem_map.2 ⟨s, hs63, rfl⟩
  have hsf : imgTab (prodL (s + 1)) ∈ fixingL prodBs tr := List.mem_filter.2 ⟨hb, hfix⟩
  obtain ⟨q, hq⟩ := exists_wit hw hsf
  unfold witOK at hq
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hq
  obtain ⟨⟨hqlt, hin⟩, hcase⟩ := hq
  have hq' : q < 1771 := hSl ▸ hqlt
  have hqrow : q ∈ (List.range 1771).filter fun q => Native.trioIn tr (SL.getD q []) :=
    List.mem_filter.2 ⟨List.mem_range.2 hq', hin⟩
  rw [Bool.or_eq_true]
  rcases hcase with hb | hb
  · right
    exact List.any_eq_true.2 ⟨q, hrow0 q hq' hb, by simpa using hqrow⟩
  · left
    rw [Bool.not_eq_true', List.all_eq_false]
    refine ⟨q, hqrow, ?_⟩
    rw [hb]
    exact Bool.false_ne_true

theorem fixCopCheck_of {TL : List (Nat × Nat × Nat)} {SL : List (List Nat)} {W : List (List Nat)}
    (hg : groupL = true) (hT : Native.trioList () = TL.toArray)
    (hS : Native.sextList () = SL.toArray) (hTl : TL.length = 3795) (hSl : SL.length = 1771)
    (h0 : TL.getD 0 default = Native.baseTrio) (hw : fixCopW prodBs TL SL W = true) :
    Native.fixCopCheck () = true := by
  unfold Native.fixCopCheck Native.sextsOfTrio
  rw [hT, hS]
  simp only [toArray_getElem!_eq_getD, h0, Native.nTrio, Native.nSext]
  rw [range_all_iff]
  intro p hp
  unfold fixCopW at hw
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hw
  obtain ⟨hlen, hall⟩ := hw
  have hz : p < (TL.zip W).length := by
    rw [List.length_zip]
    omega
  have hwp := hall _ (List.getElem_mem hz)
  simp only [List.getElem_zip] at hwp
  have e : TL.getD p default = TL[p] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : p < TL.length),
      Option.getD_some]
  rw [e, Bool.or_eq_true]
  right
  exact trio_ok hg hSl _ _ hwp _ fun q hq h => List.mem_filter.2 ⟨List.mem_range.2 hq, h⟩

end CFSG.KC.M24G
