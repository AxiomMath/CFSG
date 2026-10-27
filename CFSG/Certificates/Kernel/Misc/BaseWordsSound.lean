module

public import Certificates.Data.Kernel.Misc.BaseWords
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Quasithin.Vol2.KGFactC31WordBasis

public section

namespace CFSG.KC.Misc.BaseWords

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31.Native

variable {n w : Nat}

theorem unpack_getElem (t q : Nat) :
    (unpack n w t)[q]! = nIf(Nat.blt q n, pg w (mask w) t q, 0) := by
  by_cases h : q < n
  · have hb : Nat.blt q n = true := Nat.blt_eq.mpr h
    rw [getElem!_pos _ q (by simpa [unpack] using h), hb]
    simp [unpack]
  · rw [getElem!_neg _ q (by simpa [unpack] using h)]
    have : Nat.blt q n = false := by
      cases hb : Nat.blt q n
      · rfl
      · exact absurd (Nat.blt_eq.mp hb) h
    rw [this]
    rfl

theorem evR_map : ∀ (W : List Nat) (p : Nat), evR (W.map (unpack n w)) p = evK n w W p
  | [], _ => rfl
  | t :: W, p => by
    change evR (W.map (unpack n w)) ((unpack n w t)[p]!) =
      evK n w W (nIf(Nat.blt p n, pg w (mask w) t p, 0))
    rw [unpack_getElem, evR_map W]

theorem evPow_map (W : List Nat) : ∀ (e p : Nat), evPow (W.map (unpack n w)) e p = evPowK n w W e p
  | 0, _ => rfl
  | e + 1, p => by
    change evR (W.map (unpack n w)) (evPow (W.map (unpack n w)) e p) = evK n w W (evPowK n w W e p)
    rw [evPow_map W e p, evR_map]

theorem fixB_map (bs W : List Nat) (e : Nat) :
    fixB bs (W.map (unpack n w)) e = fixBK n w bs W e := by
  unfold fixB fixBK
  congr 1
  funext b
  rw [evPow_map]
  cases h : Nat.beq (evPowK n w W e b) b
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

theorem baseImgs_map (bs W : List Nat) :
    baseImgs bs (W.map (unpack n w)) = baseImgsK n w bs W := by
  unfold baseImgs baseImgsK
  congr 1
  funext p
  exact evR_map W p

theorem spanAddW_map (bs : List Nat) (sp : List (List Nat)) (o : List Nat) :
    spanAddW bs (sp.map (List.map (unpack n w))) (o.map (unpack n w)) =
      (spanAddWK n w bs sp o).map (List.map (unpack n w)) := by
  unfold spanAddW spanAddWK
  have e : ((sp.map (List.map (unpack n w))).any fun e =>
      baseImgs bs e == baseImgs bs (o.map (unpack n w))) =
      sp.any fun e => baseImgsK n w bs e == baseImgsK n w bs o := by
    rw [List.any_map]
    congr 1
    funext e
    simp only [Function.comp_def, baseImgs_map]
  rw [e]
  split_ifs
  · rfl
  · simp [List.map_append, List.map_map, Function.comp]

theorem spanW_fold (bs : List Nat) : ∀ (os : List (List Nat)) (sp : List (List Nat)),
    (os.map (List.map (unpack n w))).foldl (spanAddW bs) (sp.map (List.map (unpack n w))) =
      (os.foldl (spanAddWK n w bs) sp).map (List.map (unpack n w))
  | [], _ => rfl
  | o :: os, sp => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, spanAddW_map, spanW_fold bs os]

theorem spanW_map (bs : List Nat) (os : List (List Nat)) :
    spanW bs (os.map (List.map (unpack n w))) = (spanWK n w bs os).map (List.map (unpack n w)) :=
  spanW_fold bs os [[]]

theorem inSpanW_map (bs : List Nat) (sp cand : List (List Nat)) :
    inSpanW bs (sp.map (List.map (unpack n w))) (cand.map (List.map (unpack n w))) =
      inSpanWK n w bs sp cand := by
  unfold inSpanW inSpanWK
  rw [List.all_map]
  congr 1
  funext x
  simp only [Function.comp_def, List.any_map, baseImgs_map]

theorem normsW_map (bs B : List Nat) (g gi : Nat) :
    normsW bs (B.map (unpack n w)) (unpack n w g) (unpack n w gi) = normsWK n w bs B g gi := by
  unfold normsW normsWK
  have e1 : ((B.map (unpack n w)).map fun b => [b]) =
      (B.map fun b => [b]).map (List.map (unpack n w)) := by
    simp [List.map_map, Function.comp]
  have e2 : ((B.map (unpack n w)).map fun b => [unpack n w gi, b, unpack n w g]) =
      (B.map fun b => [gi, b, g]).map (List.map (unpack n w)) := by
    simp [List.map_map, Function.comp]
  rw [e1, e2, spanW_map, inSpanW_map]

end CFSG.KC.Misc.BaseWords

end
