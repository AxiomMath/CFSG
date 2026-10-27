module

public import Certificates.Data.Kernel.Co2R3K
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Sporadic.Co2Rank3.CheckInputs
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
import CFSG.Certificates.Kernel.Co2R3KSnd.OrbReplay
import CFSG.Certificates.Kernel.Co2R3KSnd.Rec
import CFSG.Certificates.Kernel.Fi22Snd.Colour

public section

namespace CFSG.KC.Co2R3.Snd

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Sporadic.Co2Rank3
  CFSG.Sporadic.Co2Rank3.Native CFSG.Sporadic.FischerOddCore.Native
open CFSG.Monster.B.Co2 (allLt_iff)

theorem memK_eq_contains (l : List Nat) (v : Nat) : memK l v = l.contains v := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show Bool.rec (motive := fun _ => Bool) (memK l v) true (Nat.beq a v) = _
    rw [ih, List.contains_cons]
    cases hb : Nat.beq a v
    · have hne : (v == a) = false :=
        beq_eq_false_iff_ne.2 fun e => by rw [e, beq_true rfl] at hb; cases hb
      rw [hne, Bool.false_or]
    · have he : (v == a) = true := beq_iff_eq.2 (beq_t hb).symm
      rw [he, Bool.true_or]

theorem bitK_eq {n d x : Nat} {R M S : Nat → Nat} (hrow : rowOK n d R M S x = true) (q : Nat) :
    bitK (M x) q = decide (q ∈ decodeRow d (R x)) := by
  unfold bitK
  rw [CFSG.KC.Fi22Snd.beq_bit]
  exact CFSG.KC.Fi22Snd.row_mask hrow q

theorem listLabelOK_of_llK {n d a L : Nat} {R M S : Nat → Nat} {good : List Nat}
    (hrow : rowOK n d R M S a = true) (ha : a < n) (h : llK n M a L good = true) :
    listLabelOK n (rowsArr n d R)[a]! (unpack n 12 L) good = true := by
  unfold llK at h
  rw [Orb.strictB_eq] at h
  unfold listLabelOK
  rw [allLt_iff]
  intro x hx
  have e := allN_iff.1 h x hx
  rw [bitK_eq hrow, memK_eq_contains] at e
  rw [CFSG.KC.Fi22Snd.rowsArr_get ha, unpack12_get L hx]
  by_cases hm : x ∈ decodeRow d (R a)
  · rw [decide_eq_true hm] at e
    have e' : good.contains (at12 L x) = true := e
    rw [List.contains_iff_mem.2 hm, e']
    rfl
  · rw [decide_eq_false hm] at e
    have e' : (!(good.contains (at12 L x))) = true := e
    rw [Bool.not_eq_true'] at e'
    have hc : (decodeRow d (R a)).contains x = false := by
      rw [Bool.eq_false_iff]
      exact fun h' => hm (List.contains_iff_mem.1 h')
    rw [hc, e']
    rfl

theorem commonCount_of_ccK {d a b c : Nat} {R M S : Nat → Nat}
    (hra : rowOK 2300 d R M S a = true) (hrb : rowOK 2300 d R M S b = true) (ha : a < 2300)
    (hb : b < 2300) (h : ccK M a b c = true) :
    commonCount (rowsArr 2300 d R)[a]! (rowsArr 2300 d R)[b]! = c := by
  unfold ccK at h
  simp only [Orb.strictB_eq] at h
  rw [← beq_t h, cntK_card, CFSG.KC.Fi22Snd.rowsArr_get ha, CFSG.KC.Fi22Snd.rowsArr_get hb]
  unfold commonCount
  rw [card_fin_eq 2300 (fun v => v ∈ decodeRow d (R a) ∧ v ∈ decodeRow d (R b))]
  exact congrArg Finset.card (Finset.filter_congr fun w _ => by
    rw [bAnd_eq, Bool.and_eq_true, bitK_eq hra, bitK_eq hrb, decide_eq_true_eq,
      decide_eq_true_eq])

private theorem refineT_size (n : Nat) (nbr : Array (List Nat)) (t c : Array Nat)
    (hc : c.size = n) : ∀ k, (refineT n nbr t c k).size = n
  | 0 => hc
  | k + 1 => by
    show (stepT n nbr t (refineT n nbr t c k)).size = n
    unfold stepT
    rw [Array.size_ofFn]

private theorem colourT_size (n : Nat) (nbr : Array (List Nat)) (t : Array Nat) (pre : List Nat)
    (k : Nat) : (colourT n nbr t pre k).size = n :=
  refineT_size n nbr t _ (by unfold initT; rw [Array.size_ofFn]) k

theorem colourLabelOK_of_clabK {n d k T L : Nat} {nbr : Array (List Nat)} {t : Array Nat}
    {R M S : Nat → Nat} {pre roots : List Nat} (hn : n < 4096) (hnbr : nbr = rowsArr n d R)
    (hrow : ∀ x < n, rowOK n d R M S x = true) (hsym : ∀ x < n, ∀ y ∈ nbr[x]!, x ∈ nbr[y]!)
    (ht : t = unpack n 12 T) (hpre : pre.length < 65536) (h : clabK n S T pre k L roots = true) :
    colourLabelOK n (colourT n nbr t pre k) (unpack n 12 L) roots = true := by
  have hc : ∀ v, cgetN n (colourK n S T pre k) v = (colourT n nbr t pre k)[v]! := by
    intro v
    unfold cgetN
    rw [nIf_eq]
    by_cases hv : v < n
    · rw [if_pos (blt_true hv)]
      exact CFSG.KC.Fi22Snd.cget_colourK hn hnbr hrow hsym ht hpre v
    · rw [if_neg (fun h' => hv (blt_t h')),
        getElem!_neg _ _ (by rw [colourT_size]; omega)]
      rfl
  unfold clabK at h
  rw [Orb.strictB_eq] at h
  obtain ⟨h1, h2⟩ := band_true h
  unfold colourLabelOK
  rw [Bool.and_eq_true, allLt_iff, allLt_iff]
  refine ⟨fun x hx => ?_, fun i hi => ?_⟩
  · have e := beq_t (allN_iff.1 h1 x hx)
    rw [hc, hc] at e
    rw [unpack12_get L hx, e]
    exact beq_self_eq_true _
  · rw [allLt_iff]
    intro j hj
    have e := bif_true (allN_iff.1 (allN_iff.1 h2 i hi) j hj)
    by_cases hij : i = j
    · subst hij
      rw [beq_self_eq_true, Bool.true_or]
    · have hne : (colourT n nbr t pre k)[roots.getD i 0]! ≠
          (colourT n nbr t pre k)[roots.getD j 0]! := by
        intro hAB
        have e2 := e.2 (beq_false hij)
        rw [hc, hc, hAB, beq_true rfl] at e2
        exact absurd e2 (by decide)
      rw [beq_eq_false_iff_ne.2 hij, Bool.false_or, bne_iff_ne]
      exact hne

end CFSG.KC.Co2R3.Snd

end
