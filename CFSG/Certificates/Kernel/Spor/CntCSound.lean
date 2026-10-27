module

public import Certificates.Data.Kernel.Spor.CntC
public import CFSG.Sporadic.SmallOddCore.J2CentralizerDInputs
import CFSG.Certificates.Kernel.SporSch.Cnt3Proof
import CFSG.Certificates.Kernel.SporSch.HeSrchLemmas
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.PairNative

section CntC

open CFSG.Monster.B.Co2

private theorem cntC3_eq (n w : Nat) (LR TR : Nat → Nat) (DP : List Nat) (k0 : Nat) :
    cntC3 n w LR TR DP k0 = ∑ k1 ∈ Finset.range (rcnt (LR 1)), ∑ k2 ∈ Finset.range (rcnt (LR 2)),
      if commK n w DP [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
        trK n (Nat.mul n w) LR TR 0 k0] = true then 1 else 0 := by
  unfold cntC3
  simp only [strictN_val]
  refine (Tab.foldUp_add _ (fun k1 _ s => ?_) 0).trans (Nat.zero_add _)
  exact Tab.foldUp_add (fun k2 => if commK n w DP [trK n (Nat.mul n w) LR TR 2 k2,
    trK n (Nat.mul n w) LR TR 1 k1, trK n (Nat.mul n w) LR TR 0 k0] = true then 1 else 0)
    (fun k2 _ s => Tab.nIf_succ _ s) s

private theorem commK_eq {n w : Nat} {Ws : List Nat} (hW : Cnt3P.RangeL n w Ws) :
    ∀ {DP : List Nat}, Cnt3P.RangeL n w DP →
      commK n w DP Ws = CFSG.Sporadic.SmallOddCore.commW n (DP.map (Raw.unpack n w))
        (Ws.map (Raw.unpack n w))
  | [], _ => rfl
  | g :: DP, hD => by
    change bAnd(allN n (fun i => Nat.beq (evRK w Ws (pg w (mask w) g i))
      (pg w (mask w) g (evRK w Ws i))), commK n w DP Ws) = _
    rw [Cnt3P.bAnd_and, commK_eq hW (fun V hV => hD V (List.mem_cons_of_mem _ hV))]
    simp only [CFSG.Sporadic.SmallOddCore.commW, List.map_cons, List.all_cons]
    congr 1
    apply Bool.eq_iff_iff.2
    rw [Raw.Orb.allN_iff, allLt_iff]
    refine forall₂_congr fun i hi => ?_
    have hg := hD g List.mem_cons_self i hi
    have e1 := Cnt3P.evRK_eq hW _ hg
    have e2 := Cnt3P.evRK_eq hW i hi
    rw [Raw.Orb.unpack_get hi, ← e1.1, ← e2.1, Raw.Orb.unpack_get e2.2]
    simp only [beq_iff_eq]
    exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

private theorem commW_ag {n : Nat} {gs W W' : List (Array Nat)} (hg : ∀ g ∈ gs, ∀ i < n, g[i]! < n)
    (h : Cnt3P.WAg n W W') :
    CFSG.Sporadic.SmallOddCore.commW n gs W = CFSG.Sporadic.SmallOddCore.commW n gs W' := by
  unfold CFSG.Sporadic.SmallOddCore.commW
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, allLt_iff, beq_iff_eq]
  refine forall₂_congr fun g hg' => forall₂_congr fun i hi => ?_
  rw [(h _ (hg g hg' i hi)).1, (h i hi).1]

end CntC

theorem cntC3_sound {n w kS BP : Nat} {PS PSI LR TR TRI CS : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {DP : List Nat}
    (hb : Binds n w PS kS 3 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hD : canonL n w DP = true)
    (h : ∀ k0 < rcnt (LR 0), cntC3 n w LR TR DP k0 = CS k0) :
    countW (CFSG.Sporadic.SmallOddCore.commW n (DP.map (unpack n w)))
        (blocksOf n (rawLevels n S base) [[0], [1, 2]]) [] =
      sumN (rcnt (LR 0)) CS := by
  have hD' := Cnt3P.rangeL_of_canonL hD
  have hgs : ∀ g ∈ DP.map (Raw.unpack n w), ∀ i < n, g[i]! < n := by
    intro g hg i hi
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hg
    rw [Raw.Orb.unpack_get hi]
    exact hD' d hd i hi
  have hs := fun i (hi : i < 3) => (Cnt3P.lev_agree hb hp hl hi).1
  rw [Cnt3P.countW_blocks, hs 0 (by norm_num), hs 1 (by norm_num), hs 2 (by norm_num), sumN_eq,
    Tab.lsum]
  refine Finset.sum_congr rfl fun k0 hk0 => ?_
  rw [Finset.mem_range] at hk0
  rw [← h k0 hk0, cntC3_eq]
  refine Finset.sum_congr rfl fun k1 hk1 => Finset.sum_congr rfl fun k2 hk2 => ?_
  rw [Finset.mem_range] at hk1 hk2
  have hK : Cnt3P.RangeL n w [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
      trK n (Nat.mul n w) LR TR 0 k0] := by
    intro W hW q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl | rfl
    · exact ((Cnt3P.lev_agree hb hp hl (i := 2) (by norm_num)).2 k2 hk2 q hq).2
    · exact ((Cnt3P.lev_agree hb hp hl (i := 1) (by norm_num)).2 k1 hk1 q hq).2
    · exact ((Cnt3P.lev_agree hb hp hl (i := 0) (by norm_num)).2 k0 hk0 q hq).2
  rw [commW_ag hgs (Cnt3P.word_ag hb hp hl hk0 hk1 hk2), commK_eq hK hD']

end CFSG.KS.SporSch

end
