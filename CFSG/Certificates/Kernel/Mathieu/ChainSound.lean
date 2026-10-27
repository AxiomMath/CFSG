module

public import CFSG.Certificates.Kernel.Spor.RawFam
public import Certificates.Data.Kernel.Mathieu.SylowK
public import CFSG.Monster.B.Mathieu.SylowSound
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KC.MathieuK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Monster.B.Mathieu

theorem bindsL_spec {n w : Nat} {PS : Nat → Nat} :
    ∀ {S : List (List Nat)} {i : Nat}, bindsL n w PS i S = true →
      ∀ j (h : j < S.length), S[j].toArray = unpack n w (PS (i + j))
  | [], _, _, j, h => absurd h (Nat.not_lt_zero j)
  | l :: S, i, hb, j, h => by
    rw [bindsL, Bool.and_eq_true] at hb
    rcases j with _ | j
    · exact toArray_eq_of_bindListK hb.1
    · have := bindsL_spec hb.2 j (by simpa using h)
      rw [List.getElem_cons_succ, this]
      congr 2
      omega

theorem binds_of {n w BP : Nat} {PS : Nat → Nat} {c : ChainRecord} (h0 : 0 < n)
    (h1 : n + 1 < 2 ^ w) (h2 : n < 65536) (hS : bindsL n w PS 0 c.strongGenerators = true)
    (hB : bindFromK w BP c.base 0 = true) :
    Binds n w PS c.strongGenerators.length c.base.length BP c.strongArrs c.baseArr := by
  refine ⟨h0, h1, h2, by simp [ChainRecord.strongArrs], fun j hj => ?_, by
    simp [ChainRecord.baseArr], fun t ht => ?_⟩
  · rw [getElem!_pos _ j (by simpa [ChainRecord.strongArrs] using hj)]
    simp only [ChainRecord.strongArrs, List.getElem_toArray, List.getElem_map]
    rw [bindsL_spec hS j hj, Nat.zero_add]
  · rw [getElem!_pos _ t (by simpa [ChainRecord.baseArr] using ht)]
    simp only [ChainRecord.baseArr, List.getElem_toArray]
    rw [bindFromK_spec hB t ht, Nat.zero_add]

theorem origArrs_eq {c : ChainRecord}
    (hgen : c.strongGenerators.take c.generators.length = c.generators) :
    c.origArrs = c.strongArrs.extract 0 c.generators.length := by
  apply Array.toList_inj.1
  simp only [ChainRecord.origArrs, ChainRecord.strongArrs, Array.toList_extract,
    List.toList_toArray, List.extract_eq_drop_take, List.drop_zero, Nat.sub_zero, ← List.map_take,
    hgen]

theorem wordArrs_eq {c : ChainRecord}
    (hlen : c.generators.length + c.derivations.length = c.strongGenerators.length) :
    c.wordArrs = CFSG.Sporadic.Schreier.Co3.Native.wordsArr c.generators.length
      c.strongGenerators.length c.derivations := by
  apply Array.ext
  · simp [ChainRecord.wordArrs, CFSG.Sporadic.Schreier.Co3.Native.wordsArr, ← hlen]
  · intro j h1 h2
    simp only [ChainRecord.wordArrs, List.getElem_toArray,
      CFSG.Sporadic.Schreier.Co3.Native.wordsArr, Array.getElem_ofFn]
    by_cases hj : j < c.generators.length
    · rw [if_pos hj, List.getElem_append_left (by simpa using hj)]
      simp
    · rw [if_neg hj, List.getElem_append_right (by simpa using hj)]
      have h1' : j < c.generators.length + c.derivations.length := by
        simpa [ChainRecord.wordArrs] using h1
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp

theorem check_of_rawK {n w nb BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat} {c : ChainRecord}
    (hn : 1 ≤ n) (hdeg : c.degree = n)
    (hlen : c.generators.length + c.derivations.length = c.strongGenerators.length)
    (hgen : c.strongGenerators.take c.generators.length = c.generators)
    (hb : Binds n w PS c.strongGenerators.length nb BP c.strongArrs c.baseArr)
    (hnd : c.base.Nodup)
    (hK : RawK n w PS PSI LR TR TRI c.strongGenerators.length c.generators.length c.derivations
      nb BP NS CH) :
    c.check n = true := by
  have hraw := rawK_sound hb hK 1
  rw [← origArrs_eq hgen, ← wordArrs_eq hlen] at hraw
  have hF := CFSG.Certificates.chainCheckFacts hraw
  unfold ChainRecord.check arraysOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨hdeg, hlen⟩, ⟨⟨hn, by simpa [ChainRecord.baseArr] using hnd⟩, ?_⟩, hraw⟩
  refine allLt_iff.2 fun k hk => ?_
  have hk' : k < c.strongArrs.size := Nat.lt_of_lt_of_le hk hF.orig_le
  have hkg : k < c.generators.length := by rwa [c.origArrs_size] at hk
  have e : c.origArrs[k]! = c.strongArrs[k]! := by
    rw [origArrs_eq hgen, getElem!_pos _ k (by simpa using ⟨hkg, hk'⟩), getElem!_pos _ k hk',
      Array.getElem_extract]
    simp
  have := hF.strong_inv k hk'
  rw [rawInvs_get _ hk'] at this
  rw [e]
  exact this

theorem chain_of_K {n w BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat} {c : ChainRecord}
    (hn : 1 ≤ n) (h1 : n + 1 < 2 ^ w) (h2 : n < 65536) (hdeg : c.degree = n)
    (hlen : c.generators.length + c.derivations.length = c.strongGenerators.length)
    (hgen : c.strongGenerators.take c.generators.length = c.generators)
    (hS : bindsL n w PS 0 c.strongGenerators = true) (hB : bindFromK w BP c.base 0 = true)
    (hnd : c.base.Nodup)
    (hK : RawK n w PS PSI LR TR TRI c.strongGenerators.length c.generators.length c.derivations
      c.base.length BP NS CH) :
    c.check n = true ∧ c.orbitSizes n = (List.range c.base.length).map fun i => rcnt (LR i) := by
  have hb := binds_of (by omega) h1 h2 hS hB
  exact ⟨check_of_rawK hn hdeg hlen hgen hb hnd hK,
    rawOrbitSizesK_sound hb (Orb.head_facts hK.1).1 hK.2.1⟩

theorem orbitSizes_of_rawK {n w nb BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {c : ChainRecord} {kO : Nat} {D : List (List Int)}
    (hb : Binds n w PS c.strongGenerators.length nb BP c.strongArrs c.baseArr)
    (hK : RawK n w PS PSI LR TR TRI c.strongGenerators.length kO D nb BP NS CH) :
    c.orbitSizes n = (List.range nb).map fun i => rcnt (LR i) :=
  rawOrbitSizesK_sound hb (Orb.head_facts hK.1).1 hK.2.1

end CFSG.KC.MathieuK

end
