module

public import CFSG.Certificates.Kernel.Spor.RawTreeDefs
import CFSG.Certificates.Kernel.Spor.RawSiftB
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Co2

theorem rawHeadK_sound {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    rawHeadOK n (S.extract 0 kO) S base (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D) =
      true :=
  (Orb.rawHeadOK_of hb hh).2

theorem levelTK_sound {n w kS kO nb BP : Nat} {PS PSI LR : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (ht : TreeOK n w PS PSI LR kS nb BP) {i : Nat} (hi : i < nb) :
    levelOKT n base[i]! (rawSteps n S base i) (CFSG.Monster.B.Co2.Native.bfs n base[i]! (rawSteps n S base i)) = true ∧
      (CFSG.Monster.B.Co2.Native.bfs n base[i]! (rawSteps n S base i)).pts.size = rcnt (LR i) := by
  obtain ⟨hk, hH⟩ := Orb.rawHeadOK_of hb hh
  have hd := Orb.hd_of_head hk hH
  obtain ⟨hp, _, _⟩ := Orb.head_facts hh
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hbl : ∀ t < nb, base[t]! < n := fun t ht' => hd.base_lt t (by omega)
  have A := (Orb.agree_treeK hb hp hbl hi (ht i hi).1 (ht i hi).2).2
  rw [CFSG.Certificates.ChainArrays.lev, rawLevels_get (by omega)] at A
  exact ⟨Orb.levelOKT_bfs (hbl i hi) (Orb.steps_lt hd), A.cnt.symm⟩

theorem schBK_sound {n w kS kO nb BP chunks : Nat} {PS PSI LR ST : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (ht : TreeOK n w PS PSI LR kS nb BP) (hst : StepsOK n w PS ST kS nb BP)
    (hsep : Sep n S base) (hs : SchBOK n w nb PS PSI LR ST kS BP) (_hc : 0 < chunks)
    {i : Nat} (hi : i < nb) :
    CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i (rawSteps n S base i) (rawLevels n S base)[i]!
      chunks = true := by
  obtain ⟨hk, hH⟩ := Orb.rawHeadOK_of hb hh
  have hd := Orb.hd_of_head hk hH
  obtain ⟨hp, _, hkS⟩ := Orb.head_facts hh
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hbl : ∀ t < nb, base[t]! < n := fun t ht' => hd.base_lt t (by omega)
  exact Orb.schreierOK_of_schB hb hp hd hb.1 hkS hbl hsep hst
    (Orb.treeAgree_of hb hp hbl ht) hi (hs i hi) chunks

theorem rawChainTK_sound {n w kS kO nb BP chunks : Nat} {PS PSI LR ST : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (ht : TreeOK n w PS PSI LR kS nb BP) (hst : StepsOK n w PS ST kS nb BP)
    (hsep : Sep n S base) (hs : SchBOK n w nb PS PSI LR ST kS BP) (hc : 0 < chunks) :
    rawChainOK n (S.extract 0 kO) S base (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)
      chunks = true := by
  have hH := rawHeadK_sound hb hh
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hperm : ∀ j < S.size, isInvA n S[j]! (rawInvs n S)[j]! = true := by
    unfold rawHeadOK at hH
    simp only [Bool.and_eq_true] at hH
    exact fun j hj => allLt_spec hH.1.1.1.1.2 hj
  have hlv : ∀ i < base.size, levelOK n base[i]! (rawSteps n S base i)
      (rawLevels n S base)[i]! = true := by
    intro i hi
    rw [rawLevels_get hi]
    refine levelOK_of (levelTK_sound hb hh ht (hbs ▸ hi)).1 (levelTrOK_bfs fun j hj => ?_)
    refine rep_of_mem_levelSteps (base := base) (i := i) hperm (t := (rawSteps n S base i)[j]!) ?_
    rw [getElem!_pos _ j hj]
    exact Array.getElem_mem hj
  have hsc : ∀ i < base.size, CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i (rawSteps n S base i)
      (rawLevels n S base)[i]! chunks = true :=
    fun i hi => schBK_sound hb hh ht hst hsep hs hc (hbs ▸ hi)
  change (rawHeadOK n (S.extract 0 kO) S base
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D) &&
    allLt base.size (fun i => levelOK n base[i]! (rawSteps n S base i)
      (rawLevels n S base)[i]!) &&
    allLt base.size (fun i => CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i (rawSteps n S base i)
      (rawLevels n S base)[i]! chunks)) = true
  rw [hH, allLt_iff.2 hlv, allLt_iff.2 hsc]
  rfl

theorem rawOrbitSizesTK_sound {n w kS kO nb BP : Nat} {PS PSI LR : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (ht : TreeOK n w PS PSI LR kS nb BP) :
    rawOrbitSizes n S base = (List.range nb).map fun i => rcnt (LR i) := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  rw [rawOrbitSizes]
  apply List.ext_getElem
  · simp [rawLevels, hbs]
  · intro k h1 h2
    have hk : k < nb := by simpa using h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    have e := rawLevels_get (n := n) (S := S) (hbs ▸ hk : k < base.size)
    rw [getElem!_pos _ k (by simpa [rawLevels, hbs] using hk)] at e
    rw [e]
    exact (levelTK_sound hb hh ht hk).2

end CFSG.KS.Raw

end
