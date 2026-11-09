module

public import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

theorem rawChainOK0_of_K {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    rawChainOK n (S.extract 0 kO) S base (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)
      0 = true := by
  obtain ⟨hk, hH⟩ := rawHeadOK_of hb hh
  have hd := hd_of_head hk hH
  have hlv : ∀ i < base.size, levelOK n base[i]! (rawSteps n S base i)
      (rawLevels n S base)[i]! = true := fun i hi => by
    rw [rawLevels_get hi]
    exact levelOK_of (levelOKT_bfs (hd.base_lt i hi) (steps_lt hd))
      (levelTrOK_bfs fun j hj => ⟨_, (step_rep hd hj).choose_spec.1⟩)
  have hsc : ∀ i < base.size, CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i
      (rawSteps n S base i) (rawLevels n S base)[i]! 0 = true := fun _ _ => rfl
  change (rawHeadOK n (S.extract 0 kO) S base
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D) &&
    allLt base.size (fun i => levelOK n base[i]! (rawSteps n S base i)
      (rawLevels n S base)[i]!) &&
    allLt base.size (fun i => CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i
      (rawSteps n S base i) (rawLevels n S base)[i]! 0)) = true
  rw [hH, allLt_iff.2 hlv, allLt_iff.2 hsc]
  rfl

end CFSG.KS.Raw.Orb
