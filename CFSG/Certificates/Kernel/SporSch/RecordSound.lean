module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Schreier

theorem origArrs_eq {c : ChainRecord} {kO : ℕ} (hg : c.generators = c.strongGenerators.take kO) :
    c.origArrs = c.strongArrs.extract 0 kO := by
  unfold ChainRecord.origArrs ChainRecord.strongArrs
  rw [List.extract_toArray, hg]
  simp [List.extract_eq_drop_take, List.map_take]

theorem wordArrs_eq {c : ChainRecord} {kO kS : ℕ} (hg : c.generators.length = kO)
    (hd : c.derivations.length + kO = kS) :
    c.wordArrs = CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS c.derivations := by
  unfold ChainRecord.wordArrs CFSG.Sporadic.Schreier.Co3.Native.wordsArr
  apply Array.ext
  · simp [hg]
    omega
  · intro i h1 h2
    simp only [List.getElem_toArray, Array.getElem_ofFn]
    by_cases hi : i < kO
    · rw [if_pos hi, List.getElem_append_left (by simp [hg]; omega)]
      simp
    · have hlt : i - kO < c.derivations.length := by simp [hg] at h1; omega
      rw [if_neg hi, List.getElem_append_right (by simp [hg]; omega),
        List.getD_eq_getElem _ _ hlt]
      simp only [List.length_replicate, hg]

theorem recordOK_of {n w kS kO nb BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {c : ChainRecord} (hg : c.generators = c.strongGenerators.take kO)
    (hgl : c.generators.length = kO) (hd : c.derivations.length + kO = kS)
    (hb : Binds n w PS kS nb BP c.strongArrs c.baseArr)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO c.derivations nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true) :
    recordOK n c 4 = true := by
  unfold recordOK
  rw [origArrs_eq hg, wordArrs_eq hgl hd]
  exact rawChainK_sound hb hh hl hNS hs

theorem recordOrbits_of {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {c : ChainRecord}
    (hb : Binds n w PS kS nb BP c.strongArrs c.baseArr)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) :
    recordOrbits n c = (List.range nb).map fun i => rcnt (LR i) :=
  rawOrbitSizesK_sound hb hp hl

end CFSG.KS.Raw

end
