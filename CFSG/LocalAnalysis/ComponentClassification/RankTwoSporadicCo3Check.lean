
module


public import Certificates.Certificate15002

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co3

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2.Native

theorem co3_check : ∃ (inX inW : Array ℕ → Bool) (d : ConjData),
    (∀ a, validA 276 a = true → inX a = true → co3InP a = true) ∧
    (∀ a, validA 276 a = true → inW a = true →
      (co3InP a || co3InP (compA 276 (idA 276) a)) = true) ∧
    conjCensusOKW 276 co3PS inX (fun _ => true) inW false false false d #[] = true ∧
    d.xs.all inW = true ∧ d.xs.length = 10 :=
  Certificates.certificate15002

end CFSG.ComponentClassification.RankTwoSporadic.Co3
