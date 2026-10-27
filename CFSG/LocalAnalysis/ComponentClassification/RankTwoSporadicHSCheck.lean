
module


public import Certificates.Certificate15000

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HS

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2.Native

theorem hs_check : ∃ (inX inW : Array ℕ → Bool) (d : ConjData),
    (∀ a, validA 100 a = true → inX a = true → hsInP a = true) ∧
    (∀ a, validA 100 a = true → inW a = true →
      (hsInP a || hsInP (compA 100 (hs100Arr 15) a)) = true) ∧
    conjCensusOKW 100 hsPS inX (fun _ => true) inW false false false d #[] = true ∧
    d.xs.all inW = true ∧ d.xs.length = 10 :=
  Certificates.certificate15000

end CFSG.ComponentClassification.RankTwoSporadic.HS
