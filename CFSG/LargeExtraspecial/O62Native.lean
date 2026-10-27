module

public import CFSG.LargeExtraspecial.O62Check
public import Certificates.Certificate10001
public meta import CFSG.LargeExtraspecial.O62Check
public meta import CFSG.Fischer.Uniq.CompTau
public meta import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LargeExtraspecial.O62

open Check

theorem checkSylow_plus_ok : checkSylow false = true :=
  Certificates.certificate10001.1

theorem checkSylow_minus_ok : checkSylow true = true :=
  Certificates.certificate10001.2.1

theorem checkRank_plus_ok : checkRank false = true :=
  Certificates.certificate10001.2.2.1

theorem checkRank_minus_ok : checkRank true = true :=
  Certificates.certificate10001.2.2.2.1

theorem checkWC_plus_ok : checkWC false = true :=
  Certificates.certificate10001.2.2.2.2.1

theorem checkWC_minus_ok : checkWC true = true :=
  Certificates.certificate10001.2.2.2.2.2

theorem Check.checkSylow_eq_true : ∀ minus, checkSylow minus = true
  | false => checkSylow_plus_ok
  | true => checkSylow_minus_ok

theorem Check.checkRank_eq_true : ∀ minus, checkRank minus = true
  | false => checkRank_plus_ok
  | true => checkRank_minus_ok

theorem Check.checkWC_eq_true : ∀ minus, checkWC minus = true
  | false => checkWC_plus_ok
  | true => checkWC_minus_ok

end CFSG.LargeExtraspecial.O62
