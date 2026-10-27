module

public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclRClosed
public import CFSG.ClassicalInvolution.ModelFacts.E8D8Adj
public import CFSG.ClassicalInvolution.ModelFacts.E8D8Row
public import CFSG.ClassicalInvolution.ModelFacts.E8D8Conn

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

variable {p f : ℕ} [Fact p.Prime]

theorem e8ClassExcluded_proved (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : E8ClassExcluded p f :=
  e8ClassExcluded_of_three (fun _ _ => fund12Connected_of_five_le p f hq) (e8D8Row' p f)
    (fun _ _ => e8D8NoThreeAdj p f hp2 hq)

end CFSG.ClassicalInvolution.RouteD.TypeE8
