module

public import Certificates.Data.Kernel.Spor.RawSlP
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

theorem lvSlKP_append (n w m nw : Nat) (S SI TR TRI : Nat → Nat) (kS T R lo a b : Nat)
    (h1 : lvSlKP n w m nw S SI TR TRI kS T R lo a = true)
    (h2 : lvSlKP n w m nw S SI TR TRI kS T R (lo + a) b = true) :
    lvSlKP n w m nw S SI TR TRI kS T R lo (a + b) = true := by
  unfold lvSlKP at h1 h2 ⊢
  refine allN_of_forall fun d hd => ?_
  rcases Nat.lt_or_ge d a with hda | hda
  · exact allN_spec h1 d hda
  · have e : Nat.add (lo + a) (d - a) = Nat.add lo d := by
      change lo + a + (d - a) = lo + d
      omega
    have h := allN_spec h2 (d - a) (by omega)
    rw [e] at h
    exact h

end CFSG.KS.Raw

end
