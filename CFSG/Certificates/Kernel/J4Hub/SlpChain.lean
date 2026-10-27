module

public import CFSG.Certificates.Kernel.J4Hub.RegSound

public section

namespace CFSG.KS.J4Hub

open CFSG.KC.Ord

variable {p d w S T L H CM RM ONE LV HV nb : Nat}

theorem slp_chain (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} (W : Nat → List Nat) (St : Nat → Nat) :
    ∀ n, (∀ j < n, Nat.beq (runSlp RB (mulR p w S d T L H CM RM) (validM p nb L H) ONE (W j) (St j))
      (St (j + 1)) = true) → (∀ j < n, 0 < St (j + 1)) →
      RegsIn p d w S nb L H G RB (St 0) → RegsIn p d w S nb L H G RB (St n)
  | 0, _, _, h0 => h0
  | n + 1, h, hp, h0 =>
    slp_sound' hc hnb (slp_chain hc hnb W St n (fun j hj => h j (Nat.lt_succ_of_lt hj))
      (fun j hj => hp j (Nat.lt_succ_of_lt hj)) h0) (h n (Nat.lt_succ_self n)) (hp n (Nat.lt_succ_self n))

end CFSG.KS.J4Hub

end
