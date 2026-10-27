module

public import CFSG.Certificates.Kernel.J4Hub.RegSound
public import CFSG.Certificates.Kernel.J4Hub.PcSound
public import CFSG.Certificates.Kernel.J4Hub.FlagSound
public import CFSG.Certificates.Kernel.J4Hub.FixedSound
public import CFSG.Certificates.Kernel.J4Hub.BfsSound
public import CFSG.Certificates.Kernel.J4Hub.PrimSubSound

public section

namespace CFSG.KS.J4Hub

open CFSG.KC.Ord CFSG.KS.Ord Matrix

variable {p d w S T L H CM RM ONE LV HV nb : Nat}

theorem one_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S) :
    validM p nb L H ONE = true ∧ ordMat p d w S ONE = 1 :=
  one_sound' hc hnb

theorem mul_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {A B : Nat} (hA : validM p nb L H A = true) (hB : validM p nb L H B = true) :
    validM p nb L H (mulR p w S d T L H CM RM A B) = true ∧
      ordMat p d w S (mulR p w S d T L H CM RM A B) = ordMat p d w S A * ordMat p d w S B :=
  mul_sound' hc hnb hA hB

theorem ordMat_inj (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {A B : Nat} (hA : validM p nb L H A = true) (hB : validM p nb L H B = true)
    (h : ordMat p d w S A = ordMat p d w S B) : A = B :=
  ordMat_inj' hc hnb hA hB h

theorem ordExact_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {RB : Nat → Nat} {nreg r q : Nat} {ps : List Nat} (hq : q < 65536)
    (hr : validM p nb L H (RB r) = true)
    (h : CFSG.KC.Fam.ordExact RB (mulR p w S d T L H CM RM) ONE nreg r q ps = true) :
    0 < r ∧ r < nreg ∧ ordMat p d w S (RB r) ^ q = 1 ∧ ∀ l ∈ ps, ordMat p d w S (RB r) ^ (q / l) ≠ 1 :=
  ordExact_sound' hc hnb hq hr h

theorem invPairs_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {RB : Nat → Nat} {nreg GR IR Lg : Nat}
    (h : CFSG.KC.Fam.invPairs RB (mulR p w S d T L H CM RM) ONE nreg GR IR Lg = true) :
    ∀ g < Lg, 0 < at16 GR g ∧ at16 GR g < nreg ∧ 0 < at16 IR g ∧ at16 IR g < nreg ∧
      (validM p nb L H (RB (at16 GR g)) = true → validM p nb L H (RB (at16 IR g)) = true →
        ordMat p d w S (RB (at16 GR g)) * ordMat p d w S (RB (at16 IR g)) = 1) :=
  invPairs_sound' hc hnb h

theorem slp_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {Cs : List Nat} {s s' : Nat}
    (hin : RegsIn p d w S nb L H G RB s)
    (h : Nat.beq (runSlp RB (mulR p w S d T L H CM RM) (validM p nb L H) ONE Cs s) s' = true)
    (hs' : 0 < s') : RegsIn p d w S nb L H G RB s' :=
  slp_sound' hc hnb hin h hs'

theorem wordProd_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {RB : Nat → Nat} {GR IR : Nat} {l : List (Nat × Bool)}
    (hv : ∀ x ∈ l, validM p nb L H (CFSG.KC.Fam.letL RB GR IR x) = true) :
    validM p nb L H (CFSG.KC.Fam.wordProd RB (mulR p w S d T L H CM RM) ONE GR IR l ONE) = true ∧
      ordMat p d w S (CFSG.KC.Fam.wordProd RB (mulR p w S d T L H CM RM) ONE GR IR l ONE) =
        (l.map fun x => ordMat p d w S (CFSG.KC.Fam.letL RB GR IR x)).prod :=
  wordProd_sound' hc hnb hv

theorem prime_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {RB : Nat → Nat} {nreg r q : Nat} (hq : q < 65536) (hr : validM p nb L H (RB r) = true)
    (h : primeOK RB (mulR p w S d T L H CM RM) ONE nreg r q = true) :
    ordMat p d w S (RB r) ^ q = 1 ∧ ordMat p d w S (RB r) ≠ 1 :=
  prime_sound' hc hnb hq hr h

theorem conj_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {C Ci X Y : Nat} (hX : validM p nb L H X = true) (hY : validM p nb L H Y = true)
    (h : CFSG.KC.Fam.conjOK (mulR p w S d T L H CM RM) (validM p nb L H) ONE C Ci X Y = true) :
    ordMat p d w S C * ordMat p d w S Ci = 1 ∧
      ordMat p d w S X * ordMat p d w S C = ordMat p d w S C * ordMat p d w S Y :=
  conj_sound' hc hnb hX hY h

theorem fixed_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {RB : Nat → Nat} {nreg v r : Nat} (hr : validM p nb L H (RB r) = true)
    (h : CFSG.KC.Fam.fixedOK RB (vecR p w S d T LV HV RM) (validM p S LV HV) nreg v r = true) :
    ordVec p d w v ᵥ* ordMat p d w S (RB r) = ordVec p d w v :=
  fixed_sound' hc hnb hr h

theorem bfs_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {V : Nat → Nat} {G0 G1 mx sf : Nat} {Cs : List Nat}
    (hV : validM p S LV HV (V 0) = true)
    (hG0 : validM p nb L H G0 = true) (hG1 : validM p nb L H G1 = true)
    (h : Nat.beq (CFSG.KC.Fam.bfsRun V (vecR p w S d T LV HV RM) G0 G1 mx Cs 1) sf = true)
    (hsf : 0 < sf) (hcnt : Nat.land sf 255 = mx) :
    ∀ k < mx, ∃ l : List Bool, ordVec p d w (V k) =
      ordVec p d w (V 0) ᵥ* (l.map fun b => if b then ordMat p d w S G1 else ordMat p d w S G0).prod :=
  bfs_sound' hc hnb hV hG0 hG1 h hsf hcnt

theorem basis_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {V : Nat → Nat} {Ri : Nat}
    (h : CFSG.KC.Fam.rowsBasis V (mulR p w S d T L H CM RM) (validM p nb L H) (validM p S LV HV) S d
      ONE Ri = true) (M : Matrix (Fin d) (Fin d) (ZMod p))
    (hM : ∀ k < d, ordVec p d w (V k) ᵥ* M = ordVec p d w (V k)) : M = 1 :=
  basis_sound' hc hnb h M hM


theorem sylowPc_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {nreg : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) {q n pb PR PW nbl BL : Nat} (hq : q.Prime)
    (hpr : regsIn PR n nreg = true) (hpw : pwOK RB (mulR p w S d T L H CM RM) PR PW n q nreg = true)
    {Cs : List Nat}
    (hpc : Nat.beq (runPc RB (mulR p w S d T L H CM RM) ONE PR PW n q pb Cs 1) (Nat.add 1 n) = true)
    (hbl : BlocksOK p d w S T RM LV HV RB PR n q nbl BL) :
    q ^ n ∣ Nat.card G :=
  sylowPc_sound' hc hnb hR hq hpr hpw hpc hbl

theorem sylowFlag_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {G : Subgroup (GL (Fin d) (ZMod p))} {RB : Nat → Nat} {nreg : Nat}
    (hR : RegsIn p d w S nb L H G RB nreg) {n PR nbl BL UP Cm Ci : Nat} (hp : p.Prime)
    (hpr : regsIn PR n nreg = true)
    (hfl : flagOK (mulR p w S d T L H CM RM) (validM p nb L H) w S d ONE UP Cm Ci = true)
    (hun : uniOK RB (mulR p w S d T L H CM RM) w ONE UP Cm Ci PR 0 n = true)
    (hbl : BlocksOK p d w S T RM LV HV RB PR n p nbl BL) :
    p ^ n ∣ Nat.card G :=
  sylowFlag_sound' hc hnb hR hp hpr hfl hun hbl

theorem primSub_sound {sizes n N : Nat} (h : CFSG.KC.Fam.primSub sizes n N = true) :
    ∀ mask < 2 ^ n, mask ≠ 0 → mask ≠ 2 ^ n - 1 → ¬ CFSG.KC.Fam.subSize sizes mask n ∣ N :=
  primSub_sound' h

end CFSG.KS.J4Hub

end
