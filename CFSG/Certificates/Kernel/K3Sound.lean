module

public import CFSG.Certificates.Kernel.K3ProgProved
public import CFSG.Certificates.Kernel.K3Proved

public section

namespace CFSG.KC.K3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Th.Native CFSG.EvenSmallLie.Child3.SelK3

theorem progK_sound {K : K3C} {cs : List Char} (h : K.progK cs = true)
    (hs : ∀ t < K.N, K.stepK t = true) :
    parseProg (String.ofList cs) = (List.range K.N).map (instrOf K) :=
  progK_sound_proved h hs

theorem k3_sound {D : Data} {K : K3C}
    (hn : D.n = K.n) (hR : D.regs = K.R) (hprog : D.prog = (List.range K.N).map (instrOf K))
    (hg : D.gens.size = K.g) (hgt : ∀ i < K.g, D.gens[i]! = tblOf K (K.GP i))
    (hsyl : D.syl = (List.range K.sy).map K.SY) (hord : D.order = K.ord) (hreps : D.reps = K.RE)
    (hwits : D.wits = (List.range K.nw).map (witOf K))
    (hh : K.headK = true) (hs : ∀ t < K.N, K.stepK t = true) (hf : ∀ r < K.R, K.finK r = true)
    (he : ∀ k < K.ord, K.eK k = true) (hc : ∀ p < K.NC, K.cK p = true)
    (hm : ∀ k < K.ord, K.memK k = true) (hw : ∀ j < K.nw, K.witK j = true) :
    check D = true :=
  k3_sound_proved hn hR hprog hg hgt hsyl hord hreps hwits hh hs hf he hc hm hw

end CFSG.KC.K3

end
