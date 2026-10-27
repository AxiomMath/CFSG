module

public import CFSG.Certificates.Kernel.Spor.RawOrbSize
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def OrbsOK (n w : Nat) (PS PSI LR : Nat → Nat) (kS nb BP NS CH : Nat) : Prop :=
  (∀ i < nb, lvOrbHdK n w (mask w) kS (pg w (mask w) BP i) (stepsAt n w PS kS BP i) (LR i) = true) ∧
  ∀ i < nb, ∀ s < NS, lvOrbSlK n w (mask w) (n * w) PS PSI kS (stepsAt n w PS kS BP i) (LR i)
    (s * CH) CH = true

theorem rawOrbitSizesK_orb {n w kS nb BP NS CH : Nat} {PS PSI LR : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (hN : n ≤ NS * CH) :
    rawOrbitSizes n S base = (List.range nb).map fun i => rcnt (LR i) :=
  Orb.rawOrbitSizes_orb hb hp ho.1 ho.2 hN

theorem rawChainK_of_card_orb {n w kS kO nb BP NS CH : Nat} {PS PSI LR : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)} (chunks : Nat)
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (_ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (_hN : n ≤ NS * CH)
    (hcard : Nat.card (Subgroup.closure (Set.range fun j : Fin kO => permOfArr n S[j.val]!)) ≤
      (rawOrbitSizes n S base).prod) :
    rawChainOK n (S.extract 0 kO) S base (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)
      chunks = true := by
  obtain ⟨hk, hH⟩ := Orb.rawHeadOK_of hb hh
  exact Orb.rawChainOK_of_head_card chunks hk hH hcard

end CFSG.KS.Raw

end
