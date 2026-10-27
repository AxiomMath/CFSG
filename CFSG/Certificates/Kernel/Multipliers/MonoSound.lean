module

public import CFSG.Certificates.Kernel.Multipliers.MonoSoundProved

public section

namespace CFSG.Certificates.Mono

open CFSG.KC.Mono CFSG.CosetTable CFSG.Certificates.CosetEnumeration

theorem mono_sound {m N n : ℕ} (R : List (List (Fin m × Bool))) (w : Fin m → List (Fin m × Bool))
    {Rc Wc : List (List ℕ)} (hR : codes R = Rc)
    (hW : codes ((List.finRange m).map fun i => (i, false) :: w i) = Wc)
    {T C : ℕ → ℕ} (hp : paramsOK N n C R.length = true)
    (h : ∀ x < N, pointOK T m N n C Rc Wc x = true) :
    ∃ (E : Type) (_ : Group E) (ψ : PG m (CFSG.LieType.Multipliers.coverWords R w) →* E)
      (τ : Multiplicative (ZMod n) →* E), Function.Injective τ ∧
        ∀ k (hk : k < R.length), ψ (PresentedGroup.mk _ (FreeGroup.mk R[k])) =
          τ (Multiplicative.ofAdd (C k : ZMod n)) :=
  mono_sound_proved R w hR hW hp h

end CFSG.Certificates.Mono

end
