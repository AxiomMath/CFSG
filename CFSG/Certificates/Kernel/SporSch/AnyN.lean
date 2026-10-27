module

public import Certificates.Data.Kernel.SporSch.Kappa
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem anyN_spec {n : Nat} {f : Nat → Bool} (h : anyN n f = true) : ∃ i < n, f i = true := by
  refine Classical.byContradiction fun hne => ?_
  have hall : allN n (fun i => Bool.rec (motive := fun _ => Bool) true false (f i)) = true :=
    CFSG.KS.Raw.allN_of_forall fun i hi => by
      cases hf : f i
      · rfl
      · exact absurd ⟨i, hi, hf⟩ hne
  unfold anyN at h
  rw [hall] at h
  exact Bool.false_ne_true h

end CFSG.KS.SporSch

end
