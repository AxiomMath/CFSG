module

public import Certificates.Data.Kernel.Spor.GraphSep
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs

public section

namespace CFSG.KS.GraphSep

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem of_sl {n NS CH : Nat} {f : Nat → Bool} (hN : n ≤ NS * CH)
    (hs : ∀ s < NS, allN CH (fun i => bIf(Nat.blt (Nat.add (s * CH) i) n, f (Nat.add (s * CH) i),
      true)) = true) : ∀ v < n, f v = true := by
  intro v hv
  obtain ⟨hCH, hsk, e⟩ := slice_cover hN hv
  have h1 := allN_spec (hs (v / CH) hsk) (v % CH) (Nat.mod_lt _ hCH)
  rw [e] at h1
  exact bIf_of_true (Nat.blt_eq ▸ hv) h1

theorem list_of_sl {n w m d NS CH : Nat} {NB AL : Nat → Nat} (hN : n ≤ NS * CH)
    (hs : ∀ s < NS, listSl n w m d NB AL (s * CH) CH = true) :
    ∀ v < n, listK n w m d NB AL v = true :=
  of_sl hN hs

theorem inv_of_sl {n w m d kS NS CH : Nat} {NB AL PS : Nat → Nat} (hN : n ≤ NS * CH)
    (hs : ∀ j < kS, ∀ s < NS, invSl n w m d NB AL PS j (s * CH) CH = true) :
    ∀ j < kS, ∀ v < n, invK w m d NB AL (PS j) v = true := by
  intro j hj
  refine of_sl (f := fun v => invK w m d NB AL (PS j) v) hN fun s hs' => ?_
  have h := hs j hj s hs'
  unfold invSl at h
  rwa [strictB_eq] at h

theorem ref_of_sl {n w m nb NS CH ORD : Nat} {NB WT : Nat → Nat} (hN : n ≤ NS * CH)
    (hs : ∀ s < NS, refSl n w m nb NB WT ORD (s * CH) CH = true) :
    ∀ k < n, nb ≤ k → refK n w m NB WT ORD k = true := by
  intro k hk hnb
  have h := of_sl (f := fun k => bIf(Nat.blt k nb, true, refK n w m NB WT ORD k)) hN hs k hk
  have hc : Nat.blt k nb = false := by
    cases h' : Nat.blt k nb
    · rfl
    · have h2 : k < nb := Nat.blt_eq ▸ h'
      omega
  rw [hc] at h
  exact h

end CFSG.KS.GraphSep

end
