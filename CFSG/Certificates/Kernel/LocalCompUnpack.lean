module

public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def bindArrK (A : Array Nat) (n w P : Nat) : Bool :=
  bAnd(Nat.beq A.size n, allN n (fun i => Nat.beq A[i]! (pg w (mask w) P i)))

theorem unpack_eq_of_bindArrK {A : Array Nat} {n w P : Nat} (h : bindArrK A n w P = true) :
    A = unpack n w P := by
  unfold bindArrK at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hs : A.size = n := Nat.eq_of_beq_eq_true h1
  have he := allN_spec h2
  unfold unpack
  refine Array.ext (by rw [hs, Array.size_ofFn]) fun i hi _ => ?_
  have hin : i < n := hs ▸ hi
  rw [Array.getElem_ofFn, ← Nat.eq_of_beq_eq_true (he i hin), getElem!_pos A i hi]

end CFSG.KS.Raw

end
