module

public import Certificates.Data.Kernel.SporSch.HeadSplit
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.WordChunkSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu

theorem headK_of_parts {n w m nw idn : Nat} {S SI : Nat → Nat} {kS kO : Nat}
    {D : List (List Int)} {nb BP : Nat} (hr : headRest n w m kS kO D nb BP = true)
    (hj : ∀ j < kS, headJ n w m nw idn S SI kO D nb BP j = true) :
    headK n w m nw idn S SI kS kO D nb BP = true := by
  unfold headRest at hr
  obtain ⟨a1, r1⟩ := (bAnd_iff _ _).1 hr
  obtain ⟨a2, r2⟩ := (bAnd_iff _ _).1 r1
  obtain ⟨a3, r3⟩ := (bAnd_iff _ _).1 r2
  obtain ⟨a4, a8⟩ := (bAnd_iff _ _).1 r3
  have hp : ∀ j < kS, permOK n w m nw (S j) (SI j) = true := fun j h =>
    ((bAnd_iff _ _).1 (hj j h)).1
  have hd : ∀ j < kS, bIf(Nat.blt j kO, true,
      strictB (S j) (fun sj => bAnd(lettersK j (dword D kO j),
        Nat.beq sj (wordK n w m idn S SI (dword D kO j))))) = true := fun j h =>
    ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (hj j h)).2).1
  have ht : ∀ j < kS, bIf(allN nb (fun t => strictB (pg w m BP t) (fun b =>
      Nat.beq (pg w m (S j) b) b)), Nat.beq (S j) idn, true) = true := fun j h =>
    ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 (hj j h)).2).2
  unfold headK
  exact (bAnd_iff _ _).2 ⟨a1, (bAnd_iff _ _).2 ⟨a2, (bAnd_iff _ _).2 ⟨a3, (bAnd_iff _ _).2 ⟨a4,
    (bAnd_iff _ _).2 ⟨allN_of_forall hp, (bAnd_iff _ _).2 ⟨allN_of_forall hd,
      (bAnd_iff _ _).2 ⟨allN_of_forall ht, a8⟩⟩⟩⟩⟩⟩⟩

theorem headJ_of_chunks {n w m nw idn : Nat} {S SI : Nat → Nat} {kO : Nat}
    {D : List (List Int)} {nb BP j L NC : Nat} {V : Nat → Nat}
    (hl : Nat.ble (dword D kO j).length (NC * L) = true) (hNC : Nat.blt 0 NC = true)
    (hc : ∀ c < NC, chunkK n w m idn S SI (dword D kO j) L V (c * L) = true)
    (h : headJW n w m nw idn S SI kO D nb BP j (V 0) = true) :
    headJ n w m nw idn S SI kO D nb BP j = true := by
  have e := wordK_of_chunks (Nat.le_of_ble_eq_true hl) (Nat.blt_eq.mp hNC) hc
  unfold headJ
  unfold headJW at h
  rw [e]
  exact h

end CFSG.KS.SporSch

end
