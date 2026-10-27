module

public import Certificates.Data.Kernel.SporSch.RuOrbK
public import Certificates.Data.Kernel.SporSch.RuEnumK
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Schreier.RuArrays
import CFSG.Certificates.Kernel.SporSch.RuOrbKS
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem unpack_getPg {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem posK_ptPos {n m w F POS : Nat} (h : posK n m w F POS = true) :
    ptPosOK n (unpack m w F) (unpack n w POS) = true := by
  obtain ⟨h1, _⟩ := (bAnd_iff _ _).1 h
  unfold ptPosOK
  rw [allLt_iff]
  intro i hi
  have hi' : i < m := by simpa [unpack] using hi
  have hc := allN_spec h1 i hi'
  have e : ∀ (y : Nat) (k : Nat → Bool), strictB y k = k y := fun y k => by cases y <;> rfl
  rw [e] at hc
  obtain ⟨ha, hb⟩ := (bAnd_iff _ _).1 hc
  have hx : pg w (mask w) F i < n := by simpa [Nat.blt_eq] using ha
  rw [unpack_getPg hi', unpack_getPg hx]
  simp [hx, Nat.eq_of_beq_eq_true hb]

theorem labK_sound {n w K : Nat} {L SZ POS : Nat → Nat} {LAB : Nat} {Ls pos : List (Array Nat)}
    (hLs : Ls = (List.range K).map fun k => unpack (SZ k) w (L k))
    (hpos : pos = (List.range K).map fun k => unpack n w (POS k))
    (h : labK n w K L SZ POS LAB = true) :
    ruLabTab n Ls = unpack n w LAB ∧ labListsOK n Ls (unpack n w LAB) pos = true := by
  exact RuOrbKS.ruLabTab_of_labK hLs hpos h

theorem forestK_sound {n w wf R G0 G1 Q ORD FO DEP PAR GL : Nat} {a b roots : Array Nat}
    (ha : a = unpack n w G0) (hb : b = unpack n w G1)
    (hr : roots.size = R ∧ ∀ t < R, roots[t]! = pg w (mask w) Q t) (hR : R ≤ n)
    (hf : ∀ t < n, forestAt n w wf R G0 G1 Q ORD FO DEP PAR GL t = true)
    (he : ∀ e < 2 * n, eventAt n w wf R G0 G1 Q ORD FO e = true) :
    orbitForest n #[a, b] roots = (unpack n w DEP, unpack n w PAR, unpack n w GL) := by
  exact RuOrbKS.orbitForest_of_checks ha hb hr hR hf he

theorem partK_sound {n w R G0 G1 LAB Q DEP PAR GL : Nat} {a b roots : Array Nat}
    (ha : a = unpack n w G0) (hb : b = unpack n w G1)
    (hr : roots.size = R ∧ ∀ t < R, roots[t]! = pg w (mask w) Q t)
    (hp : ∀ x < n, partAt n w R G0 G1 LAB Q DEP PAR GL x = true)
    (hk : ∀ k < R, rootAt n w LAB Q k = true) :
    orbitPartOK n #[a, b] (unpack n w LAB) roots (unpack n w DEP) (unpack n w PAR)
      (unpack n w GL) = true := by
  exact RuOrbKS.orbitPartOK_of_checks ha hb hr hp hk

end CFSG.KS.SporSch

end
