module

public import CFSG.Certificates.Kernel.J4NP.Elab7851Group
public import CFSG.Certificates.Kernel.J4NP.Elab7851Unpack

public section

namespace CFSG.KC.J4NP

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.KC.J4Q CFSG.KC.J4Loc

structure Chk7851 (TL : List (List ℕ)) (KK CMK PRK FMK XP MK : ℕ) (FL : List (List ℕ))
    (ENT : List (List (List (List ℕ)))) : Prop where
  pin : pinOK KK TL = true
  xp : xpOK XP = true
  root : Nat.beq (lnS 191 MK 0) 0 = true
  rows : ∀ a < 191, rowOK KK CMK PRK FMK XP FL a = true
  ents : ∀ k < 235, entBlk MK CMK PRK FMK 7507 ENT k = true

theorem star_of_chk
    {TL : List (List ℕ)} {KK CMK PRK FMK XP MK : ℕ}
    {FL : List (List ℕ)} {ENT : List (List (List (List ℕ)))} (hTL : tabL = TL)
    (h : Chk7851 TL KK CMK PRK FMK XP MK FL ENT) :
    ∀ A : Subgroup J, A ≤ P0 → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x * x = 1) →
      ¬ A ≤ Eg uJ 11 → Nat.card ↥A ≤ 2 ^ 10 :=
  star_of_facts (facts_of_checks hTL h.pin h.xp h.root h.rows h.ents)

end CFSG.KC.J4NP

end
