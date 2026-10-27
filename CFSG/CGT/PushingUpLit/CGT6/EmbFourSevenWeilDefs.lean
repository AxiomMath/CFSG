module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenRed
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] noncomputable def xbar (P : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer (P : Set G)) : MulAut (↥P ⧸ Subgroup.center ↥P) :=
  QuotientGroup.congr (Subgroup.center ↥P) (Subgroup.center ↥P) (normConj P x hx)
    (Subgroup.characteristic_iff_map_eq.mp inferInstance (normConj P x hx))

@[expose] noncomputable def fixPbar (P : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer (P : Set G)) : Subgroup (↥P ⧸ Subgroup.center ↥P) :=
  MonoidHom.eqLocus (xbar P x hx : (↥P ⧸ Subgroup.center ↥P) →* (↥P ⧸ Subgroup.center ↥P))
    (MonoidHom.id _)

theorem xbar_mk (P : Subgroup G) (x : G) (hx : x ∈ Subgroup.normalizer (P : Set G)) (g : ↥P) :
    xbar P x hx (QuotientGroup.mk g) = QuotientGroup.mk (normConj P x hx g) := rfl

end Defs

section Statements

@[expose] def ArithStmt : Prop :=
  ∀ (p j Mc Cc S a e : ℕ), p.Prime → Odd p → 2 ≤ j → Mc = p ^ j → 1 ≤ Cc →
    Cc * p ≤ Mc → (p ≠ 5 → Cc * p ^ 2 ≤ Mc) → (p = 3 → Cc * 81 ≤ Mc) →
    S ^ 2 = Mc * e → 1 ≤ S → a ≤ S → (5 * (a : ℤ) - S) ^ 2 ≤ 20 * e * Cc →
    (if p = 3 then 3 else 2) ≤ S - a

end Statements

end CFSG.CGT.PushingUpLit.CGT6
