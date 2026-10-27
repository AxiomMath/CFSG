module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.Holt.General

open MulAction Subgroup

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

variable (G) in
abbrev oddOrbitsStabilizer (α : Ω) : Subgroup G :=
  stabilizer G α ⊔ CFSG.pPrimeCore 2 G

variable (G) in
abbrev OddOrbits (α : Ω) : Type _ :=
  G ⧸ oddOrbitsStabilizer G α

variable (G) in
abbrev oddOrbitsKernel (α : Ω) : Subgroup G :=
  (toPermHom G (OddOrbits G α)).ker

theorem oddOrbitsKernel_eq_normalCore (α : Ω) :
    oddOrbitsKernel G α = (oddOrbitsStabilizer G α).normalCore :=
  (normalCore_eq_ker _).symm

theorem pPrimeCore_le_oddOrbitsKernel (α : Ω) :
    CFSG.pPrimeCore 2 G ≤ oddOrbitsKernel G α := by
  rw [oddOrbitsKernel_eq_normalCore]
  exact normal_le_normalCore.mpr le_sup_right

theorem card_quotient_oddOrbitsKernel_lt [Finite G] (hO : CFSG.pPrimeCore 2 G ≠ ⊥) (α : Ω) :
    Nat.card (G ⧸ oddOrbitsKernel G α) < Nat.card G := by
  have hN : oddOrbitsKernel G α ≠ ⊥ := fun h =>
    hO (le_bot_iff.mp (h ▸ pPrimeCore_le_oddOrbitsKernel α))
  rw [(oddOrbitsKernel G α).card_eq_card_quotient_mul_card_subgroup]
  exact lt_mul_of_one_lt_right Nat.card_pos ((one_lt_card_iff_ne_bot _).mpr hN)

end CFSG.Holt.General
