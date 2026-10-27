module

public import CFSG.ClassicalInvolution.AschTight.S19TStmt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WPerm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.GoodLift
public import CFSG.ClassicalInvolution.Q3.Q3NLCtx
public import CFSG.ClassicalInvolution.Q3.TL3T1
public import CFSG.ClassicalInvolution.Uniform.U5Comp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

namespace W

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.AE5 CFSG.ClassicalInvolution.Asc77.Thompson

section Cards

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem three_dvd_of_muIsoS4 {V : Subgroup X} (h : MuIsoS4 Φ V) : 3 ∣ Nat.card X := by
  obtain ⟨e⟩ := h
  have h1 : Nat.card ↥(muGroup Φ V) = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h2 : Nat.card ↥(muGroup Φ V) ∣ Nat.card (NQuot (V ⊔ OCW V)) :=
    Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card (NQuot (V ⊔ OCW V)) ∣
      Nat.card ↥(Subgroup.normalizer ((V ⊔ OCW V : Subgroup X) : Set X)) :=
    Subgroup.card_quotient_dvd_card _
  have h4 : Nat.card ↥(Subgroup.normalizer ((V ⊔ OCW V : Subgroup X) : Set X)) ∣ Nat.card X :=
    Subgroup.card_subgroup_dvd_card _
  rw [h1] at h2
  exact (by norm_num : 3 ∣ 24).trans (h2.trans (h3.trans h4))

end Cards

end W

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
