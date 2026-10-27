module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnPrelude

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Main


theorem TwinCoreHypR.toStd {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : TwinCoreHypR r n Y R S t) : TwinStdR r n Y R S t :=
  ⟨h.card, h.simple, h.nonab, h.datum, h.quat, h.gen, h.oddFree, h.hyp, h.aEmpty, h.twin⟩

theorem twinCoreConnR_of_inputs {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : Thm4RTwinBelow r n) : TwinCoreConnR r n := by
  intro Y _ _ R S t h hconn
  have hT := thm1RTwinInO2_of_below hr hNo h.twinBelow
  exact false_of_conn_R hr hT (le_of_eq h.card) h.simple h.nonab h.aEmpty
    (Q8Datum.isUniqueInvolution_core h.datum) h.twin (twinConn_preludeR h4 hT h.toStd hconn)

@[expose] def Thm4TwinSupplyR (r n : ℕ) : Prop :=
  CIT3Below n → TightBelowR r n → Thm1RTwinBelowR r n → Thm4RTwinBelow r n

theorem twinCoreConnR_of_supply {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : Thm4TwinSupplyR r n) : TwinCoreConnR r n :=
  fun Y _ _ R S t h hconn =>
    twinCoreConnR_of_inputs hr hNo (h4 h.below h.tbelow h.twinBelow) Y R S t h hconn

theorem twinCoreConnR_all (hNo : NoQ16E4) (h4 : ∀ r : ℕ, 4 ≤ r → ∀ n, Thm4TwinSupplyR r n) :
    ∀ r : ℕ, 4 ≤ r → ∀ n, TwinCoreConnR r n :=
  fun r hr n => twinCoreConnR_of_supply hr hNo (h4 r hr n)

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4
