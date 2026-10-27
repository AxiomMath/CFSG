module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscU
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscData
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscN
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscSecConn

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


theorem twinDiscInputsR_of {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4) (hT : Thm1RTwinInO2 r n)
    (h4 : Thm4RTwinBelow r n) (hE : TwinThmER r n) (hN : Disc15R r n) : TwinDiscInputsR r n := by
  have hB : TwinDiscBaseR r n := twinDiscBaseR_of h4 hT
  have hM : DStarConnectedTwinR r n := dstarConnectedTwinR_of hr hT
  exact
    { thmE := hE
      base := hB
      c13N := disc13N_of_thm4R hB h4 hM
      c14N := fun Y _ _ R S t₀ K K' z u J t W s =>
        disc14N_of_connR hB s (secConnUR hr h4 hT s)
      c15 := hN
      tqTz := discTqTz_of_connR hB (discSecConnTzR_of h4 hM)
      tqU := discTqUR_of hr h4 hT }

theorem twinCoreDiscPerpR_of_inputs {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : Thm4RTwinBelow r n) (hE : TwinThmER r n) (hN : Disc15R r n) :
    TwinCoreDiscPerpR r n := by
  intro Y _ _ R S t h hdisc hperp
  have hT := thm1RTwinInO2_of_below hr hNo h.twinBelow
  exact twinCoreDiscPerpR_of_inputsR (twinDiscInputsR_of hr hNo hT h4 hE hN) Y R S t h hdisc hperp

theorem twinCoreDiscPerpR_of_supply {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : Thm4TwinSupplyR r n) (hE : TwinThmER r n) (hN : Disc15R r n) :
    TwinCoreDiscPerpR r n :=
  fun Y _ _ R S t h hdisc hperp =>
    twinCoreDiscPerpR_of_inputs hr hNo (h4 h.below h.tbelow h.twinBelow) hE hN Y R S t h hdisc hperp

theorem twinCoreDiscPerpR_all (hNo : NoQ16E4) (h4 : ∀ r : ℕ, 4 ≤ r → ∀ n, Thm4TwinSupplyR r n)
    (hE : ∀ r : ℕ, 4 ≤ r → ∀ n, TwinThmER r n) (hN : ∀ r : ℕ, 4 ≤ r → ∀ n, Disc15R r n) :
    ∀ r : ℕ, 4 ≤ r → ∀ n, TwinCoreDiscPerpR r n :=
  fun r hr n => twinCoreDiscPerpR_of_supply hr hNo (h4 r hr n) (hE r hr n) (hN r hr n)

end CFSG.CGT.PushingUpLit.SolKNA.R4
