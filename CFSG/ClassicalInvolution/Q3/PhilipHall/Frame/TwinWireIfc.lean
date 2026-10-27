module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Prelude

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

set_option linter.unusedSectionVars false

@[expose] def TwinConnPreludeOut (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHyp n Y R S t → Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      (∀ K ∈ CoreAssembly.conjClass (tightCore R), ∀ z : Y, IsUniqueInvolution K z →
          classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set Y)) = ⊥) ∧
        (∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J ∧
          Nonempty (↥J ≃* QuaternionGroup 2)) ∧
        TC.SepHyp (CoreAssembly.conjClass (tightCore R)) ∧ TwinGraphStd (tightCore R)

@[expose] def TwinConnEdgesOut (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHyp n Y R S t → Subgroup.center Y = ⊥ →
    ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      ∀ N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M,
      ∀ zM zN : Y, IsUniqueInvolution M zM → IsUniqueInvolution N zN → zM ≠ zN →
        ∀ hcomm : zM ∈ Subgroup.centralizer ({zN} : Set Y),
        ∀ L : Subgroup (OddQuot zN), CFSG.IsComponent L →
          oddQuotMk zN ⟨zM, hcomm⟩ ∈ Subgroup.normalizer (L : Set (OddQuot zN)) →
          (∃ y ∈ L, oddQuotMk zN ⟨zM, hcomm⟩ * y ≠ y * oddQuotMk zN ⟨zM, hcomm⟩) →
          Q3NM.AutOddFreeOn ↥L (TL4.IsInducedAut L (oddQuotMk zN ⟨zM, hcomm⟩))

theorem preludeOut_of_V₃ {n : ℕ} (hSp : TwinCentRes.ModelFactSp62)
    (hD4m : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hI : TwinConnInputsV₃ n) : TwinConnPreludeOut n :=
  fun Y _ _ R S t h hconn => twinConn_preludeV₃ hSp hD4m hM12 hI h hconn

theorem edgesOut_of_V₃ {n : ℕ} (hSp : TwinCentRes.ModelFactSp62)
    (hD4m : TwinCentRes.ModelFactD42) (hI : TwinConnInputsV₃ n) : TwinConnEdgesOut n :=
  fun Y _ _ R S t h hZ => TwinConnV₃.autOddFreeOn_of_edges hSp hD4m hI h hZ

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

end
