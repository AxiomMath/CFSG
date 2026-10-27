module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFQ8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}

local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

section Basic

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}

theorem stdOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : V3Std n Y R S t K K' K₃ u₁ u₂ u₃ :=
  H.ex.1

theorem hypOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : HypOmegaGen Ω[R] :=
  (CoreData.of_S (stdOf H).perp.core).hyp

theorem partIOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : Q3CL.PartIHypG Ω[R] :=
  (CoreData.of_S (stdOf H).perp.core).partIHypG

theorem h2gOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : ∀ J ∈ Ω[R], IsPGroup 2 ↥J :=
  H.ex.2.2.2.1

theorem fourthOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    FourthTwin Ω[R] K K' K₃ t u₁ u₂ u₃ K₄ :=
  H.ex.2.1

theorem uniqInvOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J : Subgroup Y}
    (hJ : J ∈ twinSet Ω[R] K) : IsUniqueInvolution J t :=
  isUniqueInvolution_of_mem_twinSet (stdOf H).datum.hz hJ

theorem q8Of (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J : Subgroup Y}
    (hJ : J ∈ twinSet Ω[R] K) : Q8Facts J t := by
  obtain ⟨e⟩ := members_q8_of_isPGroup (stdOf H).perp (h2gOf H) J hJ.1
  exact q8Facts_of_iso (uniqInvOf H hJ) e

theorem commOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J J' : Subgroup Y}
    (hJ : J ∈ twinSet Ω[R] K) (hJ' : J' ∈ twinSet Ω[R] K) (hne : J ≠ J') : Commutes J J' := by
  intro x hx y hy
  have h1 := A7T22.le_trivialOnQuot_of_twin (hypOf H) hJ.1 hJ'.1 hne (uniqInvOf H hJ)
    (uniqInvOf H hJ') hx
  exact commute_of_trivialOnQuot (h2gOf H J' hJ'.1) h1 hy

theorem tmemOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : t ∈ W := by
  rw [← (stdOf H).datum.sq₁]
  exact W.mul_mem H.hu₁ H.hu₁

theorem abelianOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) :
    ∀ x ∈ W, ∀ y ∈ W, x * y = y * x :=
  Q3.Q3T6.abelian_of_mem_WSet3 (hypOf H) H.hW

theorem memKOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : K ∈ twinSet Ω[R] K :=
  mem_twinSet_self (stdOf H).datum.mem (stdOf H).datum.hz

theorem memKPOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : K' ∈ twinSet Ω[R] K :=
  (stdOf H).datum.hK'

theorem memK₃Of (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : K₃ ∈ twinSet Ω[R] K :=
  (stdOf H).datum.hK₃

theorem memK₄Of (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : K₄ ∈ twinSet Ω[R] K :=
  (fourthOf H).1

theorem neKPKOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : K' ≠ K := (stdOf H).datum.hne
theorem neK₃KOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : K₃ ≠ K := (stdOf H).datum.hK₃K
theorem neK₃KPOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : K₃ ≠ K' := (stdOf H).datum.hK₃K'
theorem neK₄KOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : K₄ ≠ K := (fourthOf H).2.1
theorem neK₄KPOf (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : K₄ ≠ K' := (fourthOf H).2.2.1
theorem neK₄K₃Of (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) : K₄ ≠ K₃ := (fourthOf H).2.2.2.1

end Basic

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
