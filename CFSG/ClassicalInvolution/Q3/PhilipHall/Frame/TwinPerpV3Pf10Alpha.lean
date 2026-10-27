module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtU
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Alpha

section Gen

variable {G : Type} [Group G] [Finite G]

theorem alpha_of_lifted_sq (hBelow : CIT3Below (Nat.card G)) (hZ : Subgroup.center G = ⊥)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) {c z a m : G} (hcB : c ∈ B) (hc1 : c ≠ 1)
    (hzB : z ∈ B) (hz1 : z ≠ 1) (hzc : z ≠ c) {M M' : Subgroup G}
    (hM : Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M z)
    (hM' : Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M' z)
    (hne : modOdd c M ≠ modOdd c M')
    (hcomm : ∀ x ∈ modOdd c M, ∀ y ∈ modOdd c M', x * y = y * x)
    (haC : a ∈ Subgroup.centralizer ({c} : Set G)) (ha2 : a * a = z)
    (hcommM : ∀ x ∈ modOdd c M, oddQuotMk c ⟨a, haC⟩ * x = x * oddQuotMk c ⟨a, haC⟩)
    (hcommM' : ∀ x ∈ modOdd c M', oddQuotMk c ⟨a, haC⟩ * x = x * oddQuotMk c ⟨a, haC⟩)
    (hm : m ∈ M) (hm2 : m * m = z) (hamB : a * m ∈ B)
    (hBle : B ≤ Subgroup.closure ({c, z, a * m} : Set G))
    {L : Subgroup (OddQuot c)} (hL : CFSG.IsComponent L) (hmov : MovedByAll B c L) :
    alphaOf (inducedImage L (modOdd c B)) = ⊥ := by
  have hsnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := fun h => hc1 (by
    have h1 : c ∈ Subgroup.center G := h (Set.mem_singleton c)
    rwa [hZ, Subgroup.mem_bot] at h1)
  have hΦ := secData3_sFamily3 hM hM' hM
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hsnc
  obtain ⟨j, hj⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_one c M M' M)
  have hzC : z ∈ Subgroup.centralizer ({c} : Set G) := Lemma52Proof.le_centralizer_of_mem hB hcB hzB
  have hzj : oddQuotMk c ⟨z, hzC⟩ ∈ secComp hΦ D j :=
    hj (oddQuotMk_mem_modOdd (isUniqueInvolution_of_sectionMember3 hM).mem hzC)
  have hzmov : ∃ w ∈ L, oddQuotMk c ⟨z, hzC⟩ * w ≠ w * oddQuotMk c ⟨z, hzC⟩ :=
    hmov _ (oddQuotMk_mem_modOdd hzB hzC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hzB hz1 hzc hzC)
  have hLj : L = secComp hΦ D j := eq_secComp_of_not_commute hΦ D hzj hL hzmov
  subst hLj
  exact Q3T7.alpha_of_twinSq3 Q3T7.twinSqAlphaAll3_proved hΦ D hB hcB hc1 hzB hz1 hzc
    (mem_sFamily3_one c M M' M) (mem_sFamily3_two c M M' M)
    (isUniqueInvolution_of_sectionMember3 hM) (isUniqueInvolution_of_sectionMember3 hM')
    hne hcomm haC ha2 hcommM hcommM' hm hm2 hamB hBle hj hmov hL

end Gen

end Alpha

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
