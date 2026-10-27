module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeTC
public import CFSG.RankThree.PartOne.KEXC.TorusConj
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharCentralizer
public import CFSG.RankThree.PartOne.KE.OrdinaryEOuter
public import CFSG.RankThree.PartOne.KGD.PlaneBridge

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KEXC
  CFSG.GH74.GLS.Stage2.Bender.Thm1


variable {L : Type} [Field L] {G : Type} [Group G] {ι : G →* ModGL TwistTag.D4.tag L}
  {g0 : ModGL TwistTag.D4.tag L}

theorem conj_mem_toralCentralizer (hιC : ∀ g, ι g ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : g0 ∈ adjointGroup TwistTag.D4.tag L) {y c : G} {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hy : rootDiagUnit TwistTag.D4.tag b = g0⁻¹ * ι y * g0) (hc : c * y = y * c) :
    g0⁻¹ * ι c * g0 ∈ toralCentralizer TwistTag.D4.tag L b := by
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hg0) (hιC c)) hg0, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff, hy]
  have h := congrArg ι hc
  rw [map_mul, map_mul] at h
  calc g0⁻¹ * ι c * g0 * (g0⁻¹ * ι y * g0) = g0⁻¹ * (ι c * ι y) * g0 := by group
    _ = g0⁻¹ * (ι y * ι c) * g0 := by rw [h]
    _ = g0⁻¹ * ι y * g0 * (g0⁻¹ * ι c * g0) := by group

theorem commute_of_conj_commute (hι : Function.Injective ι) {x c : G}
    {b : Fin TwistTag.D4.tag.rank → Lˣ} (hx : rootDiagUnit TwistTag.D4.tag b = g0⁻¹ * ι x * g0)
    (hc : g0⁻¹ * ι c * g0 * rootDiagUnit TwistTag.D4.tag b =
      rootDiagUnit TwistTag.D4.tag b * (g0⁻¹ * ι c * g0)) : c * x = x * c := by
  apply hι
  rw [hx] at hc
  rw [map_mul, map_mul]
  have h := congrArg (fun z => g0 * z * g0⁻¹) hc
  calc ι c * ι x = g0 * (g0⁻¹ * ι c * g0 * (g0⁻¹ * ι x * g0)) * g0⁻¹ := by group
    _ = g0 * (g0⁻¹ * ι x * g0 * (g0⁻¹ * ι c * g0)) * g0⁻¹ := h
    _ = ι x * ι c := by group

theorem centralizer_le_of_rootCharKernel_eq (hι : Function.Injective ι)
    (hιC : ∀ g, ι g ∈ adjointGroup TwistTag.D4.tag L) (hg0 : g0 ∈ adjointGroup TwistTag.D4.tag L)
    {x y : G} {bx by' : Fin TwistTag.D4.tag.rank → Lˣ}
    (hx : rootDiagUnit TwistTag.D4.tag bx = g0⁻¹ * ι x * g0)
    (hy : rootDiagUnit TwistTag.D4.tag by' = g0⁻¹ * ι y * g0) {p p' : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpL : ringChar L ≠ p) (hp' : p'.Prime) (hp'2 : p' ≠ 2) (hp'L : ringChar L ≠ p')
    (hordx : orderOf (rootDiagUnit TwistTag.D4.tag bx) = p)
    (hordy : orderOf (rootDiagUnit TwistTag.D4.tag by') = p') {v : WeylGroup Tag.D4}
    (hvx : rootCharKernel bx = (fun α => v • α) '' d4A2Sigma)
    (hvy : rootCharKernel by' = (fun α => v • α) '' d4A2Sigma) :
    Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨-, hMx, -, -, -, -, -, -, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer L p hp hp2 hpL bx hordx v hvx
  obtain ⟨-, hMy, -, -, -, -, -, -, -⟩ :=
    D4_odd_prime_A2_root_character_centralizer L p' hp' hp'2 hp'L by' hordy v hvy
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  have hcy := conj_mem_toralCentralizer hιC hg0 hy hc
  have hcx : g0⁻¹ * ι c * g0 ∈ toralCentralizer TwistTag.D4.tag L bx := by
    have h1 : g0⁻¹ * ι c * g0 ∈ (toralCentralizer Tag.D4 L by' : Set (ModGL Tag.D4 L)) := hcy
    rw [hMy, ← hMx] at h1
    exact h1
  exact commute_of_conj_commute hι hx
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hcx).2)

theorem centralizer_le_of_rootCharKernel_empty [IsAlgClosed L] (hι : Function.Injective ι)
    (hιC : ∀ g, ι g ∈ adjointGroup TwistTag.D4.tag L) (hg0 : g0 ∈ adjointGroup TwistTag.D4.tag L)
    {x y : G} {bx by' : Fin TwistTag.D4.tag.rank → Lˣ}
    (hx : rootDiagUnit TwistTag.D4.tag bx = g0⁻¹ * ι x * g0)
    (hy : rootDiagUnit TwistTag.D4.tag by' = g0⁻¹ * ι y * g0)
    (hker : rootCharKernel by' = ∅) (hstab : ∀ w ∈ rootCharStabilizer by', w = 1) :
    Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  have hcy := conj_mem_toralCentralizer hιC hg0 hy hc
  obtain ⟨hcG, hcC⟩ := Subgroup.mem_inf.1 hcy
  obtain ⟨w, h, hh, hgeq, hwb⟩ := exists_weyl_of_conj_regular by' by' hker hker hcG
    (Subgroup.mem_centralizer_singleton_iff.1 hcC).symm
  have hw1 : w⁻¹ = 1 := by
    apply hstab
    intro v
    have := CFSG.LieType.Chevalley.rootChar_weylTuple w by' v
    rw [hwb] at this
    exact this.symm
  have hw : w = 1 := inv_eq_one.1 hw1
  rw [hw, canonicalRep_one, mul_one] at hgeq
  apply commute_of_conj_commute hι hx
  rw [hgeq]
  exact (rootDiagUnit_mul_comm_of_mem_torusGroup bx hh).symm

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
