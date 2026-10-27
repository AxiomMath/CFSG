module

public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.ZJ
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJFinal
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ChevFrontier
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.FinalSmall
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.J3
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Final
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Model
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co3
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22Three
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi24Prime
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.McL
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Suz
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.ON
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.HN
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Ly
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Th
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.B
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.M
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ
open scoped commutatorElement

theorem kFactZJFactorizationGe_of_ffChev
    (hFF : CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.FFChevModuleTheorem) :
    KFactZJFactorizationGe := by
  intro p hp hp2 X _ _ hsec hcent _ K hKn hK hT h3 h2cl S hS2 hcore hchar
  haveI : K.Normal := hKn
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hKT⟩ := hT
  haveI : Nontrivial X := zj_nontrivial_of_pComponent hK
  have hCh : CharTwo (⊤ : Subgroup X) := by
    unfold CharTwo
    rw [pCoreOf_top]
    exact inf_le_right.trans hcent
  have hQS : pCoreOf 2 (⊤ : Subgroup X) ≤ S := by
    rw [pCoreOf_top]
    exact hcore
  haveI : (gnC S).Normal := gnC_normal S
  have hKC : ¬ K ≤ gnC S := zj_not_le_centralizer hS2 hcore hcent hchar
  have hcoreC : CFSG.pCore 2 X ≤ gnC S := zj_pCore_le_gnC hcore hcent
  have hO2 := zj_pCore_quotient_eq_bot hp hp2 hK T hKT h2cl hcoreC hKC
  obtain ⟨A, hAmax, hAnot⟩ := zj_exists_offender hS2 hcore hcent hchar
  have hA2 : IsPGroup 2 A := hS2.to_le hAmax.1
  have hKA : ⁅K, A⁆ = K := zj_commutator_eq_of_not_le_pCore hp hp2 hK T hKT h2cl hA2 hAnot
  have hRodd : Odd (Nat.card ↥((K ⊓ CFSG.pPrimeCore p X).map (QuotientGroup.mk' (gnC S)))) :=
    zj_odd_card_map_le_pPrimeCore h2cl hcoreC inf_le_right
  have hle : K ⊓ CFSG.pPrimeCore p X ≤ (CFSG.pPrimeCore p ↥K).map K.subtype := by
    rw [zj_pPrimeCore_eq_subgroupOf, Subgroup.subgroupOf_map_subtype, inf_comm]
  have h3' : ¬ 3 ∣ Nat.card ↥(⁅K, K ⊓ CFSG.pPrimeCore p X⁆ : Subgroup X) := fun h =>
    h3 (h.trans (Subgroup.card_dvd_of_le (Subgroup.commutator_mono le_rfl hle)))
  have hcentC := zj_commutator_le_gnC_of_offender hCh hQS hAmax (zj_pComponent_perfect hK) hKA
    hRodd h3'
  have hcentC' : ⁅K ⊓ CFSG.pPrimeCore p X, K⁆ ≤ gnC S := by
    rw [Subgroup.commutator_comm]
    exact hcentC
  obtain ⟨hq, ⟨e⟩⟩ := zj_component_image hK hKC
    (fun r hr y hy => hcentC' (Subgroup.commutator_mem_commutator hr hy))
  haveI : (K.map (QuotientGroup.mk' (gnC S))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hKc : IsComponentOf (K.map (QuotientGroup.mk' (gnC S))) ⊤ :=
    (CFSG.isComponent_iff_open _).mp ⟨hq, Subgroup.Normal.isSubnormal inferInstance⟩
  have hKA' : ⁅K.map (QuotientGroup.mk' (gnC S)), A.map (QuotientGroup.mk' (gnC S))⁆ ≠ ⊥ := by
    rw [← Subgroup.map_commutator, hKA]
    intro hbot
    apply hKC
    intro k hk
    have hmem : QuotientGroup.mk' (gnC S) k ∈ K.map (QuotientGroup.mk' (gnC S)) := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff k).mp hmem
  have hFFC := zj_chev_of_component hFF hsec hCh hQS hAmax hO2 hKc hKA'
  have hres := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ffChevConclusion_of_mulEquiv
    e.symm hFFC
  rcases hres with h | ⟨m, -, hm⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, hm⟩

section Assembly

theorem kFactZJFactorizationGe_holds : KFactZJFactorizationGe :=
  kFactZJFactorizationGe_of_ffChev
    (HardMathSupport.Meierfrankenfeld.AGL81.FF531.ffChevModuleTheorem_of
        (HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadic_of_each
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_J3
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Co1
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Co2
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Co3
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Fi22
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Fi23
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Fi24Prime
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_McL
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Suz
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_ONan
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_HN
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Ly
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_Th
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_B
            HardMathSupport.Cooperstein.Coordinator.FFSporadic.gf2NoFFSporadicFor_M)
        (HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOdd_of_nodes
            HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOddExceptional
            HardMathSupport.Meierfrankenfeld.LieOdd.gf2NoFFLieOddSmall))

end Assembly

end CFSG.LocalAnalysis.RankFourTheoremC
