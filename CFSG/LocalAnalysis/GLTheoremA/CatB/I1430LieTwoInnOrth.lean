module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnDefs
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieTwoInnGlue
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxOrthogonal
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.Adapters.TauCetiLieModels
import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
import TauCeti.GroupTheory.DerivedCentralQuotient
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocalBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Orb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvB
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS5
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Local
public import Certificates.Data.U62Rank.Check
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA
import Certificates.Certificate9530

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner mem_innAutDerived_congr
  exists_pow_eq_one_of_mem_inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinatePlusWitnessEquiv
  coordinateMinusWitnessEquiv)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (CompOfType)

private theorem componentsNoA6_conj_omega_two {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G] {n f : ℕ}
    (hG : StatedClassicalModel G t n 2 f) (a : G) (ha : a ^ 3 = 1) :
    ComponentsNoA6 (MulAut.conj a) := by
  intro K hK
  obtain ⟨X, _, _, hX, hno, g, hg, hker⟩ :=
    LieComp.exists_lieFactor_of_component_conj_omega LieComp.slFactorFacts_holds
      LieComp.suFactorFacts_holds LieComp.omegaFactorFacts_holds Nat.prime_three (by norm_num)
      (Or.inr ht) hG (by norm_num) a ha K hK
  obtain ⟨φ⟩ := LieComp.nonempty_centralQuotient_mulEquiv hX.perfect g hg hker
  exact ⟨fun ψ => hno LieComp.slAltSixFacts_holds LieComp.suAltSixFacts_holds
    LieComp.omegaAltSixFacts_holds (by norm_num) ⟨φ.trans ψ⟩⟩

theorem not_compOfType_isA6_inner_omega_two {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) {n f : ℕ}
    (hG : StatedClassicalModel S t n 2 f) {α : MulAut S} (hα : α ∈ inner S) (hα3 : α ^ 3 = 1) :
    ¬ CompOfType S α isA6 := by
  have hZ : Subgroup.center S = ⊥ := by
    haveI := hs
    obtain ⟨a, b, hab⟩ := hnab
    exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative fun h =>
      hab (h.is_comm.comm a b)
  obtain ⟨a, ha, rfl⟩ := exists_pow_eq_one_of_mem_inner hZ hα hα3
  exact not_compOfType_isA6
    (LieSemisimple.perfectInLayer_conj_omega (Or.inr ht) hG Nat.prime_three (by norm_num)
      (by norm_num) a ha)
    (componentsNoA6_conj_omega_two ht hG a ha)

theorem mem_inner_of_mem_innAutDerived_omegaPlus {S : Type} [Group S] [Finite S] {n ℓ f : ℕ}
    (hG : StatedClassicalModel S .POmegaPlus n ℓ f) (hn : 5 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {α : MulAut S} (hα : α ∈ innAutDerived S) (hαp : α ^ p = 1) :
    α ∈ inner S := by
  have hG0 := hG
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  obtain ⟨-, -, -, hinner⟩ := KD264Lie.matrixModel_facts_pomegaPlus hG0 hn hK e
  let θ := coordinatePlusWitnessEquiv K e
  exact (CFSG.Sporadic.FischerOddCore.congr_mem_inner_iff θ α).1
    (hinner p hp hp2 (MulAut.congr θ α) ((mem_innAutDerived_congr θ).2 hα)
      (by rw [← map_pow, hαp, map_one]))

theorem mem_inner_of_mem_innAutDerived_omegaMinus {S : Type} [Group S] [Finite S] {n ℓ f : ℕ}
    (hG : StatedClassicalModel S .POmegaMinus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut S} (hα : α ∈ innAutDerived S) (hαp : α ^ p = 1) : α ∈ inner S := by
  have hG0 := hG
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hirr, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  have hn4 : 4 ≤ n := hadm.2.2
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, -, -, hinner⟩ := KD264Lie.matrixModel_facts_pomegaMinus hG0 hK hn1 b c hirr e
  let θ := coordinateMinusWitnessEquiv K hn1 b c e
  exact (CFSG.Sporadic.FischerOddCore.congr_mem_inner_iff θ α).1
    (hinner p hp hp2 (MulAut.congr θ α) ((mem_innAutDerived_congr θ).2 hα)
      (by rw [← map_pow, hαp, map_one]))

theorem i1430InnNoTwistedD_proved : I1430InnNoTwistedD := by
  rintro S _ _ hs hnab ⟨d, hv⟩ ⟨n, q, rfl⟩ hc - ⟨e⟩ α hα hα3 -
  have hq2 : q.p = 2 := by simpa using hc
  obtain ⟨hadm, hG | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_twistedD n q hv e
  · rw [hq2] at hG
    exact not_compOfType_isA6_inner_omega_two (Or.inr rfl) hs hnab hG
      (mem_inner_of_mem_innAutDerived_omegaMinus hG Nat.prime_three (by norm_num) hα hα3) hα3
  · have h4 : 4 ≤ n := hadm.2.2
    omega

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
