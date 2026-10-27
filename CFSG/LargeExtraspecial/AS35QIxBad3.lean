module

public import CFSG.LargeExtraspecial.AS35QIxBad2
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.ThSchreier.Row
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Fischer.NoF25.Local
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.LargeExtraspecial.AS35HInd
public import CFSG.LargeExtraspecial.AS35HMain
public import CFSG.LargeExtraspecial.AS35LMain
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S10Five
public import CFSG.LargeExtraspecial.S10FourA
public import CFSG.LargeExtraspecial.S10SixA
public import CFSG.LargeExtraspecial.S10Three
public import CFSG.LargeExtraspecial.S12InspSplit
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocRed
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Permutation.BurnsideSchur
public import CFSG.RankThree.Literature.FSmithTheorem2
public import CFSG.Sporadic.Co2Smith.CClosure
public import CFSG.Sporadic.Co2Smith.CTree
public import CFSG.Sporadic.Co2Smith.ClassCountFin
public import CFSG.Sporadic.Co2Smith.GlAssembly
public import CFSG.Sporadic.Co2Smith.HPTree
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.KernelCentralizer
public import CFSG.Sporadic.ThSchreier.Max3Action
public import CFSG.Sporadic.ThSchreier.Max3ActionBase1
public import CFSG.Sporadic.ThSchreier.Rigidity
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Data.CFSGNative.Co2Smith.Orbit8
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11
public import Certificates.Kernel.J4Count.KFactsBase
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace IxBad

variable (T : IxBad S)

theorem a0_inv_comm_xh : T.a0⁻¹ * T.xh = T.xh * T.a0⁻¹ := (Commute.inv_left T.a0_comm_xh).eq

theorem conj_mem_CQ {w : G} (hw : w ∈ S.M) (hwx : w * T.xh = T.xh * w) {u : G}
    (hu : u ∈ T.CQ) : w * u * w⁻¹ ∈ T.CQ := by
  obtain ⟨huQ, hux⟩ := T.mem_CQ.mp hu
  refine T.mem_CQ.mpr ⟨S.conj_mem_QG hw huQ, ?_⟩
  have hwx' : w⁻¹ * T.xh = T.xh * w⁻¹ := (Commute.inv_left hwx).eq
  calc w * u * w⁻¹ * T.xh = w * u * (w⁻¹ * T.xh) := by group
    _ = w * u * (T.xh * w⁻¹) := by rw [hwx']
    _ = w * (u * T.xh) * w⁻¹ := by group
    _ = w * (T.xh * u) * w⁻¹ := by rw [hux]
    _ = (w * T.xh) * u * w⁻¹ := by group
    _ = T.xh * (w * u * w⁻¹) := by rw [hwx]; group

theorem a0_sq_mem_CQ : T.a0 * T.a0 ∈ T.CQ := by
  rcases T.a0_sq with h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact T.mem_CQ.mpr ⟨S.z_mem_QG, (S.z_comm T.hxhM).symm⟩

@[expose] noncomputable def RS : Subgroup G where
  carrier := {r | r ∈ T.CQ ∨ ∃ u ∈ T.CQ, r = u * T.a0}
  mul_mem' := by
    rintro a b (ha | ⟨u, hu, rfl⟩) (hb | ⟨u', hu', rfl⟩)
    · exact Or.inl (mul_mem ha hb)
    · exact Or.inr ⟨a * u', mul_mem ha hu', by group⟩
    · exact Or.inr ⟨u * (T.a0 * b * T.a0⁻¹), mul_mem hu (T.conj_mem_CQ T.ha0M T.a0_comm_xh hb),
        by group⟩
    · refine Or.inl ?_
      rw [show u * T.a0 * (u' * T.a0) = u * (T.a0 * u' * T.a0⁻¹) * (T.a0 * T.a0) by group]
      exact mul_mem (mul_mem hu (T.conj_mem_CQ T.ha0M T.a0_comm_xh hu')) T.a0_sq_mem_CQ
  one_mem' := Or.inl (one_mem _)
  inv_mem' := by
    rintro a (ha | ⟨u, hu, rfl⟩)
    · exact Or.inl (inv_mem ha)
    · refine Or.inr ⟨(T.a0⁻¹ * u⁻¹ * T.a0⁻¹⁻¹) * (T.a0 * T.a0)⁻¹, mul_mem
        (T.conj_mem_CQ (S.M.inv_mem T.ha0M) T.a0_inv_comm_xh (inv_mem hu))
        (inv_mem T.a0_sq_mem_CQ), by group⟩

theorem RS_mem_M {r : G} (hr : r ∈ T.RS) : r ∈ S.M := by
  rcases hr with h | ⟨u, hu, rfl⟩
  · exact S.QG_le_M (T.CQ_le_QG h)
  · exact S.M.mul_mem (S.QG_le_M (T.CQ_le_QG hu)) T.ha0M

theorem RS_comm_t (hS : S.SixHyp) {r : G} (hr : r ∈ T.RS) : r * T.t = T.t * r := by
  rcases hr with h | ⟨u, hu, rfl⟩
  · exact T.CQ_comm_t hS h
  · calc u * T.a0 * T.t = u * (T.a0 * T.t) := by group
      _ = u * (T.t * T.a0) := by rw [T.a0_comm_t]
      _ = (u * T.t) * T.a0 := by group
      _ = T.t * (u * T.a0) := by rw [T.CQ_comm_t hS hu]; group

theorem RS_comm_xh {r : G} (hr : r ∈ T.RS) : r * T.xh = T.xh * r := by
  rcases hr with h | ⟨u, hu, rfl⟩
  · exact T.CQ_comm_xh h
  · calc u * T.a0 * T.xh = u * (T.a0 * T.xh) := by group
      _ = u * (T.xh * T.a0) := by rw [T.a0_comm_xh]
      _ = (u * T.xh) * T.a0 := by group
      _ = T.xh * (u * T.a0) := by rw [T.CQ_comm_xh hu]; group

theorem isPGroup_RS : IsPGroup 2 T.RS := by
  rintro ⟨r, hr⟩
  rcases hr with h | ⟨u, hu, rfl⟩
  · refine ⟨2, Subtype.ext ?_⟩
    simpa using S.pow_four_eq_one (T.CQ_le_QG h)
  · have h2 : (u * T.a0) * (u * T.a0) ∈ T.CQ := by
      rw [show u * T.a0 * (u * T.a0) = u * (T.a0 * u * T.a0⁻¹) * (T.a0 * T.a0) by group]
      exact mul_mem (mul_mem hu (T.conj_mem_CQ T.ha0M T.a0_comm_xh hu)) T.a0_sq_mem_CQ
    refine ⟨3, Subtype.ext ?_⟩
    have h4 := S.pow_four_eq_one (T.CQ_le_QG h2)
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [show (2 : ℕ) ^ 3 = 2 * 4 by norm_num, pow_mul, pow_two]
    exact h4

theorem v0_ne_zero : T.l ![1, 1, 1] ≠ 0 := by
  intro h
  have h' := T.l_injective (h.trans T.l_zero.symm)
  have := congrFun h' 0
  simp at this

theorem fixSpace_beta_eq : fixSpace (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) =
    Submodule.span (ZMod 2) {T.l ![1, 1, 1], (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![1, 1, 1])} := by
  apply le_antisymm
  · intro w hw
    obtain ⟨x, rfl⟩ := T.l_surjective w
    obtain ⟨h1, h2⟩ := T.beta_fix (mem_fixSpace.mp hw)
    have e : x = x 0 • ![(1 : K), 1, 1] := by
      funext i
      fin_cases i <;> simp [h1, h2]
    rw [e, T.l_smul]
    exact Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩
  · rw [Submodule.span_le]
    have hv : (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l ![1, 1, 1]) = T.l ![1, 1, 1] := by
      rw [T.hlβ]
      simp
    rintro w (rfl | rfl)
    · exact mem_fixSpace.mpr hv
    · refine mem_fixSpace.mpr ?_
      rw [T.apply_comm_of_comm (T.hζc T.β T.hβX).symm, hv]

theorem card_fixSpace_beta : Nat.card (fixSpace (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 4 := by
  rw [S.card_submodule, T.fixSpace_beta_eq, finrank_span_pair T.hζ2 T.v0_ne_zero]
  norm_num

theorem CQ_eq_clPre : T.CQ = S.clPre (fixSpace (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  ext u
  rw [S.mem_clPre, mem_fixSpace]
  constructor
  · intro hu
    exact ⟨T.CQ_le_QG hu, (T.mem_CQ_iff (T.CQ_le_QG hu)).mp hu⟩
  · rintro ⟨huQ, h⟩
    exact (T.mem_CQ_iff huQ).mpr h

theorem card_CQ : Nat.card T.CQ = 8 := by
  rw [T.CQ_eq_clPre, S.card_clPre, T.card_fixSpace_beta]

theorem a0_not_mem_QG : T.a0 ∉ S.QG := by
  intro h
  apply T.F_not_comm
  rw [← T.ha0ρ, (S.ρ_eq_one_iff ⟨T.a0, T.ha0M⟩).mpr h, one_mul, mul_one]

theorem le_card_RS : 16 ≤ Nat.card T.RS := by
  let f : T.CQ ⊕ T.CQ → T.RS := fun s => match s with
    | Sum.inl u => ⟨u, Or.inl u.2⟩
    | Sum.inr u => ⟨u * T.a0, Or.inr ⟨u, u.2, rfl⟩⟩
  have hf : Function.Injective f := by
    rintro (u | u) (u' | u') h <;> have h' := congrArg Subtype.val h
    · exact congrArg Sum.inl (Subtype.ext h')
    · exfalso
      change (u : G) = u' * T.a0 at h'
      apply T.a0_not_mem_QG
      rw [show T.a0 = (u' : G)⁻¹ * u by rw [h']; group]
      exact S.QG.mul_mem (S.QG.inv_mem (T.CQ_le_QG u'.2)) (T.CQ_le_QG u.2)
    · exfalso
      change (u : G) * T.a0 = u' at h'
      apply T.a0_not_mem_QG
      rw [show T.a0 = (u : G)⁻¹ * u' by rw [← h']; group]
      exact S.QG.mul_mem (S.QG.inv_mem (T.CQ_le_QG u.2)) (T.CQ_le_QG u'.2)
    · change (u : G) * T.a0 = u' * T.a0 at h'
      exact congrArg Sum.inr (Subtype.ext (mul_right_cancel h'))
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum, T.card_CQ] at h1
  exact h1

theorem conj_mem_M {r : G} (hr : r * T.t = T.t * r) : T.g⁻¹ * r * T.g ∈ S.M := by
  rw [S.mem_M_iff]
  have e : S.z = T.g⁻¹ * T.t * T.g := T.g_inv_t.symm
  calc T.g⁻¹ * r * T.g * S.z = T.g⁻¹ * r * T.g * (T.g⁻¹ * T.t * T.g) := by rw [← e]
    _ = T.g⁻¹ * (r * T.t) * T.g := by group
    _ = T.g⁻¹ * (T.t * r) * T.g := by rw [hr]
    _ = (T.g⁻¹ * T.t * T.g) * (T.g⁻¹ * r * T.g) := by group
    _ = S.z * (T.g⁻¹ * r * T.g) := by rw [← e]

@[expose] noncomputable def psi (hS : S.SixHyp) : T.RS →* S.O where
  toFun r := S.ρ ⟨T.g⁻¹ * r * T.g, T.conj_mem_M (T.RS_comm_t hS r.2)⟩
  map_one' := by
    rw [show (⟨T.g⁻¹ * ((1 : T.RS) : G) * T.g, T.conj_mem_M (T.RS_comm_t hS (1 : T.RS).2)⟩ :
      S.M) = 1 from Subtype.ext (by simp), map_one]
  map_mul' r r' := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    group

theorem psi_apply (hS : S.SixHyp) (r : T.RS) :
    T.psi hS r = S.ρ ⟨T.g⁻¹ * r * T.g, T.conj_mem_M (T.RS_comm_t hS r.2)⟩ := rfl

theorem mem_Qa_of_psi_eq_one (hS : S.SixHyp) {r : T.RS} (h : T.psi hS r = 1) :
    (r : G) ∈ S.Qa T.g := by
  rw [psi_apply] at h
  rw [S.mem_Qa_iff_inv_conj_mem]
  exact (S.ρ_eq_one_iff _).mp h

theorem rho_mem_Pbar {r : G} (hrM : r ∈ S.M) (hrQt : r ∈ S.Qa T.g) :
    S.ρ ⟨r, hrM⟩ ∈ S.PbarAsc T.g :=
  ⟨⟨r, hrM⟩, mem_subgroupOf.mpr ⟨hrQt, hrM⟩, rfl⟩

theorem psi_injective (hS : S.SixHyp) : Function.Injective (T.psi hS) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro r hr
  have hrQt := T.mem_Qa_of_psi_eq_one hS hr
  rw [mem_bot]
  rcases r.2 with h | ⟨u, hu, hru⟩
  · exact Subtype.ext (T.eq_one_of_mem_CQ_Qa hS h hrQt)
  · exfalso
    have hrM := T.RS_mem_M r.2
    have hP := T.pbar_comm_zeta hS (T.rho_mem_Pbar hrM hrQt)
    have huM := S.QG_le_M (T.CQ_le_QG hu)
    have hρ : S.ρ ⟨r, hrM⟩ = T.F := by
      rw [show (⟨r, hrM⟩ : S.M) = ⟨u, huM⟩ * ⟨T.a0, T.ha0M⟩ from Subtype.ext hru, map_mul,
        (S.ρ_eq_one_iff _).mpr (T.CQ_le_QG hu), one_mul, T.ha0ρ]
    rw [hρ] at hP
    exact T.F_not_comm hP

end IxBad

end CFSG.LargeExtraspecial.AS35QIx
