module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Neighbour
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.EPilot
open CFSG.RankThree.Classical2 CFSG.LieType.Universal.Spin

section Model


noncomputable def omegaEquivPerpLeviE7 (F : Type) [Field F] [Finite F] [CharP F 2] :
    ↥(orthDerived (quadPlus 6 F)) ≃* ↥(perpLevi .E7 F) :=
  ((MonoidHom.ofInjective
      (CFSG.StandardType.RootCentOmega.spinAction_quadPlus_injective (n := 6) (K := F))).trans
    (MulEquiv.subgroupCongr (range_spinAction_quadPlus_eq_commutator (by norm_num)))).symm.trans
    (CFSG.SeitzReduction.E7Pilot.spinEquivPerpLevi F)

variable {F : Type} [Field F] [Finite F]

theorem exists_mem_centralizer_perpLevi_E7_two (hF : Nat.card F = 2) :
    ∃ y : ↥(adjointGroup .E7 F),
      y ∈ Subgroup.centralizer (perpLevi .E7 F : Set ↥(adjointGroup .E7 F)) ∧
        y ^ 3 = 1 ∧ y ∉ perpLevi .E7 F := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  obtain ⟨X, hXJ, hcyc, hX⟩ :=
    CFSG.SeitzReduction.E6Pilot.exists_nonsplit_le_subgroupOf_highRootSL2 (τ := .E7) (K := F)
  obtain ⟨-, hdisj, hXC⟩ :=
    CFSG.SeitzReduction.E7Pilot.centralizer_nonsplit_E7_of_finite hXJ hX hcyc
  obtain ⟨y, hy⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top X).mp hcyc
  have hyX : y ∈ X := by rw [← hy]; exact Subgroup.mem_zpowers y
  have hord : orderOf y = 3 := by
    rw [← Nat.card_zpowers, hy, hX, hF]
  refine ⟨y, hXC hyX, ?_, ?_⟩
  · rw [← hord]; exact pow_orderOf_eq_one y
  · intro hyD
    have hybot : y ∈ (⊥ : Subgroup ↥(adjointGroup .E7 F)) := by
      have h : y ∈ X ⊓ perpLevi .E7 F := ⟨hyX, hyD⟩
      rwa [disjoint_iff.mp hdisj] at h
    rw [Subgroup.mem_bot] at hybot
    rw [hybot, orderOf_one] at hord
    norm_num at hord

end Model

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
