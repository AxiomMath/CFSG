module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutD1Rho
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

section Pgl3

variable {Q : Type} [Group Q]

theorem pgl3four_commutator_simple {K : Subgroup Q} (hK : IsPGL3Four ↥K) :
    IsSimpleGroup ↥⁅K, K⁆ := by
  obtain ⟨F, _, _, ρ, hF4, hρi, hρr⟩ := L46E.exists_rho hK
  obtain ⟨ψ, -, hψi, hψr⟩ := L46E.Rho_exists_psi ρ hρi hρr
  have hs : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    L46E.isSimpleGroup_P3
  let e1 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F ≃* ↥ψ.range :=
    MonoidHom.ofInjective hψi
  let e2 : ↥ψ.range ≃* ↥(commutator ↥K) := MulEquiv.subgroupCongr hψr
  let e3 : ↥(commutator ↥K) ≃* ↥⁅K, K⁆ := by
    refine (commutator ↥K).equivMapOfInjective K.subtype K.subtype_injective |>.trans ?_
    exact MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator K)
  have := hs
  exact ((e1.trans e2).trans e3).symm.isSimpleGroup

theorem pgl3four_component_eq [Finite Q] {K : Subgroup Q} (hK : IsPGL3Four ↥K) {J : Subgroup Q}
    (hJ : IsComponent J) (hJK : J ≤ K) : J = ⁅K, K⁆ := by
  have hsimple := pgl3four_commutator_simple hK
  have hJL : J ≤ ⁅K, K⁆ := by
    have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ.1.1
    calc J = ⁅J, J⁆ := hperf.symm
      _ ≤ ⁅K, K⁆ := Subgroup.commutator_mono hJK hJK
  have hsub : (J.subgroupOf ⁅K, K⁆).IsSubnormal := hJ.2.subgroupOf
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimple hsub with hbot | htop
  · exfalso
    have hJbot : J = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hJL hx⟩ : ↥⁅K, K⁆) ∈ J.subgroupOf ⁅K, K⁆ := hx
      rw [hbot, Subgroup.mem_bot] at this
      exact Subtype.ext_iff.mp this
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
    exact (Subgroup.nontrivial_iff_ne_bot J).mp hnt hJbot
  · exact le_antisymm hJL (Subgroup.subgroupOf_eq_top.mp htop)

end Pgl3

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
