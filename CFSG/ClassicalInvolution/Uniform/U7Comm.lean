module

public import CFSG.ClassicalInvolution.Uniform.U7Vstar
public import CFSG.ClassicalInvolution.Uniform.U7Star

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement


section Comm

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem thm3Comm_of_violation (hgen : G2NonToralGenerate3) (hF : G2CentralizerInvolution3)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (D : OmegaLieU 3 1 Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hnA : ¬ AEmpty Ω K) :
    aStar Ω K = vStar Ω K ∧
      ∀ L ∈ Ω, L ∉ vStar Ω K → ∀ M ∈ vStar Ω K, ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M := by
  have hex : ExactMembers Ω := D.exactMembers hΩ
  obtain ⟨C, R, S, J, zK, zJ, a, hR, hS, rfl, rfl, hv, hQ⟩ := exists_g2Comp hΩ D hK hnA
  have hJ : S.map C.ψ ∈ aStar Ω (R.map C.ψ) :=
    Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨zK, zJ, hv⟩⟩
  have hA := aStar_eq_members hgen hΩ C hR hK hQ hJ
  have hKc : R.map C.ψ ∈ C.members := ⟨hK, R, hR, rfl⟩
  have hV := C.vStar_eq_members hF hΩ hex hKc
  refine ⟨hA.trans hV.symm, ?_⟩
  intro L hL hLv M hMv
  rw [hV] at hLv hMv
  have hc := C.commutes_of_not_mem hL hLv hMv
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc x hx y hy)]
  exact one_mem _

theorem thm3CommBelowExactU_three (hgen : G2NonToralGenerate3) (hF : G2CentralizerInvolution3)
    {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) : Thm3CommBelowExactU 3 1 n := by
  intro _ _ G _ _ hlt hO Ω hΩ K hK hnA
  obtain ⟨D⟩ := exists_omegaLieU hn hΩ ⟨K, hK⟩ hO hlt
  exact thm3Comm_of_violation hgen hF hΩ D hK hnA

end Comm

end CFSG.ClassicalInvolution.Uniform
