module

public import CFSG.ClassicalInvolution.Asc77.AscT7JHyp51u
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S3Aux
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.A7T22

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Hat2A7S
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

namespace Hyp22G

omit [Finite G] in
theorem mem_B_cases (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) {c : G}
    (hc : c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) :
    c = 1 ∨ c = u₁ * u₂ ∨ c = z ∨ c = u₂ * u₃ ∨ c = u₁ * u₂ * z ∨ c = u₁ * u₂ * (u₂ * u₃) ∨
      c = z * (u₂ * u₃) ∨ c = u₁ * u₂ * z * (u₂ * u₃) :=
  T7J.mem_closure_three (h.comm_gen _ (by simp) _ (by simp)) (h.comm_gen _ (by simp) _ (by simp))
    (h.comm_gen _ (by simp) _ (by simp)) h.sq_12 h.hz.sq h.sq_23 hc

omit [Finite G] in
theorem B_le_centralizer_of_mem (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) {c : G}
    (hc : c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) :
    Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
  fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (T7A.commutes_closure h.comm_gen b hb c hc)

theorem mul_ne_z (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₂ ≠ z := by
  intro he
  refine Hyp22Core.not_mem_of_orderOf_four h.hyp h.mem h.hK'.1 h.hne h.hu₂.2 ?_ h.hu₂.1
  have : u₂ = u₁⁻¹ * z := by rw [← he]; group
  rw [this]
  exact K.mul_mem (K.inv_mem h.hu₁.1) h.hz.mem

theorem mul_ne_one_ne_z_23 (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : u₂ * u₃ ≠ 1 ∧ u₂ * u₃ ≠ z :=
  ⟨h.rotate.mul_ne_one, h.rotate.mul_ne_z⟩

theorem mul_ne_one_ne_z_13 (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) : u₁ * u₃ ≠ 1 ∧ u₁ * u₃ ≠ z := by
  rw [h.comm₁₃]
  exact ⟨h.rotate.rotate.mul_ne_one, h.rotate.rotate.mul_ne_z⟩

theorem comm_le_oddCore_centralizer (h : Hyp22G Ω K K' K₃ z u₁ u₂ u₃) {J J' : Subgroup G}
    (hJ : J ∈ twinSet Ω K) (hJ' : J' ∈ twinSet Ω K) (hne : J ≠ J') :
    ⁅J, J'⁆ ≤ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
  (Sec6Gen.comm_le_oddCore_of_twin h.hyp hJ.1 hJ'.1 hne (isUniqueInvolution_of_mem_twinSet h.hz hJ)
    (isUniqueInvolution_of_mem_twinSet h.hz hJ')).trans
    (inf_le_left.trans (Balance.oddCoreIn_le_of_isSubnormal (h.subn J hJ)))

end Hyp22G

end CFSG.ClassicalInvolution.A7T22
