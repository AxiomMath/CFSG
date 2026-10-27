module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Cases
import CFSG.RankThree.PartTwo.Sec19.Step196KFact

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts (psuConj)

theorem modelAct_ker {Y : Type*} [Group Y] {K : Subgroup Y} [K.Normal]
    (hK : Open.IsQuasisimple K) {M : Type*} [Group M] (e : K ⧸ Subgroup.center K ≃* M) :
    (modelAct K e).ker = Subgroup.centralizer (K : Set Y) := by
  have : Group.IsPerfect K := ⟨hK.1⟩
  ext y
  rw [MonoidHom.mem_ker, modelAct, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, map_eq_one_iff _ (MulAut.congr e).injective,
    map_eq_one_iff _ (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective
      K), Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have hconj : MulAut.conjNormal y ⟨x, hx⟩ = (1 : MulAut K) ⟨x, hx⟩ := by rw [h]
    have hc : y * x * y⁻¹ = x := by
      have := congrArg Subtype.val hconj
      simpa [MulAut.conjNormal_apply] using this
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · intro h
    ext ⟨x, hx⟩
    have hxy : x * y = y * x := h x hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← hxy, mul_inv_cancel_right]

theorem pow_three_mem_range_conj_of_mem_linearAutGroup {F : Type} [Field F]
    {d : MulAut (projectiveSL 3 F)} (hd : d ∈ linearAutGroup 3 F) :
    d ^ 3 ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range :=
  CFSG.RankThree.PartTwo.Sec19.Step196Proof.pow_three_mem_range_conj_of_mem_linearAutGroup hd

theorem pow_three_mem_range_conj_of_mem_psuConj_range {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} {d : MulAut (unitaryPSU h 3)} (hd : d ∈ (psuConj h).range) :
    d ^ 3 ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range :=
  CFSG.RankThree.PartTwo.Sec19.Step196Proof.pow_three_mem_range_conj_of_mem_psuConj_range h hd

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

end
