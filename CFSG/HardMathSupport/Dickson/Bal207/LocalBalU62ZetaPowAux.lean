module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimarySelfDual

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary

section Abstract

variable {ℓ f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData ℓ f K)
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  (H : UnitaryPrimaryData hK.bar B x) {a : K[X]}
  (ha : a ∈ primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar a = a)
  [Fact (Irreducible a)]
include H ha hself

theorem u62lb_bar_mul_eq_one (e : AdjoinRoot a) (Y : Module.End K V)
    (hYe : ∀ v : primaryComponent (x : Module.End K V) a,
      Y (v : V) = ((e • v : primaryComponent (x : Module.End K V) a) : V))
    (hYB : ∀ v w : primaryComponent (x : Module.End K V) a,
      B (Y (v : V)) (Y (w : V)) = B (v : V) (w : V)) :
    (unitaryFieldData_adjoinRoot hK (a := a)).bar e * e = 1 := by
  have hsep := separatingLeft_primaryComponent_selfDual H ha hself
  have key : ∀ w : primaryComponent (x : Module.End K V) a,
      ((unitaryFieldData_adjoinRoot hK (a := a)).bar e * e - 1) • w = 0 := by
    intro w
    have h1 : ∀ v : primaryComponent (x : Module.End K V) a,
        B (v : V) ((((unitaryFieldData_adjoinRoot hK (a := a)).bar e * e - 1) • w :
          primaryComponent (x : Module.End K V) a) : V) = 0 := by
      intro v
      have e1 := hYB v w
      rw [hYe v, hYe w, smul_adjoint_bar hK H ha hself e v (e • w)] at e1
      rw [sub_smul, one_smul, mul_smul, Submodule.coe_sub, map_sub, e1, sub_self]
    exact hsep _ fun y => H.symm.eq_iff.mp (h1 y)
  obtain ⟨v, hv, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot H.squarefree ha)
  rcases smul_eq_zero.mp (key ⟨v, hv⟩) with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd (congrArg Subtype.val h0) hv0

end Abstract

end CFSG.HardMathSupport.Dickson.Bal207

end
