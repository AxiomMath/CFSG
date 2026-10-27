module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23NonsolvCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverFixInduced
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Facts
public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import CFSG.Sporadic.Fi23.Fischer
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CoverFix CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

theorem fi23InvolutionFixed_proved :
    Fi.V3.Fi23InvolutionFixed := by
  intro K₂ _ _ hperf hK α hα1 hα2
  obtain ⟨e⟩ := hK
  let e' : (K₂ ⧸ center K₂) ≃* CFSG.Sporadic.Fi23.J := e.trans CFSG.Sporadic.Fi23.fi23EquivJ
  let π : K₂ →* K₂ ⧸ center K₂ := QuotientGroup.mk' (center K₂)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = center K₂ := QuotientGroup.ker_mk' _
  obtain ⟨β, hβ⟩ := exists_induced π hπ hker α
  have hβ1 : β ≠ 1 := induced_ne_one hperf π hker.le hβ hα1
  have hβ2 : β * β = 1 := induced_sq π hπ hβ hα2
  obtain ⟨u, hβu⟩ := CFSG.ComponentClassification.BMCase.inner_of_equiv e
    CFSG.Sporadic.FischerOddCore.fi23_mulAut_eq_conj β
  set t : CFSG.Sporadic.Fi23.J := e' u with ht
  have hZ : Subgroup.center CFSG.Sporadic.Fi23.J = ⊥ := CFSG.Sporadic.Fi23.center_J
  have hu2 : u * u = 1 := by
    have h1 : ∀ x, u * u * x * (u * u)⁻¹ = x := fun x => by
      have := congrArg (fun γ : MulAut (K₂ ⧸ center K₂) => γ x) hβ2
      simp only [MulAut.mul_apply, MulAut.one_apply, hβu, MulAut.conj_apply] at this
      calc u * u * x * (u * u)⁻¹ = u * (u * x * u⁻¹) * u⁻¹ := by group
        _ = x := this
    apply e'.injective
    have hc : e' (u * u) ∈ Subgroup.center CFSG.Sporadic.Fi23.J := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := e'.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      have := h1 x
      calc x * (u * u) = (u * u * x * (u * u)⁻¹) * (u * u) := by rw [this]
        _ = u * u * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    rw [hc, map_one]
  have ht2 : t ^ 2 = 1 := by
    rw [ht, pow_two, ← map_mul, hu2, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    have : u = 1 := e'.injective (by rw [← ht, h, map_one])
    apply hβ1
    rw [hβu, this, map_one]
  have hnsol : ¬ Group.IsSolvable ↥(fixed β) := by
    intro hs
    refine not_isSolvable_centralizer_involution ht2 ht1 ?_
    let f : ↥(centralizer ({t} : Set CFSG.Sporadic.Fi23.J)) →* ↥(fixed β) :=
      (((e'.symm : CFSG.Sporadic.Fi23.J →* K₂ ⧸ center K₂)).comp
        (centralizer ({t} : Set CFSG.Sporadic.Fi23.J)).subtype).codRestrict (fixed β) fun y => by
          have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
          show β (e'.symm (y : CFSG.Sporadic.Fi23.J)) = e'.symm (y : CFSG.Sporadic.Fi23.J)
          rw [hβu, MulAut.conj_apply]
          apply e'.injective
          rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← ht]
          calc t * (y : CFSG.Sporadic.Fi23.J) * t⁻¹ = (y : CFSG.Sporadic.Fi23.J) * t * t⁻¹ := by
                rw [hy]
            _ = y := by group
    have hf : Function.Injective f := fun a b hab =>
      Subtype.ext (e'.symm.injective (congrArg Subtype.val hab))
    exact Group.isSolvable_of_isSolvable_injective hf
  exact not_isSolvable_fixed_of_induced π hπ hker.le hβ hnsol

end CFSG.EvenSporadicStandard.Induction
