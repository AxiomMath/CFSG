module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.FieldPart.Hom
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Basic

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootDiagUnit)
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K]

theorem hElt_coe (μ : Kˣ) : ((hElt μ : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
    rootDiagUnit Tag.D4 (fun j : Fin Tag.D4.rank => μ ^ Tag.D4.cartan ctr j) :=
  torusElt_eq_rootDiagUnit ctr μ

theorem d4Graph_hElt (ε : ℕ) (μ : Kˣ) : d4Graph K ε (hElt μ) = hElt μ := by
  refine Subtype.ext ?_
  rw [coe_d4Graph, hElt_coe]
  have hP : d4P K * rootDiagUnit Tag.D4 (fun j : Fin Tag.D4.rank => μ ^ Tag.D4.cartan ctr j) *
      (d4P K)⁻¹ = rootDiagUnit Tag.D4 (fun j : Fin Tag.D4.rank => μ ^ Tag.D4.cartan ctr j) := by
    have h := diagramMap_mul_rootDiagUnit (K := K) (t := TwistTag.D4)
      (fun j : Fin Tag.D4.rank => μ ^ Tag.D4.cartan ctr j)
    have hb : (fun i : Fin TwistTag.D4.tag.rank =>
        (fun j : Fin Tag.D4.rank => μ ^ Tag.D4.cartan ctr j) (TwistTag.D4.perm.symm i)) =
        fun j : Fin Tag.D4.rank => μ ^ Tag.D4.cartan ctr j := by
      funext i
      have : Tag.D4.cartan ctr (TwistTag.D4.perm.symm i) = Tag.D4.cartan ctr i := by
        fin_cases i <;> decide
      simp only [this]
    rw [hb] at h
    change diagramMap TwistTag.D4 K * _ = _ * diagramMap TwistTag.D4 K at h
    exact (mul_inv_eq_iff_eq_mul.2 h)
  induction ε with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_inv_rev]
    have : d4P K ^ n * d4P K * rootDiagUnit Tag.D4 (fun j : Fin Tag.D4.rank =>
        μ ^ Tag.D4.cartan ctr j) * ((d4P K)⁻¹ * (d4P K ^ n)⁻¹) =
        d4P K ^ n * (d4P K * rootDiagUnit Tag.D4 (fun j : Fin Tag.D4.rank =>
          μ ^ Tag.D4.cartan ctr j) * (d4P K)⁻¹) * (d4P K ^ n)⁻¹ := by group
    rw [this, hP, ih]

theorem exactNormalAut_hElt (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (μ : Kˣ) :
    exactNormalAut Tag.D4 K a σ ε (hElt μ) = hElt (Units.map σ.toRingHom.toMonoidHom μ) := by
  refine Subtype.ext ?_
  rw [coe_exactNormalAut, exactQ_D4, hElt_coe, units_map_entrywiseHom_rootDiagUnit_ringEquiv]
  change rootDiagUnit Tag.D4 a * 1 * _ * 1⁻¹ * (rootDiagUnit Tag.D4 a)⁻¹ = _
  rw [inv_one, mul_one, mul_one, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
    hElt_coe]
  congr 1
  funext i
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [mul_comm (a i), mul_assoc, mul_inv_cancel, mul_one, map_zpow]

theorem sigmaOf_eq_of_hElt {β : StabU K} {σ : K ≃+* K}
    (h : ∀ μ : Kˣ, (β : MulAut (adjointGroup Tag.D4 K)) (hElt μ) =
      hElt (Units.map σ.toRingHom.toMonoidHom μ)) : sigmaOf β = σ := by
  obtain ⟨a, ha⟩ := semilin_sigmaOf β
  refine RingEquiv.ext fun x => ?_
  by_cases hx : x = 0
  · simp [hx]
  set μ : Kˣ := Units.mk0 x hx
  have h1 := congrArg (β : MulAut (adjointGroup Tag.D4 K)) (hElt_mul_zElt μ 1)
  rw [map_mul, map_mul, map_inv, h μ, ha 1, ha ((μ : K) * 1), hElt_mul_zElt] at h1
  have h2 := zElt_injective h1
  simp only [mul_one, map_one, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_one] at h2
  have hμ : (μ : K) = x := rfl
  rw [hμ] at h2
  have h3 : (a : K) * (sigmaOf β) x = (a : K) * σ x := by rw [← h2, mul_comm]
  exact mul_left_cancel₀ a.ne_zero h3

theorem normalForm_mem_StabU (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε ∈ StabU K := by
  have h1 := exactNormalAut_mem (K := K) (τ := Tag.D4) a σ 0
  have h2 := d4Graph_mem (K := K) ε
  exact (mul_mem h1 h2).1

theorem fieldPart_normalForm (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    fieldPart (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) = σ := by
  rw [fieldPart_of_mem_StabU (normalForm_mem_StabU a σ ε)]
  refine sigmaOf_eq_of_hElt (fun μ => ?_)
  show (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) (hElt μ) = _
  rw [MulAut.mul_apply, d4Graph_hElt, exactNormalAut_hElt]

theorem exists_algebraic_of_mem_commutator {η : MulAut (adjointGroup Tag.D4 K)}
    (hη : η ∈ commutator (MulAut (adjointGroup Tag.D4 K))) (hη3 : η ^ 3 = 1) :
    ∃ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ), ε < 3 ∧
      η = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε) := by
  obtain ⟨g, a, σ, ε, hε, -, rfl⟩ := exists_cube_normal_form_sigma η hη3
  have h1 := fieldPart_eq_one_of_mem_commutator hη
  rw [map_mul, fieldPart_conj, fieldPart_normalForm, one_mul] at h1
  subst h1
  exact ⟨g, a, ε, hε, rfl⟩

end CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart
