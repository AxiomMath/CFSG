module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenGraphField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBHigherLinearField

namespace EvenLinearSL

variable {K : Type*} [Field K] {n : ℕ}

theorem conjAut_mem_inner_of_sq_eq_one [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K) (h : conjAut n K A ^ 2 = 1) :
    conjAut n K A ∈ inner (projectiveSL n K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set m := Fintype.card K - 1 with hm
  have hcard : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hK]
  have hmodd : Odd m := by
    rw [hm, hcard]
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨k, hk⟩ : Even (2 ^ f) := (Nat.even_pow' (by omega)).mpr even_two
    exact ⟨k - 1, by omega⟩
  have hdet : ((A ^ m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h1 : ((A ^ m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
        ((GeneralLinearGroup.det A : Kˣ) : K) ^ m := by
      rw [← GeneralLinearGroup.val_det_apply, map_pow, Units.val_pow_eq_pow_val]
    rw [h1, hm]
    exact FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero _)
  set g : SpecialLinearGroup (Fin n) K := ⟨(A ^ m : GL (Fin n) K), hdet⟩ with hg
  have hgA : SpecialLinearGroup.toGL g = A ^ m := Units.ext rfl
  have hpow : conjAut n K A = conjAut n K A ^ m := by
    obtain ⟨j, hj⟩ := hmodd
    rw [hj, pow_succ, pow_mul, h, one_pow, one_mul]
  rw [hpow, ← map_pow, ← hgA, conjAut_toGL]
  exact ⟨_, rfl⟩

end EvenLinearSL

open EvenLinearSL

theorem even_linear_semilinear_involution_full_centralizer_odd_core {n f : ℕ} (hn : 3 ≤ n)
    (hf : 1 ≤ f) {K : Type*} [Field K] (hK : Nat.card K = 2 ^ f)
    {H : Subgroup (MulAut (projectiveSL n K))} (hH : inner (projectiveSL n K) ≤ H)
    {a : MulAut (projectiveSL n K)} (haE : a ∈ semilinearAutGroup n K) (ha : orderOf a = 2) :
    CFSG.oddCore ↥(H ⊓ centralizer {a}) = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero n := ⟨by omega⟩
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut' _
  have ha2 : a ^ 2 = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp haE
  by_cases hσ : σ = 1
  ·
    subst hσ
    rw [map_one, mul_one] at ha ha2 ⊢
    exact even_linear_higher_inner_involution_full_centralizer_odd_core hn hf hK hH
      (conjAut_mem_inner_of_sq_eq_one hf hK A ha2) ha
  obtain ⟨-, -, B, hB⟩ := even_linear_field_involution_descent hf hK hn A σ hσ ha2
  set g := conjAut n K B with hg
  set β := fieldAut n K σ with hβ
  rw [hB]
  refine EvenCatalog.oddCore_eq_bot_of_mulEquiv (EvenCatalog.centralizerConjEquivMap H g β).symm ?_
  set H' := H.map (MulAut.conj g⁻¹).toMonoidHom with hH'
  have hinnH' : inner (projectiveSL n K) ≤ H' := EvenCatalog.inner_le_map_conj hH g
  have hβ2 : β ^ 2 = 1 := by
    have h1 : β = g⁻¹ * (conjAut n K A * fieldAut n K σ) * g := by
      rw [hB]
      group
    rw [h1, sq, show g⁻¹ * (conjAut n K A * fieldAut n K σ) * g *
        (g⁻¹ * (conjAut n K A * fieldAut n K σ) * g) =
        g⁻¹ * ((conjAut n K A * fieldAut n K σ) * (conjAut n K A * fieldAut n K σ)) * g by group,
      ← sq, ha2, mul_one, inv_mul_cancel]
  obtain ⟨hker, ⟨e, -⟩, hNinn, -, hNC, hNnormal, hcentN⟩ :=
    linear_quadratic_field_full_centralizer_rigidity σ hn
  set N := (subfieldConj n σ).range with hN
  have hNodd : CFSG.oddCore N = ⊥ := by
    have hsimp : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin n) (fixedField K σ)) :=
      (CFSG.LinearGroups.linear_projective_simple (by omega) (Or.inl hn)).2.1
    have : IsSimpleGroup N :=
      (e.symm.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL n _).symm).isSimpleGroup
    set i0 : Fin n := ⟨0, by omega⟩ with hi0
    set i1 : Fin n := ⟨1, by omega⟩ with hi1
    have hi01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
    set t₁ : SpecialLinearGroup (Fin n) (fixedField K σ) :=
      SpecialLinearGroup.transvection hi01 1 with ht₁
    have htt : t₁ * t₁ = 1 := by
      apply Subtype.ext
      have h2 : (1 : fixedField K σ) + 1 = 0 := by
        apply Subtype.ext
        change (1 : K) + 1 = 0
        exact CharTwo.add_self_eq_zero 1
      change (1 + Matrix.single i0 i1 (1 : fixedField K σ)) * (1 + Matrix.single i0 i1 1) = 1
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul]
      rw [Matrix.single_mul_single_of_ne (h := hi01.symm), add_zero, add_assoc,
        ← Matrix.single_add, h2, Matrix.single_zero, add_zero]
    set c : N := ⟨subfieldConj n σ t₁, ⟨t₁, rfl⟩⟩ with hc
    have hc2 : c ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hc, ← map_pow, sq, htt, map_one]
      rfl
    have hc1 : c ≠ 1 := by
      intro h1
      have h2 : t₁ ∈ (subfieldConj n σ).ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val h1
      rw [hker] at h2
      obtain ⟨u, -, hu⟩ := mem_scalars.mp h2
      have h3 := congrFun (congrFun hu i0) i1
      change Matrix.transvection i0 i1 (1 : fixedField K σ) i0 i1 = _ at h3
      simp [Matrix.transvection, Matrix.scalar_apply, hi01] at h3
    have heven : Even (Nat.card N) :=
      even_iff_two_dvd.mpr (orderOf_eq_prime hc2 hc1 ▸ orderOf_dvd_natCard c)
    exact EvenCatalog.oddCore_eq_bot_of_isSimpleGroup heven
  refine EvenCatalog.oddCore_eq_bot_of_normal_of_centralizer (R := N) ?_ ?_ hNodd ?_
  · intro r hr
    exact mem_inf.mpr ⟨hinnH' (hNinn hr), hNC hr⟩
  · intro x hx r hr
    have h1 := hNnormal.conj_mem ⟨r, hNC hr⟩ (mem_subgroupOf.mpr hr) ⟨x, (mem_inf.mp hx).2⟩
    exact mem_subgroupOf.mp h1
  · intro x hx hcomm
    have hxN : x ∈ centralizer (N : Set (MulAut (projectiveSL n K))) :=
      mem_centralizer_iff.mpr fun r hr => (hcomm r hr).symm
    rw [hcentN] at hxN
    obtain ⟨z, rfl⟩ := mem_zpowers_iff.mp hxN
    refine ⟨1, ?_⟩
    rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
      hβ2, _root_.one_zpow]

end CFSG.ComponentClassification.UnbalancedCatalog
