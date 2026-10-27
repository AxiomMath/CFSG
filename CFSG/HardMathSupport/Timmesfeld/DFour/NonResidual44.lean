module

public import CFSG.HardMathSupport.Timmesfeld.DFour.Residual44Assembly
public import CFSG.HardMathSupport.Timmesfeld.DFour.NonResidual44Count
public import CFSG.RankThree.SteinbergR3ECAEvenD4Centralizer

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open QuadraticMap Module
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit (plusCX plusCXstar)
open CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.DefChar.Orth
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv)
open CFSG.RankThree.EvenD4Centralizer
  (card_fixed_coordinate_families mem_pointFamilyAut_of_card_fixed_ne)
open CFSG.ComponentClassification.UnbalancedCatalog.ThreeFamily (card_fixed_maximal)
open scoped Pointwise

section NonResidual

variable {K : Type} [Field K] [Finite K]

local notation "Q₈" => coordinateQuadPlus 4 K

theorem three_le_card_of_charP {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) :
    3 ≤ Nat.card K := by
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rw [Nat.card_eq_fintype_card, hcard]
  calc 3 ≤ p := hp3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ (n : ℕ) := Nat.pow_le_pow_right hp.pos n.pos

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem nonResidual44_core (hp2 : p ≠ 2) {g : matrixProjectiveDerived Q₈} {gh : matrixDerived Q₈}
    (hgh : matrixProjectiveProjection Q₈ gh = g) (hghp : gh ^ p = 1) (hg : orderOf g = p)
    (hres : ¬ Residual44 gh) {α : MulAut (matrixProjectiveDerived Q₈)}
    (hfix : ∀ s, s * g = g * s → α s = s) :
    α ∈ matrixProjectiveImage Q₈ := by
  have : NeZero (2 * 4) := ⟨by norm_num⟩
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨-, -, hab, himage⟩ := coordinatePlusFour_facts (K := K) p
  have hcc : (1 : K) * 1 = 1 := mul_one 1
  have hG' : gEnd gh 1 = toE gh.val := by rw [gEnd, one_smul]
  have hG : gEnd gh 1 ^ p = 1 := by
    rw [hG', ← toE_pow, ← Subgroup.coe_pow, hghp, Subgroup.coe_one, toE_one]
  have hG1 : gEnd gh 1 ≠ 1 := by
    intro h1
    rw [hG'] at h1
    have hgh1 : gh = 1 := Subtype.ext (toE_injective (by rw [h1, Subgroup.coe_one, toE_one]))
    rw [hgh1, map_one] at hgh
    rw [← hgh, orderOf_one] at hg
    exact hp.one_lt.ne hg
  set z := zEnd p gh 1 with hzdef
  have hz : ∀ x y, polar Q₈ (z x) y = -polar Q₈ x (z y) := zEnd_skew gh h2 hodd hG hcc
  have hzp : z ^ p = 0 := zEnd_pow gh hG
  have hz0 : z ≠ 0 := zOf_ne_zero h2 hodd hG hG1
  have hcomm : ∀ t : matrixDerived Q₈, matrixProjectiveProjection Q₈ t * g =
      g * matrixProjectiveProjection Q₈ t ↔ toE t.val * z = z * toE t.val := by
    intro t
    rw [← hgh, commute_proj_iff hcc hG t]
    exact ⟨comm_z_of_comm_g gh, comm_g_of_comm_z gh h2 hodd hG⟩
  obtain ⟨w₀, hw₀, hQw₀⟩ : ∃ w₀, ((toE gh.val - 1) ^ 2 : Module.End K (Fin (2 * 4) → K)) w₀ = 0 ∧
      Q₈ w₀ ≠ 0 := by
    by_contra h
    exact hres fun w hw => by_contra fun hQ => h ⟨w, hw, hQ⟩
  have hzw₀ : z (z w₀) = 0 := by
    have hc : Commute (gEnd gh 1 - 1) (invS p (gEnd gh 1)) :=
      (commute_invS (p := p) (G := gEnd gh 1)).sub_left (Commute.one_left _)
    have hz2 : z ^ 2 = invS p (gEnd gh 1) ^ 2 * (gEnd gh 1 - 1) ^ 2 := by
      rw [hzdef, zEnd, zOf, hc.mul_pow, (hc.pow_pow 2 2).eq]
    have h0 : (z ^ 2) w₀ = 0 := by
      rw [hz2, Module.End.mul_apply, hG', hw₀, map_zero]
    simpa [pow_two, Module.End.mul_apply] using h0
  obtain ⟨w, hzzw, hzw, hQw⟩ : ∃ w, z (z w) = 0 ∧ z w ≠ 0 ∧ Q₈ w ≠ 0 := by
    by_cases h0 : z w₀ = 0
    · obtain ⟨a, ha0, hza, w₁, rfl⟩ := exists_W hzp hz0
      by_cases hQ₁ : Q₈ w₁ = 0
      · by_cases hQp : Q₈ (w₁ + w₀) = 0
        · refine ⟨w₁ - w₀, by rw [map_sub, map_sub, hza, hzw₀, sub_zero],
            by rw [map_sub, h0, sub_zero]; exact ha0, fun hQm => hQw₀ ?_⟩
          rw [QuadraticMap.map_add Q₈, hQ₁, zero_add] at hQp
          rw [sub_eq_add_neg, QuadraticMap.map_add Q₈, QuadraticMap.map_neg, polar_neg_right,
            hQ₁, zero_add] at hQm
          have h2Q : (2 : K) * Q₈ w₀ = 0 := by linear_combination hQp + hQm
          exact (mul_eq_zero.1 h2Q).resolve_left h2
        · exact ⟨w₁ + w₀, by rw [map_add, map_add, hza, hzw₀, add_zero],
            by rw [map_add, h0, add_zero]; exact ha0, hQp⟩
      · exact ⟨w₁, hza, ha0, hQ₁⟩
    · exact ⟨w₀, hzw₀, h0, hQw₀⟩
  have hQu : Q₈ (z w) = 0 := by
    have e1 := polar_self Q₈ (z w)
    rw [hz, hzzw, polar_zero_right, neg_zero, two_smul] at e1
    have : (2 : K) * Q₈ (z w) = 0 := by linear_combination -e1
    exact (mul_eq_zero.1 this).resolve_left h2
  have huw : polar Q₈ (z w) w = 0 := by
    have e2 := hz w w
    rw [polar_comm Q₈ w (z w)] at e2
    have : (2 : K) * polar Q₈ (z w) w = 0 := by linear_combination e2
    exact (mul_eq_zero.1 this).resolve_left h2
  obtain ⟨f, hf⟩ := exists_eich_mem hp2 hab hQu huw
  have hfz : toE f.val * z = z * toE f.val := by
    rw [hf]
    exact LinearMap.ext fun x =>
      (eich_comm₂ hz hzzw (show z w = (1 : K) • z w from (one_smul K _).symm) x).symm
  have hαf : α (matrixProjectiveProjection Q₈ f) = matrixProjectiveProjection Q₈ f :=
    hfix _ ((hcomm f).2 hfz)
  set Rd := statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)
    with hRd
  set A := Rd.symm f with hA
  have hAf : Rd A = f := Rd.apply_symm_apply f
  set R := reindexVectorEquiv (K := K) (plusIndexEquiv 4) with hR
  have hRQ : ∀ x, Q₈ (R x) = quadPlus 4 K x :=
    reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 K)
  have hRQ' : ∀ x, quadPlus 4 K (R.symm x) = Q₈ x := fun x => by
    rw [← hRQ, R.apply_symm_apply]
  have hAx : ∀ y, toLinEquiv _ K A.val y = y + polar (quadPlus 4 K) y (R.symm (z w)) • R.symm w -
      (polar (quadPlus 4 K) y (R.symm w) +
        quadPlus 4 K (R.symm w) * polar (quadPlus 4 K) y (R.symm (z w))) • R.symm (z w) := by
    intro y
    have h1 := statedDerivedReindexEquiv_symm_vector (plusIndexEquiv 4) (quadPlus 4 K)
      (coe_quadPlus 4 K) f (R y)
    rw [LinearEquiv.symm_apply_apply] at h1
    change toLinEquiv _ K (Rd.symm f).val y = _
    rw [h1]
    change R.symm (toE f.val (R y)) = _
    rw [hf, eich_apply, map_sub, map_add, map_smul, map_smul, R.symm_apply_apply, hRQ']
    have hp1 : polar Q₈ (R y) (z w) = polar (quadPlus 4 K) y (R.symm (z w)) := by
      rw [← polar_isometry R hRQ, R.apply_symm_apply]
    have hp2' : polar Q₈ (R y) w = polar (quadPlus 4 K) y (R.symm w) := by
      rw [← polar_isometry R hRQ, R.apply_symm_apply]
    rw [hp1, hp2']
  have hu0' : R.symm (z w) ≠ 0 := fun h0 => hzw (by simpa using h0)
  have hQu' : quadPlus 4 K (R.symm (z w)) = 0 := by rw [hRQ']; exact hQu
  have huw' : polar (quadPlus 4 K) (R.symm (z w)) (R.symm w) = 0 := by
    rw [← polar_isometry R hRQ, R.apply_symm_apply, R.apply_symm_apply]
    exact huw
  have hQw' : quadPlus 4 K (R.symm w) ≠ 0 := by rw [hRQ']; exact hQw
  have hlt := card_fixed_maximal_lt_card_fixed_lines (three_le_card_of_charP hp2) hu0' hQu' huw'
    hQw' hAx
  obtain ⟨cP, cX, cXs⟩ := card_fixed_coordinate_families A
  have hsum := card_fixed_maximal (K := K) (n := 4) (by norm_num) (toLinEquiv _ K A.val)
  change Nat.card {U // U ∈ projectivePointFamily Q₈ ∧
    MulAut.conj (matrixProjectiveProjection Q₈ (Rd A)) • U = U} = _ at cP
  change Nat.card {U // U ∈ plusCX 4 K ∧
    MulAut.conj (matrixProjectiveProjection Q₈ (Rd A)) • U = U} = _ at cX
  change Nat.card {U // U ∈ plusCXstar 4 K (by norm_num) ∧
    MulAut.conj (matrixProjectiveProjection Q₈ (Rd A)) • U = U} = _ at cXs
  rw [hAf] at cP cX cXs
  have hmem := mem_pointFamilyAut_of_card_fixed_ne (c := MulAut.conj
    (matrixProjectiveProjection Q₈ f)) (by rw [cX, cP]; omega) (by rw [cXs, cP]; omega)
    (α := α) (by rw [mul_conj_mul_inv_eq, hαf])
  rw [himage] at hmem
  exact hmem

end NonResidual

theorem dFourNonResidual44_holds :
    ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p], p ≠ 2 →
      ∀ (g : matrixProjectiveDerived (coordinateQuadPlus 4 K))
        (gh : matrixDerived (coordinateQuadPlus 4 K)),
        matrixProjectiveProjection (coordinateQuadPlus 4 K) gh = g → gh ^ p = 1 →
        orderOf g = p → ¬ Residual44 gh →
        ∀ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
          (orderOf α).Coprime p → (∀ s, s * g = g * s → α s = s) →
            α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) :=
  fun _ _ _ _ _ _ hp2 _ _ hgh hghp hg hres _ _ hfix =>
    nonResidual44_core hp2 hgh hghp hg hres hfix

theorem dFourPrimeCentralizerInImage_holds : DFourPrimeCentralizerInImage :=
  dFourPrimeCentralizerInImage_of_nonResidual44 dFourNonResidual44_holds

end CFSG.HardMathSupport.Timmesfeld.DFour
