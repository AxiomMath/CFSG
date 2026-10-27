module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock
import CFSG.RankThree.PartOne.KC.OrthogonalFixedRestrict
import CFSG.RankThree.PartOne.KC.OrthogonalBlockScalar
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem perfectNoncycThreeIn_orthFixed [CharP K 2] (hx : OddOrderIsometry Q 3 x)
    (hd : 6 ≤ finrank K (fixedSpace x)) : PerfectNoncycThreeIn (supportedBlock Q x (X - 1)) := by
  refine (((perfectNoncycThreeIn_orth_six hx.polarBilin_fixed_nondegenerate hd).top_of_le
    le_rfl).map ((supportedBlock Q x (X - 1)).subtype.comp (fixedBlockEquiv hx).symm.toMonoidHom)
    ((Subgroup.subtype_injective _).comp (fixedBlockEquiv hx).symm.injective)).mono ?_
  rintro _ ⟨g, -, rfl⟩
  exact ((fixedBlockEquiv hx).symm g).2

theorem perfectThreeIn_orthFixed [CharP K 2] (hx : OddOrderIsometry Q 3 x)
    (hd : finrank K (fixedSpace x) = 4) (hK : 4 ≤ Nat.card K) :
    PerfectThreeIn (supportedBlock Q x (X - 1)) := by
  refine (((perfectThreeIn_orth_four hx.polarBilin_fixed_nondegenerate hd hK).top_of_le
    le_rfl).map ((supportedBlock Q x (X - 1)).subtype.comp (fixedBlockEquiv hx).symm.toMonoidHom)
    ((Subgroup.subtype_injective _).comp (fixedBlockEquiv hx).symm.injective)).mono ?_
  rintro _ ⟨g, -, rfl⟩
  exact ((fixedBlockEquiv hx).symm g).2

variable {h : K[X]} [Fact (Irreducible h)]

omit [Finite K] in
theorem orderOf_root_eq_three (hx : OddOrderIsometry Q 3 x) (hh : h ∈ primaryFactors x.toLinearMap)
    (hX : h ≠ X - 1) : orderOf (AdjoinRoot.root h) = 3 := by
  obtain ⟨hlam0, hord⟩ := hx.orderOf_root Nat.prime_three hh hX
  rw [← hord, ← orderOf_units]
  rfl

theorem finite_adjoinRoot : Finite (AdjoinRoot h) := by
  have : Module.Finite K (AdjoinRoot h) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finite
  exact Module.finite_of_finite K

theorem perfectNoncycThreeIn_orthPaired (hx : OddOrderIsometry Q 3 x)
    (hh : h ∈ primaryFactors x.toLinearMap) (hX : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h)
    (hm : 3 ≤ primaryMultiplicity x.toLinearMap h) :
    PerfectNoncycThreeIn (supportedBlock Q x h) := by
  have := finite_adjoinRoot (K := K) (h := h)
  set b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
    (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  set φ := pairedBlockEquiv hx hh hne
  refine ((perfectNoncycThreeIn_gl hm (orderOf_root_eq_three hx hh hX)).map
    (((supportedBlock Q x h).subtype.comp φ.symm.toMonoidHom).comp
      (Matrix.GeneralLinearGroup.toLin' b).toMonoidHom)
    (((Subgroup.subtype_injective _).comp φ.symm.injective).comp
      (Matrix.GeneralLinearGroup.toLin' b).injective)).mono ?_
  rintro _ ⟨g, -, rfl⟩
  exact (φ.symm _).2

omit [Finite K] in
theorem four_le_card_adjoinRoot (hK : 4 ≤ Nat.card K) : 4 ≤ Nat.card (AdjoinRoot h) := by
  have hirr : Irreducible h := Fact.out
  have : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  rw [Module.natCard_eq_pow_finrank (K := K), (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim]
  calc 4 ≤ Nat.card K := hK
    _ = Nat.card K ^ 1 := (pow_one _).symm
    _ ≤ Nat.card K ^ h.natDegree := Nat.pow_le_pow_right (by omega) hirr.natDegree_pos

theorem perfectThreeIn_orthPaired (hx : OddOrderIsometry Q 3 x)
    (hh : h ∈ primaryFactors x.toLinearMap) (hX : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) (hK : 4 ≤ Nat.card K) :
    PerfectThreeIn (supportedBlock Q x h) := by
  have := finite_adjoinRoot (K := K) (h := h)
  set b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
    (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  set φ := pairedBlockEquiv hx hh hne
  refine ((perfectThreeIn_gl hm (four_le_card_adjoinRoot hK)
    (orderOf_root_eq_three hx hh hX)).map
    (((supportedBlock Q x h).subtype.comp φ.symm.toMonoidHom).comp
      (Matrix.GeneralLinearGroup.toLin' b).toMonoidHom)
    (((Subgroup.subtype_injective _).comp φ.symm.injective).comp
      (Matrix.GeneralLinearGroup.toLin' b).injective)).mono ?_
  rintro _ ⟨g, -, rfl⟩
  exact (φ.symm _).2

theorem exists_selfDual_unitary (hx : OddOrderIsometry Q 3 x)
    (hh : h ∈ primaryFactors x.toLinearMap) (hX : h ≠ X - 1) (hself : h = reciprocalPolynomial h) :
    ∃ (ℓ f d : ℕ) (hU : UnitaryFieldData ℓ (f * d) (AdjoinRoot h))
      (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar] primaryComponent x.toLinearMap h
        →ₗ[AdjoinRoot h] AdjoinRoot h),
      h.natDegree = 2 * d ∧ Nat.card K = ℓ ^ f ∧ B.IsSymm ∧ B.SeparatingLeft ∧
        hU.bar (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹ ∧
        Nonempty (↥(supportedBlock Q x h) ≃* ↥(sesqUnitaryGroup B)) := by
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian (by decide) hh hX hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (blockGL Q x h).range = sesqUnitaryGroup B := by
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hX hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  refine ⟨ℓ, f, d, hU, B, hdeg, hq, hBsymm, hBl, by rw [hbar, hroot], ⟨?_⟩⟩
  exact (MonoidHom.ofInjective (hx.blockGL_injective hh)).trans (MulEquiv.subgroupCongr hrange)

theorem perfectNoncycThreeIn_orthSelfDual (hx : OddOrderIsometry Q 3 x)
    (hh : h ∈ primaryFactors x.toLinearMap) (hX : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hdeg : h.natDegree ≤ 2) (hm : 3 ≤ primaryMultiplicity x.toLinearMap h)
    (hq : primaryMultiplicity x.toLinearMap h = 3 → 4 ≤ Nat.card K) :
    PerfectNoncycThreeIn (supportedBlock Q x h) := by
  obtain ⟨ℓ, f, d, hU, B, hd, hqK, hBs, hBl, hbar, ⟨φ⟩⟩ := exists_selfDual_unitary hx hh hX hself
  have hpos := (irreducible_of_mem_primaryFactors hh).natDegree_pos
  have hd1 : d = 1 := by omega
  subst hd1
  have : Finite (AdjoinRoot h) := hU.finite
  obtain ⟨e, he⟩ := hU.exists_orthonormal_basis hBs hBl
  refine ((perfectNoncycThreeIn_sesqUnitary hBs hBl e he hm (fun h3 => ?_)
    (orderOf_root_eq_three hx hh hX) hbar).map
    ((supportedBlock Q x h).subtype.comp φ.symm.toMonoidHom)
    ((Subgroup.subtype_injective _).comp φ.symm.injective)).mono ?_
  · rw [mul_one, ← hqK]
    have := hq h3
    omega
  · rintro _ ⟨g, -, rfl⟩
    exact (φ.symm g).2

theorem perfectThreeIn_orthSelfDual (hx : OddOrderIsometry Q 3 x)
    (hh : h ∈ primaryFactors x.toLinearMap) (hX : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hdeg : h.natDegree ≤ 2) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h)
    (hK : 4 ≤ Nat.card K) : PerfectThreeIn (supportedBlock Q x h) := by
  obtain ⟨ℓ, f, d, hU, B, hd, hqK, hBs, hBl, hbar, ⟨φ⟩⟩ := exists_selfDual_unitary hx hh hX hself
  have hpos := (irreducible_of_mem_primaryFactors hh).natDegree_pos
  have hd1 : d = 1 := by omega
  subst hd1
  obtain ⟨e, he⟩ := hU.exists_orthonormal_basis hBs hBl
  refine ((perfectThreeIn_sesqUnitary hBs hBl e he hm (by rw [mul_one, ← hqK]; exact hK)
    (orderOf_root_eq_three hx hh hX) hbar).map
    ((supportedBlock Q x h).subtype.comp φ.symm.toMonoidHom)
    ((Subgroup.subtype_injective _).comp φ.symm.injective)).mono ?_
  rintro _ ⟨g, -, rfl⟩
  exact (φ.symm g).2

end CFSG.AGLEmbedding.ToralCensus
