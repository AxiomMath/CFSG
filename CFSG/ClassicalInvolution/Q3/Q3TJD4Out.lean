module

public import CFSG.ClassicalInvolution.Q3.Q3TJExc
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open scoped Pointwise

theorem relIndex_inner_matrixImage_dvd_two_pow {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (e : ι ≃ Fin d)
    (Q₀ : QuadraticForm K (ι → K)) (hab : IsometryAbelianizationBound 3 Q₀)
    {Qc : QuadraticForm K (Fin d → K)} (hQc : Qc = reindexQuadraticForm e Q₀) (hQ : Qc ≠ 0) :
    ∃ a : ℕ, (inner (matrixProjectiveDerived Qc)).relIndex (matrixProjectiveImage Qc) ∣ 2 ^ a := by
  subst hQc
  have ha := relIndex_inner_dvd (reindexQuadraticForm e Q₀)
  have hb := relIndex_isometryRange_dvd (reindexQuadraticForm e Q₀) (exists_nonzero_value _ hQ)
  have hc := (relIndex_linearRange_dvd (reindexQuadraticForm e Q₀)).trans
    (Subgroup.card_subgroup_dvd_card (fieldProjection (reindexQuadraticForm e Q₀)).range)
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = 2 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units, hK]
    norm_num
  have hring : Nat.card (K ≃+* K) = 1 := by
    have : Subsingleton (K ≃+* K) := ⟨fun a b =>
      (ringEquiv_eq_refl_of_card_three hK a).trans (ringEquiv_eq_refl_of_card_three hK b).symm⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨RingEquiv.refl K⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.card (Abelianization (matrixIsometries (reindexQuadraticForm e Q₀))) =
      2 ^ m := by
    have := hab.1
    exact IsPGroup.iff_card.mp ((CFSG.IsElementaryAbelian.isPGroup 2 _).of_equiv
      (MulEquiv.abelianizationCongr (matrixIsometriesReindexEquiv e Q₀)).symm)
  have h1 : inner (matrixProjectiveDerived (reindexQuadraticForm e Q₀)) ≤
      (isometryConjugationHom (reindexQuadraticForm e Q₀)).range := by
    rw [inner_eq_map_commutator (reindexQuadraticForm e Q₀)]
    exact Subgroup.map_le_range _ _
  have h2 := isometryConjugationHom_range_le (reindexQuadraticForm e Q₀)
  have h3 : (linearConjugationHom (reindexQuadraticForm e Q₀)).range ≤
      matrixProjectiveImage (reindexQuadraticForm e Q₀) := by
    rintro _ ⟨g, rfl⟩
    exact (mem_matrixProjectiveImage_iff _ _).mpr ⟨g.val, rfl⟩
  refine ⟨m + 1, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (h1.trans h2) h3,
    ← Subgroup.relIndex_mul_relIndex _ _ _ h1 h2]
  rw [hm] at ha
  rw [hsq] at hb
  rw [hring] at hc
  calc _ ∣ 2 ^ m * 2 * 1 := Nat.mul_dvd_mul (Nat.mul_dvd_mul ha hb) hc
    _ = 2 ^ (m + 1) := by ring

theorem exists_eq_conj_of_pow_two_pow_mem {G : Type*} [Group G] {k : ℕ} {α : MulAut G}
    (h : α ^ (2 ^ k) ∈ inner G) (hodd : Odd (orderOf α)) : ∃ g : G, α = MulAut.conj g := by
  set a : Outer G := (α : MulAut G ⧸ inner G) with ha
  have h1 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    rw [ha, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact h)
  have h2 : orderOf a ∣ orderOf α := orderOf_dvd_of_pow_eq_one (by
    rw [ha, ← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one])
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hodd' : Odd (orderOf a) := hodd.of_dvd_nat h2
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hodd'
    exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_pow.mpr ⟨even_two, hj0⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff α).mp hj
  exact ⟨g, hg.symm⟩

theorem exists_eq_conj_of_smul_statedPointFamily
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))))
    (hβ : β • statedPointFamily (coe_quadPlus 4 (GaloisField 3 1)) =
      statedPointFamily (coe_quadPlus 4 (GaloisField 3 1)))
    (hodd : Odd (orderOf β)) : ∃ y, β = MulAut.conj y := by
  have hK : Nat.card (GaloisField 3 1) = 3 ^ 1 := by rw [natCard_galoisField_three, pow_one]
  have hT : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1))))
      .POmegaPlus 4 3 1 :=
    ⟨⟨Nat.prime_three, le_rfl, le_rfl⟩, GaloisField 3 1, inferInstance, inferInstance, hK,
      ⟨MulEquiv.refl _⟩⟩
  set γ := MulAut.congr (plusCoordinateEquiv 4 (GaloisField 3 1)) β with hγdef
  have hγ : γ ∈ matrixProjectiveImage (coordinateQuadPlus 4 (GaloisField 3 1)) := by
    rw [← coordinate_plus_family_eq_matrixImage hT _ hK (MulEquiv.refl _),
      mem_projectivePointFamilyAut_iff]
    have key := familyTransport_automorphism (plusCoordinateEquiv 4 (GaloisField 3 1))
      (statedPointFamily (coe_quadPlus 4 (GaloisField 3 1))) β
    rw [hβ, plusCoordinate_pointFamily] at key
    exact key.symm
  have hab := orthogonal_model_isometry_abelianization_order_bound _ .POmegaPlus
    (.inr (.inl rfl)) 4 3 1 hT (GaloisField 3 1) hK (quadPlus 4 (GaloisField 3 1))
    (coe_quadPlus 4 (GaloisField 3 1)) (MulEquiv.refl _)
  obtain ⟨a, ha⟩ := relIndex_inner_matrixImage_dvd_two_pow natCard_galoisField_three
    (plusIndexEquiv 4) (quadPlus 4 (GaloisField 3 1)) hab
    (Qc := coordinateQuadPlus 4 (GaloisField 3 1)) rfl
    (coordinate_model_intrinsic_plus hT _ hK (MulEquiv.refl _)).1
  have hpow := Subgroup.pow_index_mem
    ((inner (matrixProjectiveDerived (coordinateQuadPlus 4 (GaloisField 3 1)))).subgroupOf
      (matrixProjectiveImage (coordinateQuadPlus 4 (GaloisField 3 1)))) ⟨γ, hγ⟩
  rw [Subgroup.mem_subgroupOf, SubgroupClass.coe_pow] at hpow
  obtain ⟨c, hc⟩ := ha
  have hγpow : γ ^ (2 ^ a) ∈ inner (matrixProjectiveDerived
      (coordinateQuadPlus 4 (GaloisField 3 1))) := by
    rw [hc, pow_mul]
    exact Subgroup.pow_mem _ hpow c
  obtain ⟨y, hy⟩ := exists_eq_conj_of_pow_two_pow_mem hγpow
    (by rwa [hγdef, MulEquiv.orderOf_eq])
  refine ⟨(plusCoordinateEquiv 4 (GaloisField 3 1)).symm y,
    (MulAut.congr (plusCoordinateEquiv 4 (GaloisField 3 1))).injective ?_⟩
  rw [← hγdef, hy, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
    MulEquiv.apply_symm_apply]

end CFSG.ClassicalInvolution.Q3.Q3T
