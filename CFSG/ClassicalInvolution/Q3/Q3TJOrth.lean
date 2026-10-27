module

public import CFSG.ClassicalInvolution.Q3.Q3TJCl
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

theorem card_outer_reindex_dvd_two_pow {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hab : IsometryAbelianizationBound 3 Q₀) {Qc : QuadraticForm K (Fin d → K)}
    (hQc : Qc = reindexQuadraticForm e Q₀) (hQ : Qc ≠ 0) (hE : matrixProjectiveImage Qc = ⊤) :
    ∃ a : ℕ, Nat.card (Outer (matrixProjectiveDerived Qc)) ∣ 2 ^ a := by
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
  have hD : (matrixProjectiveImage (reindexQuadraticForm e Q₀)).index = 1 := by
    rw [hE, Subgroup.index_top]
  refine ⟨m + 1, ?_⟩
  rw [card_outer_eq, hD, mul_one]
  rw [hm] at ha
  rw [hsq] at hb
  rw [hring] at hc
  calc _ ∣ 2 ^ m * 2 * 1 := Nat.mul_dvd_mul (Nat.mul_dvd_mul ha hb) hc
    _ = 2 ^ (m + 1) := by ring

theorem exists_card_outer_dvd_two_pow_orth (T : Type) [Group T] (t : StatedLieTag) (n : ℕ)
    (ht : t = .POmegaOdd ∨ (t = .POmegaPlus ∧ n ≠ 4) ∨ t = .POmegaMinus)
    (h : StatedClassicalModel T t n 3 1) : ∃ a : ℕ, Nat.card (Outer T) ∣ 2 ^ a := by
  rcases ht with rfl | ⟨rfl, hn4⟩ | rfl
  · obtain ⟨⟨hp, hf, hn, hp2⟩, K, _, _, hK, ⟨e⟩⟩ := id h
    have hK3 : Nat.card K = 3 := by rw [hK]; norm_num
    have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaOdd (.inl rfl) n 3 1
      h K hK (quadOdd n K) (coe_quadOdd n K) e
    have hE : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ := by
      rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaOdd (.inl rfl) n 3 1
        h) K hK e).1]
      exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T .POmegaOdd
        (.inl rfl) n 3 1 h) K hK).2
    have hout : Nat.card (Outer T) =
        Nat.card (Outer (matrixProjectiveDerived (coordinateQuadOdd n K))) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
        (coordinateOddWitnessEquiv K e)).toEquiv
    obtain ⟨a, ha⟩ := card_outer_reindex_dvd_two_pow hK3 (oddIndexEquiv n) (quadOdd n K) hab
      (Qc := coordinateQuadOdd n K) rfl (coordinate_model_intrinsic_odd h K hK e).1 hE
    exact ⟨a, hout ▸ ha⟩
  · obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := id h
    have hK3 : Nat.card K = 3 := by rw [hK]; norm_num
    have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
      (.inr (.inl rfl)) n 3 1 h K hK (quadPlus n K) (coe_quadPlus n K) e
    have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
      (.inr (.inl rfl)) n 3 1 h) K hK e).1
    have horbit := orthogonal_geometry_plus_point_family_orbit h hK e
    have hE : matrixProjectiveImage (coordinateQuadPlus n K) = ⊤ := by
      rw [← hEA]
      exact horbit.2.2.2.2.1 (by omega)
    have hout : Nat.card (Outer T) =
        Nat.card (Outer (matrixProjectiveDerived (coordinateQuadPlus n K))) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
        (coordinatePlusWitnessEquiv K e)).toEquiv
    obtain ⟨a, ha⟩ := card_outer_reindex_dvd_two_pow hK3 (plusIndexEquiv n) (quadPlus n K) hab
      (Qc := coordinateQuadPlus n K) rfl (coordinate_model_intrinsic_plus h K hK e).1 hE
    exact ⟨a, hout ▸ ha⟩
  · obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
    have hK3 : Nat.card K = 3 := by rw [hK]; norm_num
    have hn1 : 1 ≤ n := by omega
    have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaMinus
      (.inr (.inr rfl)) n 3 1 h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
    have hE : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ := by
      rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaMinus
        (.inr (.inr rfl)) n 3 1 h) hn1 K hK b c hirr e).1]
      exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T
        .POmegaMinus (.inr rfl) n 3 1 h) hn1 K hK b c hirr).2
    have hout : Nat.card (Outer T) =
        Nat.card (Outer (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c))) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
        (coordinateMinusWitnessEquiv K hn1 b c e)).toEquiv
    obtain ⟨a, ha⟩ := card_outer_reindex_dvd_two_pow hK3 (minusIndexEquiv n hn1)
      (quadMinus n K b c) hab (Qc := coordinateQuadMinus n K hn1 b c) rfl
      (coordinate_model_intrinsic_minus h K hK b c hirr e).1 hE
    exact ⟨a, hout ▸ ha⟩

theorem two_ne_zero_galoisField_three : (2 : GaloisField 3 1) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : GaloisField 3 1) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (GaloisField 3 1) 3] at h'
  norm_num at h'

theorem exists_eq_conj_POmegaOdd {X : Type} [Group X] {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n 3 1) (hZ : Subgroup.center X = ⊥)
    (f : (Generic.modelUniv .POmegaOdd n 3 1 Nat.prime_three).K →* X)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .POmegaOdd n 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  have hn : 3 ≤ n := hadm.2.2.1
  let f' : ↥(spinGroup (quadOdd n (GaloisField 3 1))) →* X := f
  have hker' : f'.ker ≤ Subgroup.center ↥(spinGroup (quadOdd n (GaloisField 3 1))) := hker
  obtain ⟨e⟩ := nonempty_mulEquiv_of_ker_eq_center f' hf hker' hZ
    (QuotientGroup.mk' (Subgroup.center ↥(spinGroup (quadOdd n (GaloisField 3 1)))))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hT : StatedClassicalModel X .POmegaOdd n 3 1 :=
    ⟨hadm, GaloisField 3 1, inferInstance, inferInstance,
      by rw [natCard_galoisField_three, pow_one],
      ⟨e.trans (spinQuotientCenterEquivQuadOdd two_ne_zero_galoisField_three hn)⟩⟩
  obtain ⟨a, ha⟩ := exists_card_outer_dvd_two_pow_orth X .POmegaOdd n (Or.inl rfl) hT
  exact exists_eq_conj_of_card_outer_dvd ha α hodd

theorem exists_eq_conj_POmegaPlus {X : Type} [Group X] {n : ℕ} (hn4 : n ≠ 4)
    (hadm : StatedLieAdmissible .POmegaPlus n 3 1) (hZ : Subgroup.center X = ⊥)
    (f : (Generic.modelUniv .POmegaPlus n 3 1 Nat.prime_three).K →* X)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .POmegaPlus n 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  have hn : 4 ≤ n := hadm.2.2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  let f' : ↥(spinGroup (quadPlus (m + 3) (GaloisField 3 1))) →* X := f
  have hker' : f'.ker ≤ Subgroup.center ↥(spinGroup (quadPlus (m + 3) (GaloisField 3 1))) := hker
  obtain ⟨e⟩ := nonempty_mulEquiv_of_ker_eq_center f' hf hker' hZ
    (QuotientGroup.mk' (Subgroup.center ↥(spinGroup (quadPlus (m + 3) (GaloisField 3 1)))))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hT : StatedClassicalModel X .POmegaPlus (m + 3) 3 1 :=
    ⟨hadm, GaloisField 3 1, inferInstance, inferInstance,
      by rw [natCard_galoisField_three, pow_one],
      ⟨e.trans (spinQuotientCenterEquivQuadPlus (by omega))⟩⟩
  obtain ⟨a, ha⟩ := exists_card_outer_dvd_two_pow_orth X .POmegaPlus (m + 3)
    (Or.inr (Or.inl ⟨rfl, hn4⟩)) hT
  exact exists_eq_conj_of_card_outer_dvd ha α hodd

theorem exists_eq_conj_POmegaMinus {X : Type} [Group X] {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n 3 1) (hZ : Subgroup.center X = ⊥)
    (f : (Generic.modelUniv .POmegaMinus n 3 1 Nat.prime_three).K →* X)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .POmegaMinus n 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  have hn : 4 ≤ n := hadm.2.2
  let b := (LieType.Universal.minusCoeffs 3 1).1
  let c := (LieType.Universal.minusCoeffs 3 1).2
  let f' : ↥(spinGroup (quadMinus n (GaloisField 3 1) b c)) →* X := f
  have hker' : f'.ker ≤ Subgroup.center ↥(spinGroup (quadMinus n (GaloisField 3 1) b c)) := hker
  obtain ⟨e⟩ := nonempty_mulEquiv_of_ker_eq_center f' hf hker' hZ
    (QuotientGroup.mk' (Subgroup.center ↥(spinGroup (quadMinus n (GaloisField 3 1) b c))))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hT : StatedClassicalModel X .POmegaMinus n 3 1 :=
    ⟨hadm, GaloisField 3 1, inferInstance, inferInstance,
      by rw [natCard_galoisField_three, pow_one], b, c, LieType.Universal.minusCoeffs_irr 3 1,
      ⟨e.trans (spinQuotientCenterEquivQuadMinus hn (LieType.Universal.minusCoeffs_irr 3 1))⟩⟩
  obtain ⟨a, ha⟩ := exists_card_outer_dvd_two_pow_orth X .POmegaMinus n (Or.inr (Or.inr rfl)) hT
  exact exists_eq_conj_of_card_outer_dvd ha α hodd

end CFSG.ClassicalInvolution.Q3.Q3T
