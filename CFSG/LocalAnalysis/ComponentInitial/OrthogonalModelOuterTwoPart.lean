module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelAbelianization
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTwoPartBound
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelFamily
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelImage
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace OrthogonalOuter

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)
open scoped Pointwise

theorem relIndex_map_dvd_relIndex {G G' : Type*} [Group G] [Group G'] (φ : G →* G')
    (H K : Subgroup G) : (H.map φ).relIndex (K.map φ) ∣ H.relIndex K := by
  have hK : K.map φ = (φ.comp K.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hK, ← Subgroup.index_comap]
  exact Subgroup.index_dvd_of_le fun k hk =>
    Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)

theorem ordProj_two_le_two_of_le_three {k : ℕ} (hk : k ≤ 3) : ordProj[2] k ≤ 2 := by
  interval_cases k
  · simp
  · exact (ordProj_two_eq_one_of_odd odd_one).trans_le (by norm_num)
  · exact (ordProj_two_two_pow 1).le
  · exact (ordProj_two_eq_one_of_odd ⟨1, rfl⟩).trans_le (by norm_num)

section Semilinear

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

@[expose] def isometryConjugationHom :
    matrixIsometries Q →* MulAut (matrixProjectiveDerived Q) :=
  (matrixProjectiveConjugationHom Q).comp (matrixIsometryInclusion Q)

@[expose] def linearConjugationHom :
    linearSimilarityPairs Q →* MulAut (matrixProjectiveDerived Q) :=
  (matrixProjectiveConjugationHom Q).comp (linearSimilarityPairs Q).subtype

theorem matrixProjectiveConjugationHom_derivedInclusion (A : matrixDerived Q) :
    matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q A) =
      MulAut.conj (matrixProjectiveProjection Q A) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change matrixProjectiveConjugation Q _ (matrixProjectiveProjection Q B) = _
  rw [matrixProjectiveConjugation_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar {g h : similarityPairs Q}
    (c : Kˣ) (hleft : g.val.left = h.val.left * GeneralLinearGroup.scalar (Fin d) c)
    (hright : g.val.right = h.val.right) :
    matrixProjectiveConjugationHom Q g = matrixProjectiveConjugationHom Q h := by
  have hc : ∀ X : GL (Fin d) K, X * GeneralLinearGroup.scalar (Fin d) c =
      GeneralLinearGroup.scalar (Fin d) c * X := by
    intro X
    have hmem : GeneralLinearGroup.scalar (Fin d) c ∈ Subgroup.center (GL (Fin d) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    exact Subgroup.mem_center_iff.mp hmem X
  have hD : ∀ B, matrixDerivedConjugation Q g B = matrixDerivedConjugation Q h B := by
    intro B
    apply Subtype.ext
    rw [matrixDerivedConjugation_val, matrixDerivedConjugation_val, hleft, hright]
    set s := GeneralLinearGroup.scalar (Fin d) c
    set X := CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K
      h.val.right B.val
    calc h.val.left * s * X * (h.val.left * s)⁻¹
        = h.val.left * (X * s) * s⁻¹ * h.val.left⁻¹ := by rw [hc X]; group
      _ = h.val.left * X * h.val.left⁻¹ := by group
  apply MulEquiv.ext
  intro x
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change matrixProjectiveConjugation Q g (matrixProjectiveProjection Q B) =
    matrixProjectiveConjugation Q h (matrixProjectiveProjection Q B)
  rw [matrixProjectiveConjugation_mk, matrixProjectiveConjugation_mk, hD]

theorem inner_eq_map_commutator :
    inner (matrixProjectiveDerived Q) =
      (commutator (matrixIsometries Q)).map (isometryConjugationHom Q) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q x
    have hB : B.val ∈ (commutator (matrixIsometries Q)).map (matrixIsometries Q).subtype := by
      rw [← matrixDerived_eq_map_commutator]
      exact B.property
    obtain ⟨A, hA, hAB⟩ := hB
    refine ⟨A, hA, ?_⟩
    have hincl : matrixIsometryInclusion Q A = matrixDerivedInclusion Q B := by
      apply Subtype.ext
      rw [matrixIsometryInclusion_val, matrixDerivedInclusion_val, ← hAB]
      rfl
    change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q A) = _
    rw [hincl, matrixProjectiveConjugationHom_derivedInclusion]
  · rintro _ ⟨A, hA, rfl⟩
    have hB : A.val ∈ matrixDerived Q := by
      rw [matrixDerived_eq_map_commutator]
      exact ⟨A, hA, rfl⟩
    have hincl : matrixIsometryInclusion Q A = matrixDerivedInclusion Q ⟨A.val, hB⟩ :=
      Subtype.ext rfl
    change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q A) ∈ _
    rw [hincl, matrixProjectiveConjugationHom_derivedInclusion]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem isometryConjugationHom_range_le :
    (isometryConjugationHom Q).range ≤ (linearConjugationHom Q).range := by
  rintro _ ⟨A, rfl⟩
  exact ⟨⟨matrixIsometryInclusion Q A, (mem_linearSimilarityPairs_iff Q _).mpr rfl⟩, rfl⟩

theorem linearConjugationHom_mem_range_of_multiplier_eq_sq (hQ : ∃ v, Q v ≠ 0)
    (g : linearSimilarityPairs Q) (c : Kˣ) (hc : multiplierHom Q hQ g = c ^ 2) :
    linearConjugationHom Q g ∈ (isometryConjugationHom Q).range := by
  have hA : g.val.val.left * GeneralLinearGroup.scalar (Fin d) c⁻¹ ∈ matrixIsometries Q := by
    rw [mem_matrixIsometries_iff]
    intro v
    have hv : matrixLinearEquiv (g.val.val.left * GeneralLinearGroup.scalar (Fin d) c⁻¹) v =
        ((c⁻¹ : Kˣ) : K) • matrixLinearEquiv g.val.val.left v := by
      rw [matrixLinearEquiv_mul, LinearEquiv.mul_apply, ← LinearEquiv.map_smul]
      congr 1
      funext i
      rw [matrixLinearEquiv_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.mulVec_diagonal]
      rfl
    have hc0 : ((c : Kˣ) : K) ≠ 0 := c.ne_zero
    have hcc : ((c : K))⁻¹ * (c : K)⁻¹ * (c : K) ^ 2 = 1 := by
      rw [sq, ← mul_assoc, inv_mul_cancel_right₀ hc0, inv_mul_cancel₀ hc0]
    rw [hv, QuadraticMap.map_smul, multiplierHom_spec Q hQ g v, hc, smul_eq_mul,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, ← mul_assoc, hcc, one_mul]
  refine ⟨⟨_, hA⟩, ?_⟩
  refine (matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar Q (g := g.val)
    (h := matrixIsometryInclusion Q ⟨_, hA⟩) c ?_ ?_).symm
  · change g.val.val.left = g.val.val.left * GeneralLinearGroup.scalar (Fin d) c⁻¹ *
      GeneralLinearGroup.scalar (Fin d) c
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  · exact (mem_linearSimilarityPairs_iff Q g.val).mp g.property

theorem relIndex_inner_dvd :
    (inner (matrixProjectiveDerived Q)).relIndex (isometryConjugationHom Q).range ∣
      Nat.card (Abelianization (matrixIsometries Q)) := by
  rw [inner_eq_map_commutator Q, MonoidHom.range_eq_map (isometryConjugationHom Q)]
  refine (relIndex_map_dvd_relIndex _ _ _).trans ?_
  rw [Subgroup.relIndex_top_right]
  exact dvd_rfl

theorem relIndex_isometryRange_dvd (hQ : ∃ v, Q v ≠ 0) :
    (isometryConjugationHom Q).range.relIndex (linearConjugationHom Q).range ∣
      (powMonoidHom 2 : Kˣ →* Kˣ).range.index := by
  have hS : ((powMonoidHom 2 : Kˣ →* Kˣ).range.comap (multiplierHom Q hQ)).map
      (linearConjugationHom Q) ≤ (isometryConjugationHom Q).range := by
    rintro _ ⟨g, ⟨c, hc⟩, rfl⟩
    exact linearConjugationHom_mem_range_of_multiplier_eq_sq Q hQ g c hc.symm
  refine (Subgroup.relIndex_dvd_of_le_left _ hS).trans ?_
  rw [MonoidHom.range_eq_map (linearConjugationHom Q)]
  refine (relIndex_map_dvd_relIndex _ _ _).trans ?_
  rw [Subgroup.relIndex_top_right, Subgroup.index_comap]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

theorem relIndex_linearRange_dvd :
    (linearConjugationHom Q).range.relIndex (matrixProjectiveConjugationHom Q).range ∣
      Nat.card (fieldProjection Q).range := by
  have h : (linearConjugationHom Q).range =
      (linearSimilarityPairs Q).map (matrixProjectiveConjugationHom Q) := by
    rw [linearConjugationHom, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h, MonoidHom.range_eq_map (matrixProjectiveConjugationHom Q)]
  refine (relIndex_map_dvd_relIndex _ _ _).trans ?_
  rw [Subgroup.relIndex_top_right]
  exact (Subgroup.index_ker (fieldProjection Q)).dvd

theorem card_outer_eq :
    Nat.card (Outer (matrixProjectiveDerived Q)) =
      (inner (matrixProjectiveDerived Q)).relIndex (isometryConjugationHom Q).range *
        (isometryConjugationHom Q).range.relIndex (linearConjugationHom Q).range *
        (linearConjugationHom Q).range.relIndex (matrixProjectiveImage Q) *
        (matrixProjectiveImage Q).index := by
  have h1 : inner (matrixProjectiveDerived Q) ≤ (isometryConjugationHom Q).range := by
    rw [inner_eq_map_commutator Q]
    exact Subgroup.map_le_range _ _
  have h2 := isometryConjugationHom_range_le Q
  have h3 : (linearConjugationHom Q).range ≤ matrixProjectiveImage Q := by
    rintro _ ⟨g, rfl⟩
    exact (mem_matrixProjectiveImage_iff Q _).mpr ⟨g.val, rfl⟩
  change (CFSG.ComponentClassification.OuterAutomorphisms.inner
    (matrixProjectiveDerived Q)).index = _
  rw [Subgroup.relIndex_mul_relIndex _ _ _ h1 h2,
    Subgroup.relIndex_mul_relIndex _ _ _ (h1.trans h2) h3,
    Subgroup.relIndex_mul_index (h1.trans (h2.trans h3))]

theorem ordProj_two_card_outer_le [Finite K] (hQ : ∃ v, Q v ≠ 0) {f : ℕ} (hf : f ≠ 0)
    (hK : Nat.card (K ≃+* K) ∣ f) :
    ordProj[2] (Nat.card (Outer (matrixProjectiveDerived Q))) ≤
      Nat.card (Abelianization (matrixIsometries Q)) *
        (powMonoidHom 2 : Kˣ →* Kˣ).range.index * ordProj[2] f *
        ordProj[2] (matrixProjectiveImage Q).index := by
  have hpos : Nat.card (Outer (matrixProjectiveDerived Q)) ≠ 0 := Nat.card_pos.ne'
  have ha := relIndex_inner_dvd Q
  have hb := relIndex_isometryRange_dvd Q hQ
  have hc := (relIndex_linearRange_dvd Q).trans
    ((Subgroup.card_subgroup_dvd_card (fieldProjection Q).range).trans hK)
  rw [card_outer_eq Q] at hpos ⊢
  set a := (inner (matrixProjectiveDerived Q)).relIndex (isometryConjugationHom Q).range
  set b := (isometryConjugationHom Q).range.relIndex (linearConjugationHom Q).range
  set c := (linearConjugationHom Q).range.relIndex (matrixProjectiveConjugationHom Q).range
  set k := (matrixProjectiveImage Q).index
  obtain ⟨habc, hk0⟩ := mul_ne_zero_iff.mp hpos
  obtain ⟨hab, hc0⟩ := mul_ne_zero_iff.mp habc
  obtain ⟨ha0, hb0⟩ := mul_ne_zero_iff.mp hab
  have hA0 : Nat.card (Abelianization (matrixIsometries Q)) ≠ 0 := Nat.card_pos.ne'
  have hS0 : (powMonoidHom 2 : Kˣ →* Kˣ).range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [Nat.ordProj_mul 2 habc hk0, Nat.ordProj_mul 2 hab hc0, Nat.ordProj_mul 2 ha0 hb0]
  refine Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ?_ ?_) ?_) le_rfl
  · exact (Nat.ordProj_le 2 ha0).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hA0) ha)
  · exact (Nat.ordProj_le 2 hb0).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hS0) hb)
  · exact ordProj_two_le_of_dvd hf hc

end Semilinear

section Reindex

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

theorem matrixIsometries_reindex_eq_comap (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K)) :
    matrixIsometries (reindexQuadraticForm e Q₀) =
      (TauCeti.QuadraticMap.orthogonalGroup Q₀).comap
        ((reindexMatrixEquiv e).symm.trans (toLinEquiv ι K)).toMonoidHom := by
  ext A
  obtain ⟨B, rfl⟩ := (reindexMatrixEquiv e).surjective A
  rw [reindexMatrixEquiv_mem_isometries]
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]

@[expose] def matrixIsometriesReindexEquiv (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K)) :
    matrixIsometries (reindexQuadraticForm e Q₀) ≃*
      TauCeti.QuadraticMap.orthogonalGroup Q₀ where
  toFun A := ⟨((reindexMatrixEquiv e).symm.trans (toLinEquiv ι K)) A,
    (SetLike.ext_iff.mp (matrixIsometries_reindex_eq_comap e Q₀) A.val).mp A.property⟩
  invFun B := ⟨((reindexMatrixEquiv e).symm.trans (toLinEquiv ι K)).symm B, by
    rw [matrixIsometries_reindex_eq_comap, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    exact B.property⟩
  left_inv A := Subtype.ext (MulEquiv.symm_apply_apply _ _)
  right_inv B := Subtype.ext (MulEquiv.apply_symm_apply _ _)
  map_mul' A B := Subtype.ext (map_mul ((reindexMatrixEquiv e).symm.trans (toLinEquiv ι K))
    A.val B.val)

theorem card_abelianization_matrixIsometries_reindex (e : ι ≃ Fin d)
    (Q₀ : QuadraticForm K (ι → K)) :
    Nat.card (Abelianization (matrixIsometries (reindexQuadraticForm e Q₀))) =
      Nat.card (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q₀)) :=
  Nat.card_congr (MulEquiv.abelianizationCongr (matrixIsometriesReindexEquiv e Q₀)).toEquiv

theorem ordProj_two_card_outer_reindex_le [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hab : IsometryAbelianizationBound p Q₀) {Qc : QuadraticForm K (Fin d → K)}
    (hQc : Qc = reindexQuadraticForm e Q₀) (hQ : Qc ≠ 0) :
    (p = 2 → ordProj[2] (Nat.card (Outer (matrixProjectiveDerived Qc))) ≤
        2 * ordProj[2] f * ordProj[2] (matrixProjectiveImage Qc).index) ∧
      (p ≠ 2 → ordProj[2] (Nat.card (Outer (matrixProjectiveDerived Qc))) ≤
        8 * ordProj[2] f * ordProj[2] (matrixProjectiveImage Qc).index) := by
  subst hQc
  have hbound := ordProj_two_card_outer_le (reindexQuadraticForm e Q₀)
    (exists_nonzero_value _ hQ) (f := f) (by omega) (card_ringAut_and_isCyclic hp K hK).1.dvd
  rw [card_abelianization_matrixIsometries_reindex] at hbound
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = Nat.gcd (Nat.card K - 1) 2 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
  rw [hsq] at hbound
  obtain ⟨-, hodd, htwo⟩ := hab
  set k₂ := ordProj[2] (matrixProjectiveImage (reindexQuadraticForm e Q₀)).index
  set f₂ := ordProj[2] f
  set A := Nat.card (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q₀))
  refine ⟨fun hp2 => ?_, fun hp2 => ?_⟩
  · have hgcd : Nat.gcd (Nat.card K - 1) 2 = 1 := by
      apply Nat.coprime_two_right.mpr
      rw [hK, hp2]
      exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two)
        odd_one
    rw [hgcd, mul_one] at hbound
    calc _ ≤ A * f₂ * k₂ := hbound
      _ ≤ 2 * f₂ * k₂ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (htwo hp2))
  · have hgcd : Nat.gcd (Nat.card K - 1) 2 ≤ 2 := Nat.gcd_le_right _ (by norm_num)
    calc _ ≤ A * Nat.gcd (Nat.card K - 1) 2 * f₂ * k₂ := hbound
      _ ≤ 4 * 2 * f₂ * k₂ :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul (hodd hp2) hgcd))
      _ = 8 * f₂ * k₂ := by norm_num

end Reindex

theorem exists_outer_two_part_le (T : Type) [Group T] (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ)
    (h : StatedClassicalModel T t n p f) :
    ∃ k : ℕ, (p = 2 → ordProj[2] (Nat.card (Outer T)) ≤ 2 * ordProj[2] f * k) ∧
      (p ≠ 2 → ordProj[2] (Nat.card (Outer T)) ≤ 8 * ordProj[2] f * k) ∧ k ≤ 2 ∧
      (¬(t = .POmegaPlus ∧ n = 4) → k = 1) := by
  have h1 : ordProj[2] 1 = 1 := ordProj_two_eq_one_of_odd odd_one
  rcases ht with rfl | rfl | rfl
  ·
    have h0 := h
    obtain ⟨⟨hp, hf, hn, hp2⟩, K, _, _, hK, ⟨e⟩⟩ := h0
    have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaOdd (.inl rfl) n p f
      h K hK (quadOdd n K) (coe_quadOdd n K) e
    have hE : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ := by
      rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaOdd (.inl rfl) n p f
        h) K hK e).1]
      exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T .POmegaOdd
        (.inl rfl) n p f h) K hK).2
    have hout : Nat.card (Outer T) =
        Nat.card (Outer (matrixProjectiveDerived (coordinateQuadOdd n K))) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
        (coordinateOddWitnessEquiv K e)).toEquiv
    obtain ⟨-, hodd⟩ := ordProj_two_card_outer_reindex_le hp hf hK (oddIndexEquiv n)
      (quadOdd n K) hab (Qc := coordinateQuadOdd n K) rfl
      (coordinate_model_intrinsic_odd h K hK e).1
    rw [hE, Subgroup.index_top, h1, ← hout] at hodd
    exact ⟨1, fun h2 => absurd h2 hp2, hodd, by norm_num, fun _ => rfl⟩
  ·
    have h0 := h
    obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h0
    have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
      (.inr (.inl rfl)) n p f h K hK (quadPlus n K) (coe_quadPlus n K) e
    have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaPlus
      (.inr (.inl rfl)) n p f h) K hK e).1
    have horbit := orthogonal_geometry_plus_point_family_orbit h hK e
    have hout : Nat.card (Outer T) =
        Nat.card (Outer (matrixProjectiveDerived (coordinateQuadPlus n K))) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
        (coordinatePlusWitnessEquiv K e)).toEquiv
    obtain ⟨h2, hodd⟩ := ordProj_two_card_outer_reindex_le hp hf hK (plusIndexEquiv n)
      (quadPlus n K) hab (Qc := coordinateQuadPlus n K) rfl
      (coordinate_model_intrinsic_plus h K hK e).1
    rw [← hout] at h2 hodd
    have htop : 5 ≤ n → (matrixProjectiveImage (coordinateQuadPlus n K)).index = 1 := by
      intro h5
      rw [← hEA, horbit.2.2.2.2.1 h5, Subgroup.index_top]
    have hidx : (matrixProjectiveImage (coordinateQuadPlus n K)).index ≤ 3 := by
      rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
      · have hst : (projectivePointFamilyAut (coordinateQuadPlus n K)).index =
            (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
              (projectivePointFamily (coordinateQuadPlus n K))).ncard :=
          MulAction.index_stabilizer _ _
        rw [← hEA, hst]
        exact (horbit.2.2.2.2.2 h4).2
      · rw [htop h5]
        norm_num
    refine ⟨_, h2, hodd, ordProj_two_le_two_of_le_three hidx, fun hnp => ?_⟩
    rw [htop (by by_contra hlt; exact hnp ⟨rfl, by omega⟩), h1]
  ·
    have h0 := h
    obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
    have hn1 : 1 ≤ n := by omega
    have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaMinus
      (.inr (.inr rfl)) n p f h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
    have hE : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ := by
      rw [← ((orthogonal_geometry_model_stabilizer_preserving_image T .POmegaMinus
        (.inr (.inr rfl)) n p f h) hn1 K hK b c hirr e).1]
      exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant T
        .POmegaMinus (.inr rfl) n p f h) hn1 K hK b c hirr).2
    have hout : Nat.card (Outer T) =
        Nat.card (Outer (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c))) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
        (coordinateMinusWitnessEquiv K hn1 b c e)).toEquiv
    obtain ⟨h2, hodd⟩ := ordProj_two_card_outer_reindex_le hp hf hK (minusIndexEquiv n hn1)
      (quadMinus n K b c) hab (Qc := coordinateQuadMinus n K hn1 b c) rfl
      (coordinate_model_intrinsic_minus h K hK b c hirr e).1
    rw [hE, Subgroup.index_top, h1, ← hout] at h2 hodd
    exact ⟨1, h2, hodd, by norm_num, fun _ => rfl⟩

end OrthogonalOuter

open OrthogonalOuter CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem orthogonal_model_outer_two_part_bound (T : Type) [Group T] (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n p f : ℕ)
    (h : StatedClassicalModel T t n p f) :
    4 ≤ ordProj[2] (Nat.card T) ∧
      ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T) ∧
      (p = 2 → ordProj[2] (Nat.card (Outer T)) ≤ 4 * ordProj[2] f) ∧
      (p ≠ 2 → ¬(t = .POmegaPlus ∧ n = 4) →
        ordProj[2] (Nat.card (Outer T)) ≤ 8 * ordProj[2] f) ∧
      (p ≠ 2 → t = .POmegaPlus → n = 4 →
        ordProj[2] (Nat.card (Outer T)) ≤ 16 * ordProj[2] f) := by
  obtain ⟨k, hk2, hkodd, hk, hk1⟩ := exists_outer_two_part_le T t ht n p f h
  obtain ⟨hlow2, hlowodd, hlowplus⟩ := orthogonal_model_linear_subgroup_two_part_lower_bound ht h
  have hf : 1 ≤ f := h.1.2.1
  obtain ⟨hf1, -⟩ := (lie_order_two_adic_arithmetic).2.2 f hf
  have hf2pos : 0 < ordProj[2] f := Nat.ordProj_pos f 2
  set o := ordProj[2] (Nat.card (Outer T))
  set a := ordProj[2] (Nat.card T)
  set f₂ := ordProj[2] f
  rcases eq_or_ne p 2 with rfl | hp2
  ·
    have ho : o ≤ 4 * f₂ := by
      calc o ≤ 2 * f₂ * k := hk2 rfl
        _ ≤ 2 * f₂ * 2 := Nat.mul_le_mul_left _ hk
        _ = 4 * f₂ := by ring
    have ha := hlow2 rfl
    have hX : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hcube : 4 * 2 ^ f ≤ (2 ^ f) ^ 3 := by
      calc 4 * 2 ^ f ≤ (2 ^ f * 2 ^ f) * 2 ^ f :=
            Nat.mul_le_mul_right _ ((by norm_num : 4 ≤ 2 * 2).trans (Nat.mul_le_mul hX hX))
        _ = (2 ^ f) ^ 3 := by ring
    exact ⟨by omega, by omega, fun _ => ho, fun h2 => absurd rfl h2, fun h2 => absurd rfl h2⟩
  ·
    have hlow := hlowodd hp2
    have ho16 : o ≤ 16 * f₂ := by
      calc o ≤ 8 * f₂ * k := hkodd hp2
        _ ≤ 8 * f₂ * 2 := Nat.mul_le_mul_left _ hk
        _ = 16 * f₂ := by ring
    have ho8 : ¬(t = .POmegaPlus ∧ n = 4) → o ≤ 8 * f₂ := fun hnp => by
      have := hkodd hp2
      rw [hk1 hnp, mul_one] at this
      exact this
    have hlt : o < a := by
      by_cases hplus : t = .POmegaPlus ∧ n = 4
      · have h128 := hlowplus hp2 hplus.1
        have hsq : f₂ ≤ f₂ ^ 2 := Nat.le_self_pow (by norm_num) f₂
        omega
      · have := ho8 hplus
        omega
    exact ⟨by omega, hlt, fun h2 => absurd h2 hp2, fun _ => ho8, fun _ _ _ => ho16⟩

end CFSG.LocalAnalysis.ComponentInitial
