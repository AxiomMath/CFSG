module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294DeltaBase
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294DeltaThreePoint
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Orthogonal
public import CFSG.RankThree.PartOne.KLC.D4OutCentral
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1POddOut

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThree.PartTwo.Census
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower (comm_mem_of_series)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open scoped commutatorElement Pointwise

theorem comm_mem_inner_of_mem_projectiveImage {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {α x : MulAut (matrixProjectiveDerived Q)} (hα : α ∈ matrixProjectiveImage Q)
    (hx : x ∈ matrixProjectiveImage Q) {k : ℕ} (hk : α ^ p ^ k = 1) :
    x * α * x⁻¹ * α⁻¹ ∈ inner (matrixProjectiveDerived Q) := by
  have hQv := exists_nonzero_value Q hQ
  have hNO : inner (matrixProjectiveDerived Q) ≤ (isometryConjugationHom Q).range := by
    rw [inner_eq_map_commutator Q]
    exact Subgroup.map_le_range _ _
  have hOD := isometryConjugationHom_range_le Q
  have hDE : (linearConjugationHom Q).range ≤ matrixProjectiveImage Q := by
    rintro _ ⟨g, rfl⟩
    exact (mem_matrixProjectiveImage_iff Q _).mpr ⟨g.val, rfl⟩
  have hOE : ∀ e ∈ matrixProjectiveImage Q, ∀ o ∈ (isometryConjugationHom Q).range,
      e * o * e⁻¹ ∈ (isometryConjugationHom Q).range := by
    rintro e he _ ⟨A, rfl⟩
    obtain ⟨g, rfl⟩ := (mem_matrixProjectiveImage_iff Q _).1 he
    have hmem : g * matrixIsometryInclusion Q A * g⁻¹ ∈ matrixIsometryPairs Q :=
      (matrixIsometryPairs_normal Q).conj_mem _ ⟨A, rfl⟩ g
    obtain ⟨A', hA'⟩ := hmem
    refine ⟨A', ?_⟩
    change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q A') = _
    rw [hA']
    simp only [map_mul, map_inv]
    rfl
  have hEE : ∀ a ∈ matrixProjectiveImage Q, ∀ b ∈ matrixProjectiveImage Q,
      a * b * a⁻¹ * b⁻¹ ∈ (linearConjugationHom Q).range := by
    intro a ha b hb
    obtain ⟨g₁, rfl⟩ := (mem_matrixProjectiveImage_iff Q _).1 ha
    obtain ⟨g₂, rfl⟩ := (mem_matrixProjectiveImage_iff Q _).1 hb
    change ⁅matrixProjectiveConjugationHom Q g₁, matrixProjectiveConjugationHom Q g₂⁆ ∈ _
    rw [← map_commutatorElement]
    refine ⟨⟨⁅g₁, g₂⁆, ?_⟩, rfl⟩
    rw [mem_linearSimilarityPairs_iff]
    change fieldProjection Q ⁅g₁, g₂⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact CFSG.RankThree.PartOne.OutStructure.ringAut_comm K _ _
  have hO4 : (inner (matrixProjectiveDerived Q)).relIndex (isometryConjugationHom Q).range ≤ 4 :=
    (Nat.le_of_dvd Nat.card_pos (relIndex_inner_dvd Q)).trans hab
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index ≤ 2 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
    exact Nat.gcd_le_right _ two_pos
  have hsq0 : 0 < (powMonoidHom 2 : Kˣ →* Kˣ).range.index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hD2 : (isometryConjugationHom Q).range.relIndex (linearConjugationHom Q).range ≤ 2 :=
    (Nat.le_of_dvd hsq0 (relIndex_isometryRange_dvd Q hQv)).trans hsq
  haveI : Finite (matrixProjectiveDerived Q) := inferInstance
  haveI : Finite (MulAut (matrixProjectiveDerived Q)) :=
    CFSG.RankThree.PartOne.OutStructure.instFiniteMulAut' _
  haveI : (inner (matrixProjectiveDerived Q)).Normal := inner_normal _
  exact comm_mem_of_series (inner (matrixProjectiveDerived Q)) (isometryConjugationHom Q).range
    (linearConjugationHom Q).range (matrixProjectiveImage Q) hNO hOD hDE hOE hEE hO4 hD2 hp hp5
    hα hk hx

theorem DeltaTowerAt.of_projectiveImage_top {K : Type} [Field K] [Finite K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4)
    (htop : matrixProjectiveImage Q = ⊤) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    DeltaTowerAt p (matrixProjectiveDerived Q) :=
  DeltaTowerAt.of_pComm fun γ α ⟨_, hk⟩ =>
    comm_mem_inner_of_mem_projectiveImage Q hQ hab hp hp5 (by rw [htop]; trivial)
      (by rw [htop]; trivial) hk

theorem DeltaTowerAt.of_statedPlus_five {X : Type} [Group X] {n ℓ f : ℕ} (hn : 5 ≤ n)
    (h : StatedClassicalModel X .POmegaPlus n ℓ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    DeltaTowerAt p X := by
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, -⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.orthPlus_hyps h K hK e
  exact DeltaTowerAt.of_mulEquiv (coordinatePlusWitnessEquiv K e)
    (DeltaTowerAt.of_projectiveImage_top _ hQ hab
      (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn) hp hp5)

theorem DeltaTowerAt.of_statedMinus {X : Type} [Group X] {n ℓ f : ℕ}
    (h : StatedClassicalModel X .POmegaMinus n ℓ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    DeltaTowerAt p X := by
  have h0 := h
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hab, -⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.orthMinus_hyps h K hK b c hirr hn1 e
  exact DeltaTowerAt.of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e)
    (DeltaTowerAt.of_projectiveImage_top _ hQ hab
      (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr)
      hp hp5)

theorem DeltaTowerAt.of_statedOdd {X : Type} [Group X] {n ℓ f : ℕ}
    (h : StatedClassicalModel X .POmegaOdd n ℓ f) {p : ℕ} : DeltaTowerAt p X := by
  obtain ⟨⟨hℓ, hf, hn3, hℓ2⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K ℓ]
    exact hℓ2
  refine DeltaTowerAt.of_mulEquiv (coordinateOddWitnessEquiv K e) (DeltaTowerAt.of_outerComm ?_)
  intro γ α
  exact CFSG.ComponentClassification.HarrisLit.T1.commutator_mem_inner_coordinateQuadOdd K n
    hchar hn3 γ α

theorem DeltaTowerAt.of_statedPlus_four {X : Type} [Group X] {ℓ f : ℕ}
    (h : StatedClassicalModel X .POmegaPlus 4 ℓ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    DeltaTowerAt p X := by
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, -⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.orthPlus_hyps h K hK e
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e).1
  have hsub := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  obtain ⟨κ, hκF, hκy, hκz, hyz⟩ := CFSG.RankThree.PartOne.KLC.swap_data_coordinate K
  refine DeltaTowerAt.of_mulEquiv (coordinatePlusWitnessEquiv K e) (DeltaTowerAt.of_pComm ?_)
  intro γ α ⟨k, hk⟩
  have hO : ∀ a : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      a • projectivePointFamily (coordinateQuadPlus 4 K) =
          projectivePointFamily (coordinateQuadPlus 4 K) ∨
        a • projectivePointFamily (coordinateQuadPlus 4 K) = plusCX 4 K ∨
        a • projectivePointFamily (coordinateQuadPlus 4 K) = plusCXstar 4 K (by omega) := by
    intro a
    have := hsub (MulAction.mem_orbit _ a)
    simpa using this
  have hE : ∀ a b : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      a • projectivePointFamily (coordinateQuadPlus 4 K) =
          projectivePointFamily (coordinateQuadPlus 4 K) →
        b • projectivePointFamily (coordinateQuadPlus 4 K) =
          projectivePointFamily (coordinateQuadPlus 4 K) → (∃ k : ℕ, b ^ p ^ k = 1) →
          ⁅a, b⁆ ∈ inner (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
    intro a b ha hb ⟨k, hk⟩
    refine comm_mem_inner_of_mem_projectiveImage _ hQ hab hp hp5 ?_ ?_ hk
    · rw [← hEA]
      exact (mem_projectivePointFamilyAut_iff _ _).2 hb
    · rw [← hEA]
      exact (mem_projectivePointFamilyAut_iff _ _).2 ha
  exact commutator_mem_of_three_point_pElement
    (inner (matrixProjectiveDerived (coordinateQuadPlus 4 K))) hO hκF hκy hκz hyz hp hp5 hE hk γ

end CFSG.LocalAnalysis.RankFourTheoremC
