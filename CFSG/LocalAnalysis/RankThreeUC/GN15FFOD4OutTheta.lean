module

public import CFSG.RankThree.PartOne.KLC.D4OutCentral
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Out

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open Subgroup
open scoped commutatorElement Pointwise
open CFSG.RankThree.PartOne.OutStructure (Inn)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open CFSG.Open
open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KLC
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LieType.Universal.Spin

private theorem endNodeFamilies_transport_explicit {X P : Type} [Group X] [Group P] (φ : X ≃* P)
    {F y z : Set (Subgroup P)} (hyz : y ≠ z)
    (hO : ∀ a : MulAut P, a • F = F ∨ a • F = y ∨ a • F = z)
    {κ : MulAut P} (hκF : κ • F = F) (hκy : κ • y = z) (hκz : κ • z = y)
    (hN : ∀ n ∈ Inn P, n • F = F)
    (hE : ∀ a b : MulAut P, a • F = F → b • F = F → ⁅a, b⁆ ∈ Inn P) :
    familyTransport φ.symm y ≠ familyTransport φ.symm z ∧
      (∀ g : MulAut X, g • familyTransport φ.symm F = familyTransport φ.symm F ∨
        g • familyTransport φ.symm F = familyTransport φ.symm y ∨
        g • familyTransport φ.symm F = familyTransport φ.symm z) ∧
      (∃ κ' : MulAut X, κ' • familyTransport φ.symm F = familyTransport φ.symm F ∧
        κ' • familyTransport φ.symm y = familyTransport φ.symm z ∧
        κ' • familyTransport φ.symm z = familyTransport φ.symm y) ∧
      (∀ n ∈ Inn X, n • familyTransport φ.symm F = familyTransport φ.symm F) ∧
      (∀ g k : MulAut X, g • familyTransport φ.symm F = familyTransport φ.symm F →
        k • familyTransport φ.symm F = familyTransport φ.symm F → ⁅g, k⁆ ∈ Inn X) := by
  have hφ : ∀ a : MulAut X, MulAut.congr φ.symm (MulAut.congr φ a) = a := by
    intro a
    ext x
    simp [MulAut.congr_apply]
  have htr : ∀ (S : Set (Subgroup P)) (a : MulAut X),
      familyTransport φ.symm (MulAut.congr φ a • S) = a • familyTransport φ.symm S := by
    intro S a
    rw [familyTransport_automorphism, hφ]
  have hinner : (Inn X).map (MulAut.congr φ).toMonoidHom = Inn P :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ
  have hmem : ∀ a : MulAut X, a ∈ Inn X ↔ MulAut.congr φ a ∈ Inn P := by
    intro a
    rw [← hinner]
    constructor
    · exact fun h => ⟨a, h, rfl⟩
    · rintro ⟨b, hb, hba⟩
      exact (MulAut.congr φ).injective hba ▸ hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hyz ((familyTransport φ.symm).injective h)
  · intro g
    rcases hO (MulAut.congr φ g) with h | h | h
    · left
      rw [← htr F g, h]
    · right; left
      rw [← htr F g, h]
    · right; right
      rw [← htr F g, h]
  · refine ⟨MulAut.congr φ.symm κ, ?_, ?_, ?_⟩
    · rw [← familyTransport_automorphism φ.symm F κ, hκF]
    · rw [← familyTransport_automorphism φ.symm y κ, hκy]
    · rw [← familyTransport_automorphism φ.symm z κ, hκz]
  · intro n hn
    rw [← htr F n, hN _ ((hmem n).mp hn)]
  · intro g k hg hk
    have hgP : MulAut.congr φ g • F = F := by
      apply (familyTransport φ.symm).injective
      rw [htr F g, hg]
    have hkP : MulAut.congr φ k • F = F := by
      apply (familyTransport φ.symm).injective
      rw [htr F k, hk]
    rw [hmem, map_commutatorElement]
    exact hE _ _ hgP hkP

theorem outer_action_of_inverted_of_mulEquiv {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    [CharP K 2] (θ : X ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {α β : MulAut X}
    (hα : α ^ 3 ∈ Inn X) (hαN : α ∉ Inn X) (hβ : β * α * β⁻¹ = α⁻¹) :
    ∃ P Q R : Set (Subgroup X), P ≠ Q ∧ Q ≠ R ∧ P ≠ R ∧
      (∀ g : MulAut X, ∀ S ∈ ({P, Q, R} : Set (Set (Subgroup X))),
        g • S ∈ ({P, Q, R} : Set (Set (Subgroup X)))) ∧
      (∀ n ∈ Inn X, n • P = P ∧ n • Q = Q ∧ n • R = R) ∧
      β • P = P ∧ β • Q = R ∧ β • R = Q ∧
      ((α • P = Q ∧ α • Q = R ∧ α • R = P) ∨ (α • P = R ∧ α • R = Q ∧ α • Q = P)) ∧
      (∀ γ : MulAut X, γ * β = β * γ →
        (γ • P = P ∧ γ • Q = Q ∧ γ • R = R) ∨ (γ • P = P ∧ γ • Q = R ∧ γ • R = Q)) ∧
      (familyTransport θ).symm (projectivePointFamily (coordinateQuadPlus 4 K)) ∈
        ({P, Q, R} : Set (Set (Subgroup X))) := by
  classical
  obtain ⟨m, -, hKcard⟩ := @FiniteField.card K _ (Fintype.ofFinite K) 2 _
  have hm1 : 1 ≤ (m : ℕ) := Nat.one_le_iff_ne_zero.mpr m.pos.ne'
  have hK : Nat.card K = 2 ^ (m : ℕ) := by
    rw [@Nat.card_eq_fintype_card K (Fintype.ofFinite K), hKcard]
  let reindex : StatedProj (StatedOmega (StatedQuadPlus 4 K)) ≃*
      matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
    statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)
  let e₀ : X ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) := θ.trans reindex.symm
  let h : StatedClassicalModel X .POmegaPlus 4 2 m :=
    ⟨⟨Nat.prime_two, hm1, le_rfl⟩, K, inferInstance, inferInstance, hK, ⟨e₀⟩⟩
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e₀
  have hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) 4 2 m h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e₀
  have hA : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 2 := by
    rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e₀).1
  have hsub := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  obtain ⟨κ, hκF, hκy, hκz, hyz⟩ := swap_data_coordinate K
  have hO_c : ∀ a : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      a • projectivePointFamily (coordinateQuadPlus 4 K) =
          projectivePointFamily (coordinateQuadPlus 4 K) ∨
        a • projectivePointFamily (coordinateQuadPlus 4 K) = plusCX 4 K ∨
        a • projectivePointFamily (coordinateQuadPlus 4 K) = plusCXstar 4 K (by omega) := by
    intro a
    have := hsub (MulAction.mem_orbit _ a)
    simpa using this
  have hN_c : ∀ n ∈ Inn (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      n • projectivePointFamily (coordinateQuadPlus 4 K) =
        projectivePointFamily (coordinateQuadPlus 4 K) := by
    rintro _ ⟨g, rfl⟩
    exact inner_smul_pointFamily_coordinate K g
  have hE_c : ∀ a b : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      a • projectivePointFamily (coordinateQuadPlus 4 K) =
          projectivePointFamily (coordinateQuadPlus 4 K) →
        b • projectivePointFamily (coordinateQuadPlus 4 K) =
          projectivePointFamily (coordinateQuadPlus 4 K) →
        ⁅a, b⁆ ∈ Inn (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
    intro a b ha hb
    refine matrixProjectiveImage_commutator_mem_inner _ hQ hA ?_ ?_
    · rw [← hEA]
      exact (mem_projectivePointFamilyAut_iff _ _).2 ha
    · rw [← hEA]
      exact (mem_projectivePointFamilyAut_iff _ _).2 hb
  obtain ⟨hyz', hO', ⟨κ', hκ'F, hκ'y, hκ'z⟩, hN', hE'⟩ :=
    endNodeFamilies_transport_explicit θ hyz hO_c hκF hκy hκz hN_c hE_c
  obtain ⟨P, Q, R, hPQR, hPQ, hQR, hPR, hβP, hβQ, hβR, hαcyc, hγ⟩ :=
    threeCycle_of_inverted (Inn X) hO' hκ'F hκ'y hκ'z hyz' hN' hE' hα hαN hβ
  have hgen : ({P, Q, R} : Set (Set (Subgroup X))) =
      {familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K)),
        α • familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K)),
        α ^ 2 • familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K))} := by
    have hFmem : familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K)) ∈
        ({P, Q, R} : Set (Set (Subgroup X))) := by
      rw [hPQR]
      simp
    rcases hαcyc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      rcases hFmem with hF | hF | hF
    · rw [hF, h1, show α ^ 2 • P = R by rw [pow_two, mul_smul, h1, h2]]
    · rw [hF, h2, show α ^ 2 • Q = P by rw [pow_two, mul_smul, h2, h3]]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · rw [hF, h3, show α ^ 2 • R = Q by rw [pow_two, mul_smul, h3, h1]]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · rw [hF, h1, show α ^ 2 • P = Q by rw [pow_two, mul_smul, h1, h2]]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · rw [hF, h3, show α ^ 2 • Q = R by rw [pow_two, mul_smul, h3, h1]]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · rw [hF, h2, show α ^ 2 • R = P by rw [pow_two, mul_smul, h2, h3]]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
  refine ⟨P, Q, R, hPQ, hQR, hPR, ?_, ?_, hβP, hβQ, hβR, hαcyc, hγ, ?_⟩
  · intro g S hS
    rw [hgen] at hS
    rcases hS with hS | hS | hS
    · rw [hS]
      have := hO' g
      simpa [hPQR] using this
    · rw [hS]
      rw [show g • (α • familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K))) =
          (g * α) • familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K))
          from smul_smul g α _]
      have := hO' (g * α)
      simpa [hPQR] using this
    · rw [hS]
      rw [show g • (α ^ 2 • familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K))) =
          (g * α ^ 2) • familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K))
          from smul_smul g (α ^ 2) _]
      have := hO' (g * α ^ 2)
      simpa [hPQR] using this
  · intro n hn
    have hfix : ∀ g : MulAut X,
        n • (g • familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K))) =
          g • familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K)) := by
      intro g
      have hconj : g⁻¹ * n * g ∈ Inn X := by
        simpa using (inferInstance : (Inn X).Normal).conj_mem n hn g⁻¹
      calc n • (g • familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K))) =
          (n * g) • familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K)) :=
            smul_smul n g _
        _ = (g * (g⁻¹ * n * g)) •
            familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K)) := by
          rw [show n * g = g * (g⁻¹ * n * g) from by group]
        _ = g • ((g⁻¹ * n * g) •
            familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K))) :=
            (smul_smul g (g⁻¹ * n * g) _).symm
        _ = g • familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K)) := by
          rw [hN' _ hconj]
    have hSfix : ∀ S ∈ ({P, Q, R} : Set (Set (Subgroup X))), n • S = S := by
      intro S hS
      rw [hgen] at hS
      rcases hS with hS | hS | hS
      · rw [hS]
        simpa using hfix 1
      · rw [hS]
        exact hfix α
      · rw [hS]
        exact hfix (α ^ 2)
    exact ⟨hSfix P (by simp), hSfix Q (by simp), hSfix R (by simp)⟩
  · have hFsymm : (familyTransport θ).symm (projectivePointFamily (coordinateQuadPlus 4 K)) =
        familyTransport θ.symm (projectivePointFamily (coordinateQuadPlus 4 K)) := rfl
    rw [hFsymm, hPQR]
    simp

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
