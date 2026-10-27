module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerD4Layers
public import CFSG.RankThree.PartOne.KLC.D4OutCentral
public import CFSG.RankThree.PartOne.MB3.OddOutOrthogonal

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.RankThree.PartOne.OutStructure (Inn orthD exists_gen mem_orthD_iff
  orthD_relIndex_inner_not_dvd linearConjugationHom_range_eq_orthD)
open scoped commutatorElement

section Quotient

variable {G : Type*} [Group G]

theorem card_map_mk'_eq_relIndex (N K : Subgroup G) [N.Normal] :
    Nat.card (K.map (QuotientGroup.mk' N)) = N.relIndex K := by
  have h1 : ((QuotientGroup.mk' N).comp K.subtype).range = K.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h2 : ((QuotientGroup.mk' N).comp K.subtype).ker = N.subgroupOf K := by
    ext x
    simp [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rw [← h1, ← Subgroup.index_ker, h2]
  rfl

theorem commutator_mem_of_layers [Finite G] (N K D E : Subgroup G) [N.Normal]
    (hKE : ∀ e ∈ E, ∀ k ∈ K, e * k * e⁻¹ ∈ K) (hDE : ∀ e ∈ E, ∀ d ∈ D, e * d * e⁻¹ ∈ D)
    (hK4 : N.relIndex K ≤ 4) (hD2 : K.relIndex D ≤ 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hDp : ¬ p ∣ N.relIndex D) {u : G} (hcyc : ∀ e ∈ E, ∃ j : ℤ, u ^ j * e ∈ D)
    {a b : G} (ha : a ∈ E) (hb : b ∈ E) {m : ℕ} (hbm : b ^ p ^ m ∈ N) : ⁅a, b⁆ ∈ N := by
  classical
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have h1 : π ⁅a, b⁆ = 1 := by
    have key := central_of_layers (G := G ⧸ N) (K := K.map π) (D := D.map π) (E := E.map π)
      (u := π u) (a := π a) (b := π b) (p := p) (m := m) ?_ ?_ ?_ ?_ hp hp5 ?_ ?_ ?_ ?_ ?_
    · rw [map_commutatorElement]
      exact key
    · rintro _ ⟨e, he, rfl⟩ _ ⟨k, hk, rfl⟩
      exact ⟨e * k * e⁻¹, hKE e he k hk, by simp⟩
    · rintro _ ⟨e, he, rfl⟩ _ ⟨d, hd, rfl⟩
      exact ⟨e * d * e⁻¹, hDE e he d hd, by simp⟩
    · rw [card_map_mk'_eq_relIndex]
      exact hK4
    · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (relIndex_map_dvd_relIndex π K D)).trans hD2
    · rw [card_map_mk'_eq_relIndex]
      exact hDp
    · rintro _ ⟨e, he, rfl⟩
      obtain ⟨j, hj⟩ := hcyc e he
      exact ⟨j, ⟨u ^ j * e, hj, by simp⟩⟩
    · exact Subgroup.mem_map_of_mem π ha
    · exact Subgroup.mem_map_of_mem π hb
    · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hbm
  exact (QuotientGroup.eq_one_iff _).1 h1

end Quotient

section Orthogonal

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem conj_mem_isometryRange {e k : MulAut (matrixProjectiveDerived Q)}
    (he : e ∈ matrixProjectiveImage Q) (hk : k ∈ (isometryConjugationHom Q).range) :
    e * k * e⁻¹ ∈ (isometryConjugationHom Q).range := by
  obtain ⟨g, rfl⟩ := (mem_matrixProjectiveImage_iff Q e).1 he
  obtain ⟨A, rfl⟩ := hk
  obtain ⟨B, hB⟩ := (matrixIsometryPairs_normal Q).conj_mem (matrixIsometryInclusion Q A)
    ⟨A, rfl⟩ g
  refine ⟨B, ?_⟩
  change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q B) = _
  rw [hB, map_mul, map_mul, map_inv]
  rfl

theorem conj_mem_orthD {e d : MulAut (matrixProjectiveDerived Q)}
    (he : e ∈ matrixProjectiveImage Q) (hd : d ∈ orthD Q) : e * d * e⁻¹ ∈ orthD Q := by
  obtain ⟨g, rfl⟩ := (mem_matrixProjectiveImage_iff Q e).1 he
  obtain ⟨ℓ, rfl⟩ := (mem_orthD_iff Q d).1 hd
  refine (mem_orthD_iff Q _).2
    ⟨⟨g * ℓ.val * g⁻¹, (linearPairsNormal Q).conj_mem ℓ.val ℓ.property g⟩, ?_⟩
  simp [map_mul, map_inv]
  rfl

variable [Finite K]

theorem exists_zpow_mul_mem_orthD :
    ∃ u : MulAut (matrixProjectiveDerived Q), ∀ e ∈ matrixProjectiveImage Q,
      ∃ j : ℤ, u ^ j * e ∈ orthD Q := by
  obtain ⟨g₀, hg₀⟩ := exists_gen Q
  refine ⟨matrixProjectiveConjugationHom Q g₀, fun e he => ?_⟩
  obtain ⟨h, rfl⟩ := (mem_matrixProjectiveImage_iff Q e).1 he
  obtain ⟨k, hk⟩ := hg₀ h
  refine ⟨k, (mem_orthD_iff Q _).2 ⟨⟨g₀ ^ k * h, hk⟩, ?_⟩⟩
  rw [map_mul, map_zpow]
  rfl

theorem commutator_mem_inner_of_pElement (hQ : ∃ v, Q v ≠ 0)
    (hab : Nat.card (Abelianization (matrixIsometries Q)) ≤ 4) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {a b : MulAut (matrixProjectiveDerived Q)} (ha : a ∈ matrixProjectiveImage Q)
    (hb : b ∈ matrixProjectiveImage Q) {m : ℕ} (hbm : b ^ p ^ m ∈ Inn (matrixProjectiveDerived Q)) :
    ⁅a, b⁆ ∈ Inn (matrixProjectiveDerived Q) := by
  have : Finite (matrixProjectiveDerived Q) := inferInstance
  have : Finite (MulAut (matrixProjectiveDerived Q)) := inferInstance
  obtain ⟨u, hu⟩ := exists_zpow_mul_mem_orthD Q
  refine commutator_mem_of_layers (Inn (matrixProjectiveDerived Q)) (isometryConjugationHom Q).range
    (orthD Q) (matrixProjectiveImage Q) (fun e he k hk => conj_mem_isometryRange Q he hk)
    (fun e he d hd => conj_mem_orthD Q he hd) ?_ ?_ hp hp5
    (orthD_relIndex_inner_not_dvd Q hQ hab hp hp5) hu ha hb hbm
  · have : Finite (Abelianization (matrixIsometries Q)) := inferInstance
    exact (Nat.le_of_dvd Nat.card_pos (relIndex_inner_dvd Q)).trans hab
  · rw [← linearConjugationHom_range_eq_orthD]
    have h3 := relIndex_isometryRange_dvd Q hQ
    have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = Nat.gcd (Nat.card K - 1) 2 := by
      rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
    rw [hsq] at h3
    exact Nat.le_of_dvd (by norm_num) (h3.trans (Nat.gcd_dvd_right _ _))

end Orthogonal

section Main

open CFSG.LieType.Universal.Spin CFSG.RankThree.Automorphisms
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.RankThree.PartOne.KLC (swap_data_coordinate inner_smul_pointFamily_coordinate)
open scoped Pointwise

theorem d4PGood : D4PGood := by
  intro X _ _ p ℓ f hp hp5 h
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) 4 ℓ f h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hab' := card_abelianization_le_four_of_bound (plusIndexEquiv 4) (quadPlus 4 K) hab
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h K hK e).1
  have hsub := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  obtain ⟨κ, hκF, hκy, hκz, hyz⟩ := swap_data_coordinate K
  refine PGoodOut.of_mulEquiv (coordinatePlusWitnessEquiv K e)
    ⟨Inn _, inferInstance, le_rfl, fun δ hδ _ _ => hδ, ?_⟩
  rintro α γ ⟨k, hk⟩
  refine commutator_mem_of_three_point_orbit_gen (Inn _)
    (F := projectivePointFamily (coordinateQuadPlus 4 K)) (y := plusCX 4 K)
    (z := plusCXstar 4 K (by omega)) ?_ hκF hκy hκz hyz ?_ ?_ hp hp5 hk γ
  · intro a
    have := hsub (MulAction.mem_orbit _ a)
    simpa using this
  · rintro _ ⟨g, rfl⟩
    exact inner_smul_pointFamily_coordinate K g
  · rintro a b ha hb ⟨m, hm⟩
    refine commutator_mem_inner_of_pElement _ hQ hab' hp hp5 ?_ ?_ hm
    · rw [← hEA]
      exact (mem_projectivePointFamilyAut_iff _ _).2 ha
    · rw [← hEA]
      exact (mem_projectivePointFamilyAut_iff _ _).2 hb

end Main

end CFSG.AGLEmbedding.TwoGenInner
