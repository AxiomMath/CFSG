module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaThreeFamily
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaFieldWitness
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenSplitEight
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedDerivedReindexEquiv statedDerivedReindexEquiv_vector)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  (plusDerivedEquiv plusDerivedEquiv_val)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace ThreeFamily

theorem exists_centralizing_witness (K : Type) [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hαE : α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hα : orderOf α = 2) :
    ∃ g : matrixDerived (coordinateQuadPlus 4 K),
      MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) ∈
          Subgroup.centralizer {α} ∧
        Nat.card {M : Submodule K (Fin (2 * 4) → K) //
            M ∈ singularSubspaces (coordinateQuadPlus 4 K) 4 ∧
              M.map (matrixLinearEquiv g.val : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)) =
                M} ≠
          2 * Nat.card {L : Submodule K (Fin (2 * 4) → K) //
            L ∈ singularSubspaces (coordinateQuadPlus 4 K) 1 ∧
              L.map (matrixLinearEquiv g.val : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)) =
                L} := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hreg := regular_coordinateQuadPlus 4 K (by norm_num)
  have hE := commutator_coordinateQuadPlus 4 K (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, -, hinv⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by norm_num) _ hreg.1 hreg.2 hE
  have hαE' : α ∈ (unitKappa (coordinateQuadPlus 4 K)).range := by
    rw [range_unitKappa]
    exact hαE
  obtain ⟨x, hx⟩ := hαE'
  obtain ⟨-, hTT, hσ⟩ := hinv α hαE hα x.1 x.2 hx
  set T := coordinateSemilinearMap x.1.val with hTdef
  have hTs : ∀ (a : K) v, T (a • v) = x.1.val.right a • T v := fun a v =>
    coordinateSemilinearMap_smul x.1.val a v
  have hTQ : ∀ v, coordinateQuadPlus 4 K (T v) = x.1.val.right (coordinateQuadPlus 4 K v) :=
    (mem_unitMultiplierPairs_iff _ x.1).mp x.2
  set r := reindexVectorEquiv (K := K) (plusIndexEquiv 4) with hrdef
  have hr : ∀ y, coordinateQuadPlus 4 K (r y) = quadPlus 4 K y :=
    reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 K)
  have hr' : ∀ y, quadPlus 4 K (r.symm y) = coordinateQuadPlus 4 K y := fun y => by
    rw [← hr, LinearEquiv.apply_symm_apply]
  obtain ⟨g', hg'E, hg'T, hg'm⟩ : ∃ g' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K),
      g' ∈ orthElementaryGroup (quadPlus 4 K) ∧
      (∀ y, r (g' (r.symm (T y))) = T (r (g' (r.symm y)))) ∧
      Nat.card {M : Submodule K (Fin 4 ⊕ Fin 4 → K) //
          M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
            M.map (g' : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} ≠
        2 * Nat.card {L : Submodule K (Fin 4 ⊕ Fin 4 → K) //
          L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
            L.map (g' : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} := by
    rcases hσ with hσ1 | ⟨hσ2, -, -⟩
    ·
      have hTlin : ∀ v, T v = matrixLinearEquiv x.1.val.left v := fun v => by
        rw [hTdef, coordinateSemilinearMap_apply, hσ1]
        rfl
      set T' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
        (r.trans (matrixLinearEquiv x.1.val.left)).trans r.symm with hT'def
      have hT'apply : ∀ y, T' y = r.symm (T (r y)) := fun y => by
        rw [hTlin]
        rfl
      have hT'O : T' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := by
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        intro y
        rw [hT'apply, hr', hTQ, hσ1, hr]
        rfl
      have hT'2 : T' * T' = 1 := by
        apply LinearEquiv.ext
        intro y
        rw [LinearEquiv.mul_apply, hT'apply, hT'apply, LinearEquiv.apply_symm_apply, hTT,
          LinearEquiv.symm_apply_apply]
        rfl
      obtain ⟨g', hg'E, -, -, hcomm, hm⟩ :=
        even_split_eight_linear_involution_centralizer_count_witness hT'O hT'2
      refine ⟨g', hg'E, fun y => ?_, hm⟩
      have h := DFunLike.congr_fun hcomm (r.symm y)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hT'apply, hT'apply,
        LinearEquiv.apply_symm_apply] at h
      rw [h, LinearEquiv.apply_symm_apply]
    ·
      have hσσ : x.1.val.right * x.1.val.right = 1 := by
        have h2 := pow_orderOf_eq_one x.1.val.right
        rw [hσ2] at h2
        rw [← pow_two]
        exact h2
      have hσ1 : x.1.val.right ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hσ2
        exact absurd hσ2 (by norm_num)
      obtain ⟨T', hT'⟩ : ∃ T' : (Fin 4 ⊕ Fin 4 → K) →ₛₗ[(x.1.val.right : K →+* K)]
          (Fin 4 ⊕ Fin 4 → K), ∀ y, T' y = r.symm (T (r y)) :=
        ⟨{ toFun := fun y => r.symm (T (r y))
           map_add' := fun y z => by simp only [map_add]
           map_smul' := fun a y => by
             rw [LinearEquiv.map_smul, hTs, LinearEquiv.map_smul]
             rfl }, fun _ => rfl⟩
      have hT'T' : ∀ y, T' (T' y) = y := fun y => by
        rw [hT', hT', LinearEquiv.apply_symm_apply, hTT, LinearEquiv.symm_apply_apply]
      have hT'Q : ∀ y, quadPlus 4 K (T' y) = x.1.val.right (quadPlus 4 K y) := fun y => by
        rw [hT', hr', hTQ, hr]
      obtain ⟨g', hg'E, -, -, hcomm, hL, hM, -⟩ :=
        even_split_eight_field_involution_centralizer_count_witness hσσ hσ1 hT'T' hT'Q
      refine ⟨g', hg'E, fun y => ?_, ?_⟩
      · have h := hcomm (r.symm y)
        rw [hT', hT', LinearEquiv.apply_symm_apply] at h
        rw [h, LinearEquiv.apply_symm_apply]
      · rw [hL, hM]
        have hq : 0 < Nat.card K ^ 4 := pow_pos Nat.card_pos 4
        omega
  obtain ⟨A, hA⟩ := (plusDerivedEquiv 4 K (by norm_num)).surjective ⟨g', hg'E⟩
  have hAval : toLinEquiv _ K A.val = g' := by
    have h := plusDerivedEquiv_val 4 K (by norm_num) A
    rw [hA] at h
    exact h.symm
  obtain ⟨gD, hgD⟩ : ∃ gD : matrixDerived (coordinateQuadPlus 4 K),
      gD = statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A :=
    ⟨_, rfl⟩
  have hvec : ∀ y, matrixLinearEquiv gD.val (r y) = r (g' y) := fun y => by
    have h := statedDerivedReindexEquiv_vector (plusIndexEquiv 4) (quadPlus 4 K)
      (coe_quadPlus 4 K) A y
    rw [hAval] at h
    rw [hgD]
    exact h
  have hgv : ∀ v, matrixLinearEquiv gD.val v = r (g' (r.symm v)) := fun v => by
    rw [← hvec, LinearEquiv.apply_symm_apply]
  refine ⟨gD, ?_, ?_⟩
  ·
    have hTg : ∀ v, T (matrixLinearEquiv gD.val v) = matrixLinearEquiv gD.val (T v) := fun v => by
      rw [hgv, hgv, hg'T]
    have hconjD : matrixDerivedConjugation (coordinateQuadPlus 4 K) x.1 gD = gD := by
      apply Subtype.ext
      apply matrixLinearIso.injective
      apply LinearEquiv.ext
      intro v
      change matrixLinearEquiv (matrixDerivedConjugation _ x.1 gD).val v =
        matrixLinearEquiv gD.val v
      have happ : matrixLinearEquiv
          (matrixDerivedConjugation (coordinateQuadPlus 4 K) x.1 gD).val v =
            T (matrixLinearEquiv gD.val (T.symm v)) := matrixConjugation_vector x.1.val gD.val v
      rw [happ, hTg, AddEquiv.apply_symm_apply]
    have h1 := matrixDerivedInclusion_conjugation (coordinateQuadPlus 4 K) x.1 gD
    rw [hconjD] at h1
    have h2 := congrArg (matrixProjectiveConjugationHom (coordinateQuadPlus 4 K)) h1
    rw [map_mul, map_mul, map_inv, matrixProjectiveConjugationHom_derived] at h2
    have hx' : matrixProjectiveConjugationHom (coordinateQuadPlus 4 K) x.1 = α := hx
    rw [hx'] at h2
    rw [Subgroup.mem_centralizer_iff]
    intro β hβ
    rw [Set.mem_singleton_iff] at hβ
    subst hβ
    exact (eq_mul_inv_iff_mul_eq.mp h2).symm
  · rw [card_invariant_singular_congr r hr hvec 4, card_invariant_singular_congr r hr hvec 1]
    exact hg'm

end ThreeFamily

open ThreeFamily in
theorem d4_triality_full_involution_centralizer_obstruction (G : Type) [Group G] (f : ℕ)
    (h : StatedClassicalModel G .POmegaPlus 4 2 f) :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
      ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)),
        matrixProjectiveImage (coordinateQuadPlus 4 K) =
            projectivePointFamilyAut (coordinateQuadPlus 4 K) ∧
        (∀ α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K), orderOf α = 2 →
          ∀ η : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)), orderOf η = 3 →
            (∀ β ∈ inner (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ⊓
              Subgroup.centralizer {α}, η * β * η⁻¹ = β) →
            η ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) ∧
              η ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K)) ∧
        ∀ α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K), orderOf α = 2 →
          ∀ η ∈ Subgroup.centralizer {α}, orderOf η = 3 →
            (∀ β ∈ inner (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ⊓
              Subgroup.centralizer {α}, η * β * η⁻¹ = β) →
            η ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) ∧
              η ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) := by
  intro K _ _ hK e
  obtain ⟨-, hf, -⟩ := h.1
  obtain ⟨himage, hobs⟩ := d4_three_family_fixed_count_obstruction G f h K hK e
  have hmain : ∀ α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K), orderOf α = 2 →
      ∀ η : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)), orderOf η = 3 →
        (∀ β ∈ inner (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ⊓
          Subgroup.centralizer {α}, η * β * η⁻¹ = β) →
        η ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) ∧
          η ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) := by
    intro α hαE hα η hη hcomm
    obtain ⟨g, hgC, hm⟩ := exists_centralizing_witness K hf hK hαE hα
    have hc := hcomm _ (Subgroup.mem_inf.mpr ⟨⟨matrixProjectiveProjection _ g, rfl⟩, hgC⟩)
    obtain ⟨h1, h2⟩ := hobs g η hη hc hm
    exact ⟨h2, h1⟩
  exact ⟨himage.symm, hmain, fun α hαE hα η _ hη hcomm => hmain α hαE hα η hη hcomm⟩

end CFSG.ComponentClassification.UnbalancedCatalog
