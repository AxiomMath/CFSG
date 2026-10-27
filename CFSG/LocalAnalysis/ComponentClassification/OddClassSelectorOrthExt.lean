module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal
public import CFSG.LocalAnalysis.ComponentInitial.OddOrthogonalFourGroupCommutant

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
theorem isComponent_operatorCentralizer {A : V ≃ₗ[K] V} {Y : Subgroup (V ≃ₗ[K] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer A.toLinearMap)) :
    ∃ _ : Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype ≤
        orthogonalOperatorCentralizer Q A.toLinearMap,
      CFSG.IsComponent ((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
        (orthogonalOperatorCentralizer Q A.toLinearMap)) ∧
      Nonempty (((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
        (orthogonalOperatorCentralizer Q A.toLinearMap)) ≃* Y) := by
  have hYO : Y ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hY.1.trans inf_le_left
  have h := isComponentOf_comap_of_le_range (TauCeti.QuadraticMap.orthogonalGroup Q).subtype
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective hY
    (by rw [Subgroup.range_subtype]; exact inf_le_left)
  have hC : (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer A.toLinearMap).comap
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype =
        orthogonalOperatorCentralizer Q A.toLinearMap := by
    rw [Subgroup.comap_inf]
    have hOO : (TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype = ⊤ :=
      Subgroup.subgroupOf_self (TauCeti.QuadraticMap.orthogonalGroup Q)
    rw [hOO, top_inf_eq]
    rfl
  rw [hC] at h
  exact ⟨h.1, (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.1).mp h,
    ⟨(Subgroup.subgroupOfEquivOfLe h.1).trans (Subgroup.subgroupOfEquivOfLe hYO)⟩⟩

theorem orth_ext_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 10 ≤ finrank K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V))
    (hnsq : ¬ IsSquare (d : K)) (hμ : (μ : K) / (d : K) = 1)
    {Y : Subgroup (V ≃ₗ[K] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer A.toLinearMap))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X) : False := by
  classical
  obtain ⟨-, -, -, hns4⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hK (by omega) Q hQ A d μ hsquare hsim hnonscalar
  have h4 := hns4 hnsq
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  let : Field (scalarAlgebra A.toLinearMap) := scalarField A.toLinearMap d hnsq
    (CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square A d hsquare)
  let : Module (scalarAlgebra A.toLinearMap) V := evaluationModule A.toLinearMap
  obtain ⟨⟨-, hfin, -, -, -, -, -, -, hcard, -, -, -, -, -, -, -, -, -, -, hfinE, hfinrank, -⟩,
    hpos, -⟩ := h4
  obtain ⟨-, -, -, hQEnd, -, -, eO, -, -, -, -⟩ := hpos hμ
  have := hfin
  have : FiniteDimensional (scalarAlgebra A.toLinearMap) V := hfinE
  have hoddE : Odd (Nat.card (scalarAlgebra A.toLinearMap)) := by
    rw [hcard]
    exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
  have hcardE : Nat.card (scalarAlgebra A.toLinearMap) = ℓ ^ (2 * e) := by
    rw [hcard, ← pow_mul, mul_comm]
  have h5 : 5 ≤ finrank (scalarAlgebra A.toLinearMap) V := by omega
  obtain ⟨-, hY₁, ⟨eY⟩⟩ := isComponent_operatorCentralizer hY
  have hL' := LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent eO hY₁
  have hq := OddSelector.commutator_orthogonalGroup_quasisimple hoddE _ hQEnd h5
  have hrange := LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hL' hq
  obtain ⟨τ, hτ⟩ := OddSelector.exists_sp_four_hom hoddE _ hQEnd h5
  have : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSp 2 (scalarAlgebra A.toLinearMap)) :=
    OddSelector.isPerfect_statedSp le_rfl hoddE
  have hτr : ∀ x, τ x ∈ ((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
      (orthogonalOperatorCentralizer Q A.toLinearMap)).map eO.toMonoidHom := fun x => by
    rw [hrange]
    exact OddSelector.map_mem_commutator_of_isPerfect τ x
  set φ := (((Y.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).subgroupOf
    (orthogonalOperatorCentralizer Q A.toLinearMap)).equivMapOfInjective eO.toMonoidHom
      eO.injective).symm.trans eY with hφ
  exact false_of_smallSource hs
    (OddSelector.not_small_source_of_sp_cover le_rfl hℓ hℓ2 (by omega) hcardE _
      (ker_comp_codRestrict_le_center τ hτ hτr φ σ hσk))

end CFSG.ComponentClassification.OddClassSelector
