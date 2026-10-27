module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSquareZero
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

section Model

variable {n : ℕ} {K : Type} [Field K]

variable (n K) in
@[expose] noncomputable def statedProjEquiv : StatedProj (StatedSL n K) ≃* projectiveSL n K :=
  (projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center n K).symm)

theorem statedProjEquiv_mk (g : SpecialLinearGroup (Fin n) K) :
    statedProjEquiv n K (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K g)) =
      proj n K g := by
  rw [statedProjEquiv, MulEquiv.trans_apply]
  have h : (projectiveSpecialLinearGroupEquivStatedProj n K).symm
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL n K g)) = QuotientGroup.mk g := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h]
  rfl

variable {G : Type} [Group G] {A : Subgroup G}

@[expose] noncomputable def modelHom (e : rankTwoQuot A ≃* StatedProj (StatedSL n K)) :
    ↥A →* projectiveSL n K :=
  (statedProjEquiv n K).toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center ↥A)))

variable {e : rankTwoQuot A ≃* StatedProj (StatedSL n K)}

theorem modelHom_surjective : Function.Surjective (modelHom e) :=
  (statedProjEquiv n K).surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))

theorem ker_modelHom : (modelHom e).ker = center ↥A := by
  ext x
  rw [MonoidHom.mem_ker, modelHom, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem represents_iff_modelHom {x : G} {g : SpecialLinearGroup (Fin n) K} :
    Represents e x (SpecialLinearGroup.toGL g) ↔ ∃ hx : x ∈ A, modelHom e ⟨x, hx⟩ = proj n K g := by
  have hmem : SpecialLinearGroup.toGL g ∈ StatedSL n K := (specialLinearGroupEquivStatedSL n K g).2
  have hφ : (⟨SpecialLinearGroup.toGL g, hmem⟩ : ↥(StatedSL n K)) =
      specialLinearGroupEquivStatedSL n K g := rfl
  constructor
  · rintro ⟨hx, hM, he⟩
    refine ⟨hx, ?_⟩
    change statedProjEquiv n K (e (QuotientGroup.mk ⟨x, hx⟩)) = proj n K g
    rw [he, hφ, statedProjEquiv_mk]
  · rintro ⟨hx, h⟩
    refine ⟨hx, hmem, ?_⟩
    apply (statedProjEquiv n K).injective
    rw [hφ, statedProjEquiv_mk]
    exact h

theorem exists_toGL_eq {M : GL (Fin n) K} (hM : M ∈ StatedSL n K) :
    ∃ g : SpecialLinearGroup (Fin n) K, SpecialLinearGroup.toGL g = M :=
  ⟨(specialLinearGroupEquivStatedSL n K).symm ⟨M, hM⟩,
    congrArg Subtype.val ((specialLinearGroupEquivStatedSL n K).apply_symm_apply ⟨M, hM⟩)⟩

variable (e) in
@[expose] noncomputable def conjModelHom (P : GL (Fin n) K) : ↥A →* projectiveSL n K :=
  (conjAut n K P).toMonoidHom.comp (modelHom e)

theorem conjModelHom_surjective (P : GL (Fin n) K) : Function.Surjective (conjModelHom e P) :=
  (conjAut n K P).surjective.comp modelHom_surjective

theorem ker_conjModelHom (P : GL (Fin n) K) : (conjModelHom e P).ker = center ↥A := by
  rw [← ker_modelHom (e := e)]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, conjModelHom, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

theorem conjModelHom_of_represents (P : GL (Fin n) K) {x : G} {M : GL (Fin n) K}
    (hx : Represents e x M) : ∃ hxA : x ∈ A, ∃ g : SpecialLinearGroup (Fin n) K,
      conjModelHom e P ⟨x, hxA⟩ = proj n K g ∧
      (g : Matrix (Fin n) (Fin n) K) = (P : Matrix (Fin n) (Fin n) K) * M *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨g₀, rfl⟩ := exists_toGL_eq hx.2.1
  obtain ⟨hxA, h⟩ := represents_iff_modelHom.mp hx
  refine ⟨hxA, CatalogueBHigherLinearAction.slConjugation n K P g₀, ?_, ?_⟩
  · change conjAut n K P (modelHom e ⟨x, hxA⟩) = _
    rw [h, conjAut_proj]
  · rw [CatalogueBHigherLinearAction.slConjugation_matrix]
    rfl

end Model

section Conj

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

open Module

theorem exists_conj_of_sq_eq_zero {N N' : Matrix ι ι K} (hN : N * N = 0) (hN' : N' * N' = 0)
    (hr : N.rank = N'.rank) :
    ∃ P : GL ι K, (P : Matrix ι ι K) * N * ((P⁻¹ : GL ι K) : Matrix ι ι K) = N' := by
  classical
  set f := Matrix.toLin' N with hf
  set f' := Matrix.toLin' N' with hf'
  have hf2 : f ∘ₗ f = 0 := by rw [hf, ← Matrix.toLin'_mul, hN, map_zero]
  have hf'2 : f' ∘ₗ f' = 0 := by rw [hf', ← Matrix.toLin'_mul, hN', map_zero]
  have hrank : finrank K (LinearMap.range f) = finrank K (LinearMap.range f') := by
    rw [hf, hf', Matrix.toLin'_apply', Matrix.toLin'_apply']
    exact hr
  obtain ⟨r, b, hb1, hb2⟩ := exists_basis_sq_eq_zero f hf2
  obtain ⟨r', b', hb1', hb2'⟩ := exists_basis_sq_eq_zero f' hf'2
  generalize hℓ : finrank K (LinearMap.range f) = ℓ at b hb1 hb2 hrank
  generalize hℓ' : finrank K (LinearMap.range f') = ℓ' at b' hb1' hb2' hrank
  subst hrank
  have hc := Module.finrank_eq_card_basis b
  have hc' := Module.finrank_eq_card_basis b'
  rw [hc'] at hc
  simp only [Fintype.card_sum, Fintype.card_fin] at hc
  have hrr : r = r' := by omega
  subst hrr
  set φ : (ι → K) ≃ₗ[K] (ι → K) := b.equiv b' (Equiv.refl _) with hφ
  have hφb : ∀ x, φ (b x) = b' x := fun x => by rw [hφ, Basis.equiv_apply]; rfl
  have hcomm : φ.toLinearMap ∘ₗ f = f' ∘ₗ φ.toLinearMap := by
    refine b.ext fun x => ?_
    rcases x with i | x
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hb1, hφb, hb1']
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hb2, map_zero, hφb, hb2']
  have hφφ : φ.toLinearMap ∘ₗ φ.symm.toLinearMap = LinearMap.id := by
    ext v
    simp
  have hφφ' : φ.symm.toLinearMap ∘ₗ φ.toLinearMap = LinearMap.id := by
    ext v
    simp
  let P : GL ι K := ⟨LinearMap.toMatrix' φ.toLinearMap, LinearMap.toMatrix' φ.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp, hφφ, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, hφφ', LinearMap.toMatrix'_id]⟩
  refine ⟨P, ?_⟩
  have hPinv : ((P⁻¹ : GL ι K) : Matrix ι ι K) = LinearMap.toMatrix' φ.symm.toLinearMap := rfl
  have hPv : (P : Matrix ι ι K) = LinearMap.toMatrix' φ.toLinearMap := rfl
  rw [hPinv, hPv]
  have hN0 : N = LinearMap.toMatrix' f := by rw [hf, LinearMap.toMatrix'_toLin']
  have hN0' : N' = LinearMap.toMatrix' f' := by rw [hf', LinearMap.toMatrix'_toLin']
  rw [hN0, hN0', ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, hcomm,
    LinearMap.comp_assoc, hφφ, LinearMap.comp_id]

end Conj

end CFSG.ComponentClassification.RankTwoClassical
