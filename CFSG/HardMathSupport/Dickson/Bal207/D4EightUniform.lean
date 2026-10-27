module

public import CFSG.HardMathSupport.Dickson.Bal207.D4Semilin
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Model
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourHabel
public import CFSG.HardMathSupport.Dickson.Bal207.Restate
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Dickson.I271
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.Adapters.RankTwoModelTransports (glCongr)
open CFSG.SeitzReduction.OmegaPilot (matrixProjectiveCongr matrixProjectiveCongr_mk
  map_matrixDerived_glCongr)
open scoped Pointwise

section FieldChange

variable {F F₀ : Type} [Field F] [Field F₀] (τ : F ≃+* F₀) {d : ℕ}

@[expose] def semilinFieldCongr (g : coordinateSemilinearGroup d F) :
    coordinateSemilinearGroup d F₀ :=
  ⟨glCongr τ g.left, τ.symm.trans (g.right.trans τ)⟩

theorem glCongr_glFieldAut (σ : F ≃+* F) (A : GL (Fin d) F) :
    glCongr τ (glFieldAut (Fin d) F σ A) =
      glFieldAut (Fin d) F₀ (τ.symm.trans (σ.trans τ)) (glCongr τ A) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change τ (σ (A i j)) = τ (σ (τ.symm (τ (A i j))))
  rw [RingEquiv.symm_apply_apply]

theorem coordinateSemilinearMap_semilinFieldCongr (g : coordinateSemilinearGroup d F)
    (w : Fin d → F) :
    coordinateSemilinearMap (semilinFieldCongr τ g) (τ ∘ w) =
      τ ∘ coordinateSemilinearMap g w := by
  rw [coordinateSemilinearMap_apply, coordinateSemilinearMap_apply]
  have h : (fun i => (semilinFieldCongr τ g).right ((τ ∘ w) i)) =
      τ ∘ fun i => g.right (w i) := by
    funext i
    change τ (g.right (τ.symm (τ (w i)))) = τ (g.right (w i))
    rw [RingEquiv.symm_apply_apply]
  rw [h]
  exact CFSG.ClassicalInvolution.Upgrade.glCongr_mulVec τ g.left _

variable {Q : QuadraticForm F (Fin d → F)} {Q₀ : QuadraticForm F₀ (Fin d → F₀)}

theorem semilinFieldCongr_mem (hQ : ∀ v, Q₀ (τ ∘ v) = τ (Q v))
    {g : coordinateSemilinearGroup d F} (hg : g ∈ similarityPairs Q) :
    semilinFieldCongr τ g ∈ similarityPairs Q₀ := by
  obtain ⟨μ, hμ⟩ := hg
  refine ⟨Units.map τ.toMonoidHom μ, fun v => ?_⟩
  obtain ⟨w, rfl⟩ : ∃ w, τ ∘ w = v := ⟨τ.symm ∘ v, funext fun i => τ.apply_symm_apply _⟩
  rw [coordinateSemilinearMap_semilinFieldCongr, hQ (coordinateSemilinearMap g w), hμ w, hQ w,
    map_mul]
  change τ μ * τ (g.right (Q w)) = τ μ * τ (g.right (τ.symm (τ (Q w))))
  rw [RingEquiv.symm_apply_apply]

@[expose] def simPairFieldCongr (hQ : ∀ v, Q₀ (τ ∘ v) = τ (Q v)) (g : similarityPairs Q) :
    similarityPairs Q₀ :=
  ⟨semilinFieldCongr τ g.val, semilinFieldCongr_mem τ hQ g.2⟩

theorem mulAut_congr_matrixProjectiveCongr (hQ : ∀ v, Q₀ (τ ∘ v) = τ (Q v))
    (g : similarityPairs Q) :
    MulAut.congr (matrixProjectiveCongr τ hQ) (matrixProjectiveConjugationHom Q g) =
      matrixProjectiveConjugationHom Q₀ (simPairFieldCongr τ hQ g) := by
  have hmem : ∀ A : matrixDerived Q, glCongr τ A.val ∈ matrixDerived Q₀ := by
    intro A
    rw [← map_matrixDerived_glCongr τ hQ]
    exact Subgroup.mem_map_of_mem (glCongr τ).toMonoidHom A.2
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (matrixProjectiveCongr τ hQ).surjective x
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q y
  have hA : matrixProjectiveCongr τ hQ (matrixProjectiveProjection Q A) =
      matrixProjectiveProjection Q₀ ⟨glCongr τ A.val, hmem A⟩ :=
    matrixProjectiveCongr_mk τ hQ A ⟨glCongr τ A.val, hmem A⟩ rfl
  change matrixProjectiveCongr τ hQ (matrixProjectiveConjugationHom Q g
      ((matrixProjectiveCongr τ hQ).symm (matrixProjectiveCongr τ hQ
        (matrixProjectiveProjection Q A)))) = _
  rw [MulEquiv.symm_apply_apply, hA]
  change matrixProjectiveCongr τ hQ
      (matrixProjectiveConjugation Q g (matrixProjectiveProjection Q A)) =
    matrixProjectiveConjugation Q₀ (simPairFieldCongr τ hQ g)
      (matrixProjectiveProjection Q₀ ⟨glCongr τ A.val, hmem A⟩)
  rw [matrixProjectiveConjugation_mk, matrixProjectiveConjugation_mk]
  apply matrixProjectiveCongr_mk
  change glCongr τ g.val.left * glFieldAut (Fin d) F₀ (τ.symm.trans (g.val.right.trans τ))
      (glCongr τ A.val) * (glCongr τ g.val.left)⁻¹ =
    glCongr τ (g.val.left * glFieldAut (Fin d) F g.val.right A.val * g.val.left⁻¹)
  rw [map_mul, map_mul, map_inv, glCongr_glFieldAut]

theorem mulAut_congr_matrixProjectiveCongr_mem_image (hQ : ∀ v, Q₀ (τ ∘ v) = τ (Q v))
    {α : MulAut (matrixProjectiveDerived Q)} (hα : α ∈ matrixProjectiveImage Q) :
    MulAut.congr (matrixProjectiveCongr τ hQ) α ∈ matrixProjectiveImage Q₀ := by
  obtain ⟨g, rfl⟩ := hα
  exact ⟨simPairFieldCongr τ hQ g, (mulAut_congr_matrixProjectiveCongr τ hQ g).symm⟩

theorem coordinateQuadPlus_fieldCongr (n : ℕ) (v : Fin (2 * n) → F) :
    coordinateQuadPlus n F₀ (τ ∘ v) = τ (coordinateQuadPlus n F v) := by
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply]
  simp only [Function.comp_apply, map_sum, map_mul]

end FieldChange

section Orbit

variable {A T : Type*} [Group A] [MulAction A T]

theorem smul_eq_of_mem_orbit_of_pow_three {x y : T}
    (hO : (MulAction.orbit A x).ncard = 1 ∨ (MulAction.orbit A x).ncard = 3) {β : A}
    (hβ : β ^ 3 = 1) (hy : y ∈ MulAction.orbit A x) (hβy : β • y = y) : β • x = x := by
  by_contra hx
  have h3 : β • (β ^ 2 • x) = x := by rw [smul_smul, ← pow_succ', hβ, one_smul]
  have d2 : β ^ 2 • x ≠ x := fun h => hx (by rw [h] at h3; exact h3)
  have d3 : β • x ≠ β ^ 2 • x := fun h =>
    hx (smul_left_cancel β (by rw [← mul_smul, ← pow_two]; exact h.symm))
  have d4 : y ≠ x := fun h => hx (by rw [← h]; exact hβy)
  have d5 : y ≠ β • x := fun h => hx (smul_left_cancel β (by rw [← h]; exact hβy))
  have d6 : y ≠ β ^ 2 • x := fun h => d2 (by rw [h, h3] at hβy; exact hβy.symm)
  have hsub : ({y, x, β • x, β ^ 2 • x} : Set T) ⊆ MulAction.orbit A x := by
    intro z hz
    rcases hz with rfl | rfl | rfl | hz
    · exact hy
    · exact MulAction.mem_orbit_self _
    · exact MulAction.mem_orbit _ β
    · rw [Set.mem_singleton_iff.1 hz]
      exact MulAction.mem_orbit _ (β ^ 2)
  have hn1 : x ∉ ({β • x, β ^ 2 • x} : Set T) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hx, d2.symm⟩
  have hn2 : y ∉ ({x, β • x, β ^ 2 • x} : Set T) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨d4, d5, d6⟩
  have hcard : ({y, x, β • x, β ^ 2 • x} : Set T).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem hn2, Set.ncard_insert_of_notMem hn1, Set.ncard_pair d3]
  have hfin : (MulAction.orbit A x).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hle := Set.ncard_le_ncard hsub hfin
  omega

end Orbit

theorem SemilinD4EightAut.mulAut_congr_mem_image {S : Type} [Group S] {φ : MulAut S}
    (h : SemilinD4EightAut S φ) (hφ : φ ^ 3 = 1) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 8) (ψ₀ : S ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F₀)) :
    MulAut.congr ψ₀ φ ∈ matrixProjectiveImage (coordinateQuadPlus 4 F₀) := by
  obtain ⟨F, _, _, e, hF, hφe⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have : Fintype F₀ := Fintype.ofFinite F₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F₀ 2 :=
    charP_of_card_eq_prime_pow (f := 3) (by rw [← Nat.card_eq_fintype_card, hF₀]; norm_num)
  let τ : F ≃+* F₀ := FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hF₀])
  let ι := matrixProjectiveCongr τ (coordinateQuadPlus_fieldCongr τ 4)
  let ψ := (coordinatePlusWitnessEquiv F e).trans ι
  have hα : MulAut.congr ψ φ ∈ matrixProjectiveImage (coordinateQuadPlus 4 F₀) := by
    have h1 : MulAut.congr ψ φ = MulAut.congr ι (MulAut.congr (coordinatePlusWitnessEquiv F e) φ) :=
      MulEquiv.ext fun _ => rfl
    rw [h1]
    exact mulAut_congr_matrixProjectiveCongr_mem_image τ _ hφe
  obtain ⟨δ, rfl⟩ : ∃ δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F₀)),
      ψ₀ = ψ.trans δ := ⟨ψ.symm.trans ψ₀, MulEquiv.ext fun x => by simp⟩
  have hconj : MulAut.congr (ψ.trans δ) φ = δ * MulAut.congr ψ φ * δ⁻¹ :=
    MulEquiv.ext fun _ => rfl
  rw [CFSG.SeitzReduction.OmegaPilot.mem_image_iff_smul_pointFamily le_rfl] at hα
  rw [CFSG.SeitzReduction.OmegaPilot.mem_image_iff_smul_pointFamily le_rfl]
  refine smul_eq_of_mem_orbit_of_pow_three
    CFSG.SeitzReduction.OmegaPilot.orbit_pointFamily_ncard_four ?_ (MulAction.mem_orbit _ δ) ?_
  · rw [← map_pow, hφ, map_one]
  · rw [hconj, mul_smul, mul_smul, inv_smul_smul, hα]

theorem exists_d4Eight_model {Y : Type} [Group Y] (hY : IsLieQuot Y IsD4EightIdx) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 8 ∧
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F))) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hY
  cases d with
  | D r q =>
    obtain ⟨rfl, hp, he⟩ := hd
    obtain ⟨-, F, _, _, hcard, ⟨e'⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hp e
    exact ⟨F, inferInstance, inferInstance, by rw [hcard, hp, he]; norm_num, ⟨e'⟩⟩
  | _ => exact False.elim hd

theorem mulAut_congr_mem_image_of_noTrialityOn {X : Type} [Group X] {B K : Subgroup X}
    (hN : NoTrialityOn NonSemilinD4Eight B K) (hB : ∀ b ∈ B, b ^ 3 = 1) {F₀ : Type} [Field F₀]
    [Finite F₀] (hF₀ : Nat.card F₀ = 8)
    (ψ₀ : (↥K ⧸ Subgroup.center ↥K) ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F₀))
    {φ : MulAut (↥K ⧸ Subgroup.center ↥K)} (hφ : φ ∈ autImage B K) :
    MulAut.congr ψ₀ φ ∈ matrixProjectiveImage (coordinateQuadPlus 4 F₀) := by
  have h3 : φ ^ 3 = 1 := by
    obtain ⟨b, hbN, hbB, rfl⟩ := mem_autImage.1 hφ
    have hb3 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hB b hbB)
    rw [← map_pow, hb3, map_one]
  have hS : SemilinD4EightAut _ φ := by
    by_contra hns
    exact hN φ hφ ⟨h3, hns⟩
  exact hS.mulAut_congr_mem_image h3 hF₀ ψ₀

end CFSG.HardMathSupport.Dickson.Bal207

end
