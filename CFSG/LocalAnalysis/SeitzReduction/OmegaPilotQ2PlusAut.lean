module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusModel
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSimilarity

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)

theorem coeff_ne_zero_of_irreducible' {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  rintro rfl
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (-c)
  exact hirr s (by rw [zero_mul, add_zero, _root_.sq, ← hs, neg_add_cancel])

section Transport

variable {K : Type} [Field K] {d : ℕ}

theorem matrixConjugation_inl_apply (S A : GL (Fin d) K) :
    matrixConjugation (SemidirectProduct.inl S) A = S * A * S⁻¹ := by
  rw [matrixConjugation_apply]
  have h1 : (SemidirectProduct.inl S : coordinateSemilinearGroup d K).right = 1 := rfl
  rw [h1, map_one]
  try rfl

theorem matrixProjectiveImage_eq_top_of_similarity {Q Q' : QuadraticForm K (Fin d → K)}
    (S : GL (Fin d) K) (ν : Kˣ) (hS : ∀ v, Q' (matrixLinearIso S v) = ν * Q v)
    (htop : matrixProjectiveImage Q' = ⊤) : matrixProjectiveImage Q = ⊤ := by
  set Θ := CFSG.RankThree.PartOne.KCOrthogonalDescent.matrixProjectiveSimilarityEquiv Q Q' S ν hS
    with hΘ
  rw [eq_top_iff]
  intro β _
  have hmem : MulAut.congr Θ β ∈ matrixProjectiveImage Q' := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ _).1 hmem
  obtain ⟨μ, hμ⟩ := g.property
  set g₀ : coordinateSemilinearGroup d K :=
    SemidirectProduct.inl S⁻¹ * g.val * SemidirectProduct.inl S with hg₀
  have hmapS : ∀ v, coordinateSemilinearMap (SemidirectProduct.inl S) v = matrixLinearIso S v :=
    fun v => coordinateSemilinearMap_inl S v
  have hQinv : ∀ w, Q (matrixLinearIso S⁻¹ w) = (ν⁻¹ : Kˣ) * Q' w := by
    intro w
    have h1 := hS (matrixLinearIso S⁻¹ w)
    have h2 : matrixLinearIso S (matrixLinearIso S⁻¹ w) = w := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [h2] at h1
    rw [h1, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hg₀v : ∀ v, coordinateSemilinearMap g₀ v =
      matrixLinearIso S⁻¹ (coordinateSemilinearMap g.val (matrixLinearIso S v)) := by
    intro v
    rw [hg₀, coordinateSemilinearMap_mul, coordinateSemilinearMap_mul, coordinateSemilinearMap_inl,
      coordinateSemilinearMap_inl]
    rfl
  have hright : g₀.right = g.val.right := by
    rw [hg₀]
    change 1 * g.val.right * 1 = g.val.right
    rw [one_mul, mul_one]
  have hg₀mem : g₀ ∈ similarityPairs Q := by
    refine ⟨ν⁻¹ * μ * Units.map g.val.right.toMonoidHom ν, fun v => ?_⟩
    rw [hg₀v, hQinv, hμ, hS, hright, map_mul]
    have e : ((Units.map g.val.right.toMonoidHom ν : Kˣ) : K) = g.val.right (ν : K) := rfl
    rw [Units.val_mul, Units.val_mul, e]
    ring
  refine ⟨⟨g₀, hg₀mem⟩, MulEquiv.ext fun x => ?_⟩
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change matrixProjectiveConjugation Q ⟨g₀, hg₀mem⟩ (matrixProjectiveProjection Q A) =
    β (matrixProjectiveProjection Q A)
  apply Θ.injective
  obtain ⟨B, hB⟩ := CFSG.RankThree.PartOne.KCOrthogonalDescent.exists_conj_mem_matrixDerived Q Q'
    S ν hS A
  have hΘA : Θ (matrixProjectiveProjection Q A) = matrixProjectiveProjection Q' B :=
    CFSG.RankThree.PartOne.KCOrthogonalDescent.matrixProjectiveSimilarityEquiv_mk Q Q' S ν hS A B
      hB
  have hβ : Θ (β (matrixProjectiveProjection Q A)) =
      matrixProjectiveConjugation Q' g (matrixProjectiveProjection Q' B) := by
    rw [hg, ← hΘA, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hβ, matrixProjectiveConjugation_mk, matrixProjectiveConjugation_mk, hΘ]
  apply CFSG.RankThree.PartOne.KCOrthogonalDescent.matrixProjectiveSimilarityEquiv_mk
  change matrixConjugation g.val B.val = S * matrixConjugation g₀ A.val * S⁻¹
  rw [hB]
  have hc : matrixConjugation g₀ A.val = S⁻¹ * matrixConjugation g.val (S * A.val * S⁻¹) * S := by
    rw [hg₀]
    change matrixConjugationHom (SemidirectProduct.inl S⁻¹ * g.val * SemidirectProduct.inl S) A.val =
      _
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
    change matrixConjugation (SemidirectProduct.inl S⁻¹)
      (matrixConjugation g.val (matrixConjugation (SemidirectProduct.inl S) A.val)) = _
    rw [matrixConjugation_inl_apply, matrixConjugation_inl_apply, inv_inv]
  rw [hc]
  group

end Transport

section Plus

variable {K : Type} [Field K] [Finite K] {m : ℕ}

theorem matrixProjectiveImage_plusAnisoQuad_eq_top {b c : K} (hb : b ≠ 0) (hm : 3 ≤ m) :
    matrixProjectiveImage (plusAnisoQuad K m b c) = ⊤ :=
  matrixProjectiveImage_eq_top_of_similarity (plusAnisoMatrix b c hb) 1
    (coordinateQuadPlus_plusAnisoMatrix b c hb)
    (CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K (m + 2)
      (by omega))

end Plus

section Neighbour

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

@[expose] noncomputable def plusAnisoTorus (m : ℕ) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup (matrixProjectiveDerived (plusAnisoQuad K m b c)) :=
  anisoTorusOf (plusAnisoQuad K m b c) (isAnisoCoord_plusAnisoQuad (m := m) hirr).ne b c

@[expose] noncomputable def plusAnisoPerp (m : ℕ) (b c : K) :
    Subgroup (matrixProjectiveDerived (plusAnisoQuad K m b c)) :=
  pairPerpOf (plusAnisoQuad K m b c) (plusAnisoLeft m) (plusAnisoRight m)

theorem centralizer_plusAnisoTorus (hm : 1 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    centralizer (plusAnisoTorus m hirr : Set (matrixProjectiveDerived (plusAnisoQuad K m b c))) =
      plusAnisoTorus m hirr ⊔ plusAnisoPerp m b c := by
  have hreg := regular_plusAnisoQuad (K := K) (b := b) (c := c)
    (CFSG.SeitzReduction.OmegaPilot.coeff_ne_zero_of_irreducible' hirr) hm
  exact (isAnisoCoord_plusAnisoQuad hirr).centralizer_anisoTorusOf hreg.1 hreg.2

theorem plusAnisoTorus_facts {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Odd (Nat.card (plusAnisoTorus m hirr)) ∧
      plusAnisoTorus m hirr ≤ centralizer (plusAnisoTorus m hirr :
        Set (matrixProjectiveDerived (plusAnisoQuad K m b c))) ∧
      plusAnisoTorus m hirr ≤ centralizer (plusAnisoPerp m b c :
        Set (matrixProjectiveDerived (plusAnisoQuad K m b c))) := by
  have h := isAnisoCoord_plusAnisoQuad (m := m) hirr
  exact ⟨h.odd_card_anisoTorusOf,
    h.anisoTorusOf_le_centralizer_self, h.anisoTorusOf_le_centralizer_pairPerpOf⟩

theorem exists_mem_plusAnisoTorus_eq_conj (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {β : MulAut (matrixProjectiveDerived (plusAnisoQuad K m b c))}
    (hX : ∀ x ∈ plusAnisoTorus m hirr, β x = x) (hD : ∀ x ∈ plusAnisoPerp m b c, β x = x) :
    ∃ x ∈ plusAnisoTorus m hirr, β = MulAut.conj x := by
  have hb := CFSG.SeitzReduction.OmegaPilot.coeff_ne_zero_of_irreducible' hirr
  have hreg := regular_plusAnisoQuad (K := K) (m := m) (b := b) (c := c) hb (by omega)
  set j₂ : Fin m := ⟨0, by omega⟩
  set j₃ : Fin m := ⟨1, by omega⟩
  have h23 : j₂ ≠ j₃ := by simp [j₂, j₃, Fin.ext_iff]
  refine (isAnisoCoord_plusAnisoQuad hirr).exists_mem_anisoTorusOf_eq_conj hreg.1 hreg.2
    (isHypCoord_plusAnisoQuad b c j₂) (isHypCoord_plusAnisoQuad b c j₃)
    (pairDisjoint_plusAniso j₂) (pairDisjoint_plusAniso j₃) (pairDisjoint_plusAniso_hyp h23) ?_
    hX hD
  rw [matrixProjectiveImage_plusAnisoQuad_eq_top hb hm]
  exact Subgroup.mem_top β

end Neighbour

end CFSG.SeitzReduction.OmegaPilot
