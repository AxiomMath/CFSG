module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusAut

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (reindexVectorEquiv plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)

section Conj

variable {K : Type*} [Field K]

theorem eichler_conj_of_isometry {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (Φ : V ≃ₗ[K] V')
    (hΦ : ∀ x, Q' (Φ x) = Q x) (u w : V) (x : V') :
    Φ (eichler Q u w (Φ.symm x)) = eichler Q' (Φ u) (Φ w) x := by
  have hpol : ∀ y z, polar Q' (Φ y) (Φ z) = polar Q y z := fun y z => by
    simp only [polar, ← map_add, hΦ]
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hu' : Q' (Φ u) = 0 := by rw [hΦ, h.1]
    have hw' : polar Q' (Φ u) (Φ w) = 0 := by rw [hpol, h.2]
    have h1 : polar Q (Φ.symm x) u = polar Q' x (Φ u) := by
      rw [← hpol, LinearEquiv.apply_symm_apply]
    have h2 : polar Q (Φ.symm x) w = polar Q' x (Φ w) := by
      rw [← hpol, LinearEquiv.apply_symm_apply]
    rw [eichler_apply h.1 h.2, eichler_apply hu' hw', map_sub, map_add, map_smul, map_smul,
      LinearEquiv.apply_symm_apply, h1, h2, hΦ]
  · have h' : ¬(Q' (Φ u) = 0 ∧ polar Q' (Φ u) (Φ w) = 0) := by rwa [hΦ, hpol]
    rw [eichler_of_not h, eichler_of_not h']
    simp

end Conj

section Fix

variable {K : Type} [Field K] {m : ℕ}

theorem pi_single_comp_plusIndexEquiv (s : Fin (m + 2) ⊕ Fin (m + 2)) :
    (fun t => (Pi.single (plusIndexEquiv (m + 2) s) (1 : K) : Fin (2 * (m + 2)) → K)
      (plusIndexEquiv (m + 2) t)) = Pi.single s 1 := by
  funext t
  simp only [Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]

theorem plusAnisoFun_single_succ_succ (b c : K) (j : Fin m) (s : Fin (m + 2) ⊕ Fin (m + 2))
    (hs : s = .inl j.succ.succ ∨ s = .inr j.succ.succ) :
    plusAnisoFun b c (Pi.single s 1) = Pi.single s 1 := by
  have h0 : ∀ i : Fin m, (i.succ.succ : Fin (m + 2)) ≠ 0 := fun i => fin_succ_succ_ne_zero i
  have h1 : ∀ i : Fin m, (i.succ.succ : Fin (m + 2)) ≠ 1 := fun i => fin_succ_succ_ne_one i
  funext t
  rcases hs with rfl | rfl <;> rcases t with i | i <;> rcases fin_cases_two i with rfl | rfl | ⟨k, rfl⟩
  all_goals simp [Pi.single_apply, (h0 j).symm, (h1 j).symm, Fin.succ_inj]

theorem plusAnisoIsometry_single {b c : K} (hb : b ≠ 0) (j : Fin m)
    (s : Fin (m + 2) ⊕ Fin (m + 2)) (hs : s = .inl j.succ.succ ∨ s = .inr j.succ.succ) :
    plusAnisoIsometry b c hb (Pi.single (plusIndexEquiv (m + 2) s) 1) =
      Pi.single (plusIndexEquiv (m + 2) s) 1 := by
  change reindexVectorEquiv (plusIndexEquiv (m + 2))
      (plusAnisoLin b c ((reindexVectorEquiv (plusIndexEquiv (m + 2))).symm
        (Pi.single (plusIndexEquiv (m + 2) s) 1))) = _
  have e1 : (reindexVectorEquiv (plusIndexEquiv (m + 2))).symm
      (Pi.single (plusIndexEquiv (m + 2) s) (1 : K)) = Pi.single s 1 := by
    rw [← pi_single_comp_plusIndexEquiv s]
    rfl
  rw [e1, plusAnisoLin_apply, plusAnisoFun_single_succ_succ b c j s hs, ← e1,
    LinearEquiv.apply_symm_apply]

theorem plusAnisoIsometry_symm_single {b c : K} (hb : b ≠ 0) (j : Fin m)
    (s : Fin (m + 2) ⊕ Fin (m + 2)) (hs : s = .inl j.succ.succ ∨ s = .inr j.succ.succ) :
    (plusAnisoIsometry b c hb).toLinearEquiv.symm (Pi.single (plusIndexEquiv (m + 2) s) 1) =
      Pi.single (plusIndexEquiv (m + 2) s) 1 := by
  rw [LinearEquiv.symm_apply_eq]
  exact (plusAnisoIsometry_single hb j s hs).symm

end Fix

section Bridge

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

variable (m) in
@[expose] noncomputable def plusAnisoProjEquiv {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    matrixProjectiveDerived (plusAnisoQuad K m b c) ≃*
      matrixProjectiveDerived (coordinateQuadPlus (m + 2) K) :=
  ((MulEquiv.ofBijective (projHom (plusAnisoQuad K m b c))
    ⟨projHom_injective (isAnisoCoord_plusAnisoQuad (m := m) hirr).exists_ne_zero,
      projHom_surjective _⟩).symm.trans
    (orthDerivedCongr (plusAnisoIsometry b c (coeff_ne_zero_of_irreducible' hirr)))).trans
    (MulEquiv.ofBijective (projHom (coordinateQuadPlus (m + 2) K))
      ⟨projHom_injective (isHypCoord_coordinateQuadPlus (K := K) (0 : Fin (m + 2))).exists_ne_zero,
        projHom_surjective _⟩)

theorem plusAnisoProjEquiv_projHom {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (g : orthDerived (plusAnisoQuad K m b c)) :
    plusAnisoProjEquiv m hirr (projHom _ g) =
      projHom _ (orthDerivedCongr (plusAnisoIsometry b c (coeff_ne_zero_of_irreducible' hirr)) g) := by
  have h : (MulEquiv.ofBijective (projHom (plusAnisoQuad K m b c))
      ⟨projHom_injective (isAnisoCoord_plusAnisoQuad (m := m) hirr).exists_ne_zero,
        projHom_surjective _⟩).symm (projHom _ g) = g :=
    (MulEquiv.ofBijective _ _).symm_apply_apply g
  simp only [plusAnisoProjEquiv, MulEquiv.trans_apply, h]
  rfl

theorem plusAnisoProjEquiv_rootPairElt {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hm : 1 ≤ m) {j₁ j₂ j₃ : Fin m} (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃) :
    plusAnisoProjEquiv m hirr (rootPairElt
      (regular_plusAnisoQuad (K := K) (b := b) (c := c) (coeff_ne_zero_of_irreducible' hirr) hm).1
      ((isHypCoord_plusAnisoQuad b c j₁).orth (isHypCoord_plusAnisoQuad b c j₂)
        (pairDisjoint_plusAniso_hyp h12))
      ((isHypCoord_plusAnisoQuad b c j₁).orth (isHypCoord_plusAnisoQuad b c j₃)
        (pairDisjoint_plusAniso_hyp h13))
      ((isHypCoord_plusAnisoQuad b c j₂).orth (isHypCoord_plusAnisoQuad b c j₃)
        (pairDisjoint_plusAniso_hyp h23))) =
    rootPairElt (regular_coordinateQuadPlus (m + 2) K (by omega)).1
      ((isHypCoord_coordinateQuadPlus (K := K) j₁.succ.succ).orth
        (isHypCoord_coordinateQuadPlus j₂.succ.succ)
        (pairDisjoint_plus (Fin.succ_injective _ |>.ne (Fin.succ_injective _ |>.ne h12))))
      ((isHypCoord_coordinateQuadPlus (K := K) j₁.succ.succ).orth
        (isHypCoord_coordinateQuadPlus j₃.succ.succ)
        (pairDisjoint_plus (Fin.succ_injective _ |>.ne (Fin.succ_injective _ |>.ne h13))))
      ((isHypCoord_coordinateQuadPlus (K := K) j₂.succ.succ).orth
        (isHypCoord_coordinateQuadPlus j₃.succ.succ)
        (pairDisjoint_plus (Fin.succ_injective _ |>.ne (Fin.succ_injective _ |>.ne h23)))) := by
  rw [rootPairElt, plusAnisoProjEquiv_projHom, rootPairElt]
  congr 1
  apply Subtype.ext
  refine LinearEquiv.ext fun x => ?_
  rw [orthDerivedCongr_apply]
  change (plusAnisoIsometry b c (coeff_ne_zero_of_irreducible' hirr)).toLinearEquiv
      (eichler (plusAnisoQuad K m b c) (Pi.single (plusIndexEquiv (m + 2) (.inl j₁.succ.succ)) 1)
        (Pi.single (plusIndexEquiv (m + 2) (.inl j₂.succ.succ)) 1)
        ((plusAnisoIsometry b c (coeff_ne_zero_of_irreducible' hirr)).toLinearEquiv.symm x)) =
    eichler (coordinateQuadPlus (m + 2) K)
      (Pi.single (plusIndexEquiv (m + 2) (.inl j₁.succ.succ)) 1)
      (Pi.single (plusIndexEquiv (m + 2) (.inl j₂.succ.succ)) 1) x
  rw [eichler_conj_of_isometry _ (plusAnisoIsometry b c _).map_app,
    show (plusAnisoIsometry b c (coeff_ne_zero_of_irreducible' hirr)).toLinearEquiv
      (Pi.single (plusIndexEquiv (m + 2) (.inl j₁.succ.succ)) 1) =
        Pi.single (plusIndexEquiv (m + 2) (.inl j₁.succ.succ)) 1 from
      plusAnisoIsometry_single _ j₁ _ (Or.inl rfl),
    show (plusAnisoIsometry b c (coeff_ne_zero_of_irreducible' hirr)).toLinearEquiv
      (Pi.single (plusIndexEquiv (m + 2) (.inl j₂.succ.succ)) 1) =
        Pi.single (plusIndexEquiv (m + 2) (.inl j₂.succ.succ)) 1 from
      plusAnisoIsometry_single _ j₂ _ (Or.inl rfl)]

omit [Finite K] [CharP K 2] in
theorem orthDerivedCongr_plusAnisoIsometry_fix_iff {b c : K} (hb : b ≠ 0) (j : Fin m)
    (s : Fin (m + 2) ⊕ Fin (m + 2)) (hs : s = .inl j.succ.succ ∨ s = .inr j.succ.succ)
    (g : orthDerived (plusAnisoQuad K m b c)) :
    ((orthDerivedCongr (plusAnisoIsometry b c hb) g : orthDerived _) :
        (Fin (2 * (m + 2)) → K) ≃ₗ[K] (Fin (2 * (m + 2)) → K))
        (Pi.single (plusIndexEquiv (m + 2) s) 1) = Pi.single (plusIndexEquiv (m + 2) s) 1 ↔
      (g : (Fin (2 * (m + 2)) → K) ≃ₗ[K] (Fin (2 * (m + 2)) → K))
        (Pi.single (plusIndexEquiv (m + 2) s) 1) = Pi.single (plusIndexEquiv (m + 2) s) 1 := by
  rw [orthDerivedCongr_apply, plusAnisoIsometry_symm_single hb j s hs]
  constructor
  · intro h
    apply (plusAnisoIsometry b c hb).toLinearEquiv.injective
    rw [h]
    exact (plusAnisoIsometry_single hb j s hs).symm
  · intro h
    rw [h]
    exact plusAnisoIsometry_single hb j s hs

theorem map_stabPairsBar_plusAnisoProjEquiv {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (j₁ j₂ : Fin m) :
    (stabPairsBar (plusAnisoQuad K m b c) (plusIndexEquiv (m + 2) (.inl j₁.succ.succ))
        (plusIndexEquiv (m + 2) (.inr j₁.succ.succ)) (plusIndexEquiv (m + 2) (.inl j₂.succ.succ))
        (plusIndexEquiv (m + 2) (.inr j₂.succ.succ))).map
        (plusAnisoProjEquiv m hirr).toMonoidHom =
      stabTwoBar K j₁.succ.succ j₂.succ.succ := by
  have hb := coeff_ne_zero_of_irreducible' hirr
  ext y
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_subgroupOf.mp hg
    refine ⟨orthDerivedCongr (plusAnisoIsometry b c hb) g, mem_subgroupOf.mpr
      ⟨⟨?_, ?_⟩, ?_, ?_⟩, (plusAnisoProjEquiv_projHom hirr g).symm⟩
    · exact (orthDerivedCongr_plusAnisoIsometry_fix_iff hb j₁ _ (Or.inl rfl) g).mpr h1
    · exact (orthDerivedCongr_plusAnisoIsometry_fix_iff hb j₁ _ (Or.inr rfl) g).mpr h2
    · exact (orthDerivedCongr_plusAnisoIsometry_fix_iff hb j₂ _ (Or.inl rfl) g).mpr h3
    · exact (orthDerivedCongr_plusAnisoIsometry_fix_iff hb j₂ _ (Or.inr rfl) g).mpr h4
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_subgroupOf.mp hh
    obtain ⟨g, hgh⟩ : ∃ g, orthDerivedCongr (plusAnisoIsometry b c hb) g = h :=
      ⟨_, MulEquiv.apply_symm_apply _ h⟩
    subst hgh
    refine ⟨projHom _ g, ⟨g, mem_subgroupOf.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩, rfl⟩,
      plusAnisoProjEquiv_projHom hirr g⟩
    · exact (orthDerivedCongr_plusAnisoIsometry_fix_iff hb j₁ _ (Or.inl rfl) g).mp h1
    · exact (orthDerivedCongr_plusAnisoIsometry_fix_iff hb j₁ _ (Or.inr rfl) g).mp h2
    · exact (orthDerivedCongr_plusAnisoIsometry_fix_iff hb j₂ _ (Or.inl rfl) g).mp h3
    · exact (orthDerivedCongr_plusAnisoIsometry_fix_iff hb j₂ _ (Or.inr rfl) g).mp h4

theorem isQuasisimple_stabPairsBar_plusAniso (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {j₁ j₂ : Fin m} (h12 : j₁ ≠ j₂) :
    CFSG.IsQuasisimple (stabPairsBar (plusAnisoQuad K m b c)
        (plusIndexEquiv (m + 2) (.inl j₁.succ.succ)) (plusIndexEquiv (m + 2) (.inr j₁.succ.succ))
        (plusIndexEquiv (m + 2) (.inl j₂.succ.succ))
        (plusIndexEquiv (m + 2) (.inr j₂.succ.succ))) ∧
      center (stabPairsBar (plusAnisoQuad K m b c)
        (plusIndexEquiv (m + 2) (.inl j₁.succ.succ)) (plusIndexEquiv (m + 2) (.inr j₁.succ.succ))
        (plusIndexEquiv (m + 2) (.inl j₂.succ.succ))
        (plusIndexEquiv (m + 2) (.inr j₂.succ.succ))) = ⊥ := by
  have hq := isQuasisimple_stabTwoBar (K := K) (n := m + 2) (by omega)
    (Fin.succ_injective _ |>.ne (Fin.succ_injective _ |>.ne h12))
  set φ := ((stabPairsBar (plusAnisoQuad K m b c)
      (plusIndexEquiv (m + 2) (.inl j₁.succ.succ)) (plusIndexEquiv (m + 2) (.inr j₁.succ.succ))
      (plusIndexEquiv (m + 2) (.inl j₂.succ.succ))
      (plusIndexEquiv (m + 2) (.inr j₂.succ.succ))).equivMapOfInjective
    (plusAnisoProjEquiv m hirr).toMonoidHom (plusAnisoProjEquiv m hirr).injective).trans
    (MulEquiv.subgroupCongr (map_stabPairsBar_plusAnisoProjEquiv hirr j₁ j₂)) with hφ
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hq.1, ?_⟩
  have hmap := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ.symm
  rw [← hmap, hq.2, Subgroup.map_bot]

end Bridge

end CFSG.SeitzReduction.OmegaPilot
