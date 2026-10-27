module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourAniso

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadMinus regular_coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Frame

variable {K : Type} [Field K] [CharP K 2] {d m : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b : Fin m → Fin d}

theorem IsHypFrame.pairSwap_conj_frameLin (h : IsHypFrame Q a b) {p p' : Fin m} (hpp : p ≠ p')
    (t : Fin m → Kˣ) :
    pairSwap Q (a p) (b p) (a p') (b p') * frameLin a b t *
        (pairSwap Q (a p) (b p) (a p') (b p'))⁻¹ =
      frameLin a b (fun k => t (Equiv.swap p p' k)) := by
  set s := pairSwap Q (a p) (b p) (a p') (b p') with hs
  set t' : Fin m → Kˣ := fun k => t (Equiv.swap p p' k) with ht'
  have key : s.toLinearMap ∘ₗ (frameLin a b t).toLinearMap =
      (frameLin a b t').toLinearMap ∘ₗ s.toLinearMap := by
    refine LinearMap.pi_ext fun i x => ?_
    have hx : (Pi.single i x : Fin d → K) = x • Pi.single i 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hx, LinearMap.map_smul, LinearMap.map_smul]
    congr 1
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    by_cases hA : ∃ k, i = a k
    · obtain ⟨k, rfl⟩ := hA
      have h1 := h.pairSwap_coordFrameVec hpp k true
      rw [coordFrameVec_true, coordFrameVec_true, ← hs] at h1
      rw [h.frameLin_single_left, LinearEquiv.map_smul, h1, h.frameLin_single_left, ht']
      simp only [Equiv.swap_apply_self]
    by_cases hB : ∃ k, i = b k
    · obtain ⟨k, rfl⟩ := hB
      have h1 := h.pairSwap_coordFrameVec hpp k false
      rw [coordFrameVec_false, coordFrameVec_false, ← hs] at h1
      rw [h.frameLin_single_right, LinearEquiv.map_smul, h1, h.frameLin_single_right, ht']
      simp only [Equiv.swap_apply_self]
    simp only [not_exists] at hA hB
    have hfix : s (Pi.single i 1) = Pi.single i 1 :=
      h.pairSwap_apply_of_vanish (Pi.single_eq_of_ne (Ne.symm (hA p)) _)
        (Pi.single_eq_of_ne (Ne.symm (hB p)) _) (Pi.single_eq_of_ne (Ne.symm (hA p')) _)
        (Pi.single_eq_of_ne (Ne.symm (hB p')) _)
    rw [frameLin_single_of_forall_ne t hA hB, hfix, frameLin_single_of_forall_ne t' hA hB]
  rw [mul_inv_eq_iff_eq_mul]
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  exact LinearMap.congr_fun key v

omit [CharP K 2] in
theorem mulSingle_comp_swap {M : Type*} [One M] (p p' i : Fin m) (μ : M) :
    (fun k => (Pi.mulSingle i μ : Fin m → M) (Equiv.swap p p' k)) =
      Pi.mulSingle (Equiv.swap p p' i) μ := by
  funext k
  by_cases hk : k = Equiv.swap p p' i
  · subst hk
    rw [Equiv.swap_apply_self, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hk, Pi.mulSingle_eq_of_ne]
    intro h'
    apply hk
    rw [← h', Equiv.swap_apply_self]

theorem IsHypFrame.pairSwap_conj_frameLeviTorus_swap (h : IsHypFrame Q a b) {p p' : Fin m}
    (hpp : p ≠ p') (i j : Fin m) (μ : Kˣ) :
    pairSwap Q (a p) (b p) (a p') (b p') * frameLeviTorus a b i j μ *
        (pairSwap Q (a p) (b p) (a p') (b p'))⁻¹ =
      frameLeviTorus a b (Equiv.swap p p' i) (Equiv.swap p p' j) μ := by
  rw [frameLeviTorus_apply, h.pairSwap_conj_frameLin hpp, frameLeviTorus_apply]
  congr 1
  funext k
  rw [Pi.mul_apply, Pi.mul_apply, ← congrFun (mulSingle_comp_swap p p' i μ) k,
    ← congrFun (mulSingle_comp_swap p p' j μ⁻¹) k]

theorem IsHypFrame.map_conj_pairSwap_frameLeviSL_le (h : IsHypFrame Q a b) {p p' : Fin m}
    (hpp : p ≠ p') (i j : Fin m) :
    (frameLeviSL Q a b i j).map (MulAut.conj (pairSwap Q (a p) (b p) (a p') (b p'))).toMonoidHom ≤
      frameLeviSL Q a b (Equiv.swap p p' i) (Equiv.swap p p' j) := by
  rw [frameLeviSL, MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rcases hx with (⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨μ, rfl⟩
  · rw [h.pairSwap_conj_frameRootElt hpp]
    exact frameRootElt_mem_frameLeviSL_left _ _ c
  · rw [h.pairSwap_conj_frameRootElt hpp]
    exact frameRootElt_mem_frameLeviSL_right _ _ c
  · rw [h.pairSwap_conj_frameLeviTorus_swap hpp]
    exact frameLeviTorus_mem_frameLeviSL _ _ μ

theorem IsHypFrame.pairSwap_conj_frameLin_levelParam (h : IsHypFrame Q a b) {p p' : Fin m}
    (hpp : p ≠ p') {J : Finset (Fin m)} {t : Fin m → Kˣ} (ht : t ∈ levelParam J) :
    pairSwap Q (a p) (b p) (a p') (b p') * frameLin a b t *
        (pairSwap Q (a p) (b p) (a p') (b p'))⁻¹ =
      frameLin a b (fun k => t (Equiv.swap p p' k)) ∧
      (fun k => t (Equiv.swap p p' k)) ∈ levelParam (J.image (Equiv.swap p p')) := by
  refine ⟨h.pairSwap_conj_frameLin hpp t, ?_⟩
  intro i hi j hj
  obtain ⟨i', hi', rfl⟩ := Finset.mem_image.1 hi
  obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hj
  simp only [Equiv.swap_apply_self]
  exact ht i' hi' j' hj'

end Frame

theorem map_conj_eq_of_mul_self_eq_one_of_le {P : Type*} [Group P] {x : P} (hx : x * x = 1)
    {H H' : Subgroup P} (h1 : H.map (MulAut.conj x).toMonoidHom ≤ H')
    (h2 : H'.map (MulAut.conj x).toMonoidHom ≤ H) : H.map (MulAut.conj x).toMonoidHom = H' := by
  refine le_antisymm h1 fun y hy => ⟨x * y * x⁻¹, h2 ⟨y, hy, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have h3 : x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
  rw [h3, hx, one_mul, inv_one, mul_one]

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def minusSwapElt (hn : 4 ≤ n) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0) (p p' : Fin (n - 1)) :
    matrixProjectiveDerived (coordinateQuadMinus n K (by omega) β γ) :=
  projHom _ ⟨pairSwap (coordinateQuadMinus n K (by omega) β γ) (minusFrameLeft (by omega) p)
    (minusFrameRight (by omega) p) (minusFrameLeft (by omega) p') (minusFrameRight (by omega) p'),
    pairSwap_mem_orthDerived (regular_coordinateQuadMinus n K β γ hn hirr).1
      (regular_coordinateQuadMinus n K β γ hn hirr).2⟩

variable (hn : 4 ≤ n) {β γ : K} (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0) {p p' : Fin (n - 1)}

theorem minusSwapElt_mul_self (hpp : p ≠ p') :
    minusSwapElt hn hirr p p' * minusSwapElt hn hirr p p' = 1 := by
  have h := isHypFrame_minus K (by omega : 1 ≤ n) β γ
  rw [minusSwapElt, ← map_mul, ← map_one (projHom _)]
  congr 1
  exact Subtype.ext (pairSwap_mul_self (h.hyp p) (h.hyp p') (h.pairDisjoint hpp))

theorem minusSwapElt_inv (hpp : p ≠ p') :
    (minusSwapElt hn hirr p p')⁻¹ = minusSwapElt hn hirr p p' :=
  inv_eq_of_mul_eq_one_right (minusSwapElt_mul_self hn hirr hpp)

theorem minusSwapElt_conj_minusRootElt (hpp : p ≠ p') (i j : Fin (n - 1)) (c : K) :
    minusSwapElt hn hirr p p' * minusRootElt hn hirr i j c * (minusSwapElt hn hirr p p')⁻¹ =
      minusRootElt hn hirr (Equiv.swap p p' i) (Equiv.swap p p' j) c := by
  have h := isHypFrame_minus K (by omega : 1 ≤ n) β γ
  rw [minusSwapElt, minusRootElt, minusRootElt, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (h.pairSwap_conj_frameRootElt hpp i j c)

theorem map_conj_minusSwapElt_frameLeviProj_le (hpp : p ≠ p') (i j : Fin (n - 1)) :
    (frameLeviProj (coordinateQuadMinus n K (by omega) β γ) (minusFrameLeft (by omega))
        (minusFrameRight (by omega)) i j).map
          (MulAut.conj (minusSwapElt hn hirr p p')).toMonoidHom ≤
      frameLeviProj (coordinateQuadMinus n K (by omega) β γ) (minusFrameLeft (by omega))
        (minusFrameRight (by omega)) (Equiv.swap p p' i) (Equiv.swap p p' j) := by
  have h := isHypFrame_minus K (by omega : 1 ≤ n) β γ
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  have hs : pairSwap (coordinateQuadMinus n K (by omega) β γ) (minusFrameLeft (by omega) p)
      (minusFrameRight (by omega) p) (minusFrameLeft (by omega) p')
      (minusFrameRight (by omega) p') ∈ orthDerived (coordinateQuadMinus n K (by omega) β γ) :=
    pairSwap_mem_orthDerived (regular_coordinateQuadMinus n K β γ hn hirr).1
      (regular_coordinateQuadMinus n K β γ hn hirr).2
  refine ⟨⟨_, hs⟩ * y * ⟨_, hs⟩⁻¹, mem_subgroupOf.2 ?_, ?_⟩
  · exact h.map_conj_pairSwap_frameLeviSL_le hpp i j ⟨y, mem_subgroupOf.1 hy, rfl⟩
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    rfl

theorem map_conj_minusSwapElt_minusLevelTorus_le (hpp : p ≠ p') (J : Finset (Fin (n - 1))) :
    (minusLevelTorus (K := K) (by omega) β γ J).map
        (MulAut.conj (minusSwapElt hn hirr p p')).toMonoidHom ≤
      minusLevelTorus (by omega) β γ (J.image (Equiv.swap p p')) := by
  have h := isHypFrame_minus K (by omega : 1 ≤ n) β γ
  rw [minusLevelTorus, minusLevelTorus, minusFrameTorus, minusFrameTorus, h.frameTorusOf_eq_map,
    h.frameTorusOf_eq_map]
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  obtain ⟨hconj, hmem⟩ := h.pairSwap_conj_frameLin_levelParam hpp ht
  refine ⟨_, hmem, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [IsHypFrame.frameHom_apply, IsHypFrame.frameHom_apply, minusSwapElt, ← map_inv, ← map_mul,
    ← map_mul]
  congr 1
  exact Subtype.ext hconj.symm

theorem map_conj_minusSwapElt_minusLevelTorus (hpp : p ≠ p') (J : Finset (Fin (n - 1))) :
    (minusLevelTorus (K := K) (by omega) β γ J).map
        (MulAut.conj (minusSwapElt hn hirr p p')).toMonoidHom =
      minusLevelTorus (by omega) β γ (J.image (Equiv.swap p p')) := by
  refine map_conj_eq_of_mul_self_eq_one_of_le (minusSwapElt_mul_self hn hirr hpp)
    (map_conj_minusSwapElt_minusLevelTorus_le hn hirr hpp J) ?_
  have h2 := map_conj_minusSwapElt_minusLevelTorus_le hn hirr hpp (J.image (Equiv.swap p p'))
  rwa [Finset.image_image, show (Equiv.swap p p') ∘ (Equiv.swap p p') = id from
    funext fun k => Equiv.swap_apply_self p p' k, Finset.image_id] at h2

end Model

section Retarget

variable {G P : Type*} [Group G] [Group P] {L : Subgroup G}

theorem trans_conj_symm_apply (e : L ≃* P) (x y : P) :
    (e.trans (MulAut.conj x)).symm y = e.symm (x⁻¹ * y * x) := by
  rw [MulEquiv.symm_trans_apply, MulAut.conj_symm_apply]

theorem modelToG_trans_conj (e : L ≃* P) (x : P) (A : Subgroup P) :
    modelToG (e.trans (MulAut.conj x)) A = modelToG e (A.map (MulAut.conj x⁻¹).toMonoidHom) := by
  ext g
  rw [UnitaryPilot.mem_modelToG, UnitaryPilot.mem_modelToG]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨x⁻¹ * y * x⁻¹⁻¹, ⟨y, hy, rfl⟩, ?_⟩
    rw [trans_conj_symm_apply, inv_inv]
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [trans_conj_symm_apply]

end Retarget

section RetargetRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {P : Type*} [Group P]

theorem omegaRowAt_trans_conj {e : L ≃* P} {t : G} (htC : t ∈ centralizer (L : Set G)) (x : P)
    {X D : Subgroup P} {r : OmegaRow} (h : OmegaRowAt t (modelToG e X) (modelToG e D) r) :
    OmegaRowAt t (modelToG (e.trans (MulAut.conj x)) X) (modelToG (e.trans (MulAut.conj x)) D)
      r := by
  rw [modelToG_trans_conj, modelToG_trans_conj, UnitaryPilot.modelToG_map_conj,
    UnitaryPilot.modelToG_map_conj]
  exact h.map_conj_of_commute (mem_centralizer_iff.1 htC _ (e.symm x⁻¹).2)

end RetargetRow

section Param

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {n : ℕ}

theorem minusLevelCore_trans_conj_minusSwapElt (hn : 4 ≤ n) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) β γ))
    {p p' : Fin (n - 1)} (hpp : p ≠ p') (J : Finset (Fin (n - 1))) :
    minusLevelCore (e.trans (MulAut.conj (minusSwapElt hn hirr p p'))) J =
      minusLevelCore e (J.image (Equiv.swap p p')) := by
  rw [minusLevelCore, minusLevelCore, modelToG_trans_conj, minusSwapElt_inv hn hirr hpp,
    map_conj_minusSwapElt_minusLevelTorus hn hirr hpp]

theorem MinusRootFieldParam.nonempty_ofSwap {hn : 4 ≤ n} {β γ : K}
    {hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0}
    {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) β γ)} {t : G}
    {F : Type} [Field F] {ι : K →+* F} {σ : F ≃+* F} {p p' : Fin (n - 1)} (hpp : p ≠ p')
    {i j i' j' : Fin (n - 1)} (hi : Equiv.swap p p' i = i') (hj : Equiv.swap p p' j = j')
    (P : MinusRootFieldParam hn hirr (e.trans (MulAut.conj (minusSwapElt hn hirr p p'))) t ι σ
      i j) :
    Nonempty (MinusRootFieldParam hn hirr e t ι σ i' j') := by
  subst hi hj
  refine ⟨{ φ := P.φ, range_eq := ?_, N1 := fun A => ?_, upper := ?_, N3 := P.N3 }⟩
  · rw [P.range_eq, minusLevelCore_trans_conj_minusSwapElt hn hirr e hpp, Finset.image_insert,
      Finset.image_singleton]
  · have h1 := P.N1 A
    rw [modelToG_trans_conj, minusSwapElt_inv hn hirr hpp] at h1
    exact UnitaryPilot.modelToG_mono e (map_conj_minusSwapElt_frameLeviProj_le hn hirr hpp i j) h1
  · rw [P.upper, trans_conj_symm_apply]
    congr 2
    have h2 := minusSwapElt_conj_minusRootElt hn hirr hpp i j 1
    rw [minusSwapElt_inv hn hirr hpp] at h2 ⊢
    exact h2

end Param

section Inputs

theorem minusFourPlanes_swap_facts :
    (⟨0, by omega⟩ : Fin (2 + 2 - 1)) ≠ ⟨1, by omega⟩ ∧
      (⟨1, by omega⟩ : Fin (2 + 2 - 1)) ≠ ⟨2, by omega⟩ ∧
      Equiv.swap (⟨1, by omega⟩ : Fin (2 + 2 - 1)) ⟨2, by omega⟩ ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧
      Equiv.swap (⟨1, by omega⟩ : Fin (2 + 2 - 1)) ⟨2, by omega⟩ ⟨1, by omega⟩ = ⟨2, by omega⟩ ∧
      Equiv.swap (⟨0, by omega⟩ : Fin (2 + 2 - 1)) ⟨1, by omega⟩ ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧
      Equiv.swap (⟨0, by omega⟩ : Fin (2 + 2 - 1)) ⟨1, by omega⟩ ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  decide

theorem omegaMinusFourRootParamOneTwoInput_of_rootParam (hparam : OmegaMinusFourRootParamInput) :
    OmegaMinusFourRootParamOneTwoInput := by
  intro G _ _ L hset f K _ _ _ b c hirr hKc hf2 e t ht hKt hrow F _ _ _ ι σ hσ hfix
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  set x₁ := minusSwapElt (n := 2 + 2) le_rfl hirr ⟨0, by omega⟩ ⟨1, by omega⟩ with hx₁
  set x₂ := minusSwapElt (n := 2 + 2) le_rfl hirr ⟨1, by omega⟩ ⟨2, by omega⟩ with hx₂
  set e₁ := e.trans (MulAut.conj x₁) with he₁
  set e₂ := e₁.trans (MulAut.conj x₂) with he₂
  have hrow₂ : ∀ k : Fin (4 - 1),
      OmegaRowAt t (modelToG e₂ (minusPairTorus (K := K) (by norm_num) b c k))
        (modelToG e₂ (minusPairPerp (K := K) (by norm_num) b c k)) .field :=
    fun k => omegaRowAt_trans_conj htC x₂ (omegaRowAt_trans_conj htC x₁ (hrow k))
  obtain ⟨h01, h12, s0, s1, s0', s2'⟩ := minusFourPlanes_swap_facts
  obtain ⟨P₂⟩ := hparam G L hset f K b c hirr hKc hf2 e₂ t ht hKt hrow₂ F ι σ hσ hfix
  obtain ⟨P₁⟩ := MinusRootFieldParam.nonempty_ofSwap (e := e₁) h12 s0 s1 P₂
  exact MinusRootFieldParam.nonempty_ofSwap (e := e) h01 s0' s2' P₁

end Inputs

end CFSG.SeitzReduction.OmegaPilot
