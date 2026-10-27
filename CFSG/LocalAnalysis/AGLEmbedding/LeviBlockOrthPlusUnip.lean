module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusBlocks
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviUnipotent
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLevi

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type} [Field K]

theorem mulVec_comp_eq_of_support {ι κ : Type} [Fintype ι] [Fintype κ] {φ : ι → κ}
    (hφ : Function.Injective φ) (M : Matrix κ κ K) {v : κ → K}
    (hv : ∀ x, x ∉ Set.range φ → v x = 0) : (M *ᵥ v) ∘ φ = M.submatrix φ φ *ᵥ (v ∘ φ) := by
  funext s
  simp only [Function.comp_apply, mulVec, dotProduct, submatrix_apply]
  symm
  refine Fintype.sum_of_injective φ hφ _ _ (fun x hx => by rw [hv x hx, mul_zero]) fun _ => rfl

theorem quadPlus_eq_add_res {t m : ℕ} (htm : t + m = r) (v : Fin r ⊕ Fin r → K) :
    quadPlus r K v = ∑ i : Fin t, v (Sum.inl ⟨i, by have := i.isLt; omega⟩) *
        v (Sum.inr ⟨i, by have := i.isLt; omega⟩) + quadPlus m K (v ∘ plusResIdx htm) := by
  subst htm
  rw [quadPlus_apply, quadPlus_apply, Fin.sum_univ_add]
  rfl

theorem low_not_mem_range_plusResIdx {t m : ℕ} (htm : t + m = r) (i : Fin t) :
    (Sum.inl ⟨i, by have := i.isLt; omega⟩ : Fin r ⊕ Fin r) ∉ Set.range (plusResIdx htm) ∧
      (Sum.inr ⟨i, by have := i.isLt; omega⟩ : Fin r ⊕ Fin r) ∉ Set.range (plusResIdx htm) := by
  have hi := i.isLt
  refine ⟨fun hc => ?_, fun hc => ?_⟩ <;>
  · rw [mem_range_plusResIdx] at hc
    simp only [plusPos_inl, plusPos_inr] at hc
    omega

theorem quadPlus_resBlock_mulVec {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) (g : ↥(plusFlagStab K r D))
    (w : Fin m ⊕ Fin m → K) :
    quadPlus m K ((plusResBlockHom hD ht htm g : Matrix _ _ K) *ᵥ w) = quadPlus m K w := by
  set v : Fin r ⊕ Fin r → K := Function.extend (plusResIdx htm) w 0 with hv
  have hvφ : v ∘ plusResIdx htm = w := Function.extend_comp (plusResIdx_injective htm) _ _
  have hsupp : ∀ x, x ∉ Set.range (plusResIdx htm) → v x = 0 := fun x hx =>
    Function.extend_apply' _ _ _ fun ⟨s, hs⟩ => hx ⟨s, hs⟩
  have hgO := mem_orthogonalGroup_of_mem_plusFlagStab g.2
  have hcut := plusCut_of_mem_plusFlagStab hD g.2 ht
  have hgv : ∀ i : Fin t, (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) v
      (Sum.inr ⟨i, by have := i.isLt; omega⟩) = 0 := by
    intro i
    have hi : 2 * r - t ≤ plusPos r (Sum.inr ⟨i, by have := i.isLt; omega⟩) := by
      rw [plusPos_inr]
      have := i.isLt
      simp only
      omega
    rw [apply_eq_autMat_mulVec, mulVec, dotProduct]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x ∈ Set.range (plusResIdx htm)
    · rw [hcut.2 _ _ ((mem_range_plusResIdx htm x).1 hx).2 hi, zero_mul]
    · rw [hsupp x hx, mul_zero]
  have hQ := map_of_mem hgO v
  rw [quadPlus_eq_add_res htm, quadPlus_eq_add_res htm v] at hQ
  simp only [hgv, mul_zero, Finset.sum_const_zero, zero_add] at hQ
  simp only [hsupp _ (low_not_mem_range_plusResIdx htm _).1, zero_mul, Finset.sum_const_zero,
    zero_add] at hQ
  rw [hvφ, apply_eq_autMat_mulVec,
    mulVec_comp_eq_of_support (plusResIdx_injective htm) _ hsupp, hvφ] at hQ
  rw [coe_plusResBlockHom]
  exact hQ

@[expose] noncomputable def plusResAut {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) :
    ↥(plusFlagStab K r D) →* ((Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) :=
  (matrixEquiv m K).toMonoidHom.comp (plusResBlockHom hD ht htm)

theorem plusResAut_mem_orthogonalGroup {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) (g : ↥(plusFlagStab K r D)) :
    plusResAut hD ht htm g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  exact quadPlus_resBlock_mulVec hD ht htm g w

theorem predCut_one {D : Finset ℕ} (hD : ∀ d ∈ D, 1 ≤ d) : predCut D 1 = 0 := by
  rw [predCut, Finset.filter_false_of_mem fun d hd => by have := hD d hd; omega,
    Finset.sup_empty]
  rfl

theorem predCut_sup_succ (D : Finset ℕ) : predCut D (D.sup id + 1) = D.sup id := by
  refine le_antisymm (Finset.sup_le fun c hc => Finset.le_sup (f := id)
    (Finset.mem_filter.mp hc).1) ?_
  rcases D.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sup_empty]
    exact bot_le
  · obtain ⟨c, hc, hce⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [hce]
    exact le_predCut hc (by simp only [id] at hce ⊢; omega)

theorem predCut_mono (D : Finset ℕ) {b b' : ℕ} (h : b ≤ b') : predCut D b ≤ predCut D b' :=
  Finset.sup_mono (Finset.monotone_filter_right _ fun _ _ hc => lt_of_lt_of_le hc h)

theorem predCut_succ_of_mem {D : Finset ℕ} {i : ℕ} (hi : i + 1 ∈ D) :
    predCut D (i + 2) = i + 1 :=
  le_antisymm (Nat.le_of_lt_succ (predCut_lt (by omega))) (le_predCut hi (by omega))

theorem predCut_succ_of_not_mem {D : Finset ℕ} {i : ℕ} (hi : i + 1 ∉ D) :
    predCut D (i + 2) = predCut D (i + 1) := by
  rw [predCut, predCut]
  congr 1
  ext c
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hc, hci⟩
    refine ⟨hc, ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hci with h | h
    · exact h
    · exact absurd (h ▸ hc) hi
  · rintro ⟨hc, hci⟩
    exact ⟨hc, by omega⟩

theorem isPGroup_of_plusBlocks [CharP K 2] {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r)
    (hD1 : ∀ d ∈ D, 1 ≤ d) {N : Subgroup ↥(plusFlagStab K r D)}
    (hN : ∀ g ∈ N, (∀ b (hb : b ∈ D), plusEBlockHom hD hb g = 1) ∧
      ∀ x ∈ plusCutSpace r K (2 * r - D.sup id),
        (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) x - x ∈ plusCutSpace r K (D.sup id)) :
    IsPGroup 2 N := by
  set t := D.sup id with ht
  have htr : t ≤ r := Finset.sup_le hD
  set F : ℕ → Submodule K (Fin r ⊕ Fin r → K) := fun i => plusCutSpace r K (predCut D (i + 1))
    with hF
  have hF0 : F 0 = ⊥ := by
    simp only [hF, zero_add, predCut_one hD1, plusCutSpace_zero]
  have hpredr : ∀ i, predCut D i ≤ r := fun i =>
    (Finset.sup_le fun c hc => hD c (Finset.mem_filter.mp hc).1)
  have key := CFSG.SeitzReduction.OmegaPilot.isPGroup_two_of_flag
    (polarBilin (quadPlus r K)) (N.map (plusFlagStab K r D).subtype) F hF0 t
    (fun i _ => plusCutSpace_mono (predCut_mono D (by omega))) ?_
  · exact key.of_equiv (N.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm
  rintro _ ⟨g, hgN, rfl⟩
  obtain ⟨hblock, htop⟩ := hN g hgN
  have hgO := mem_orthogonalGroup_of_mem_plusFlagStab g.2
  refine ⟨fun x y => by simp only [polarBilin_apply_apply, Subgroup.coe_subtype,
    polar_map_of_mem hgO], fun i hi x hx => ?_, fun x hx => ?_⟩
  · simp only [hF] at hx ⊢
    have hpred := predCut_eq_zero_or_mem D (i + 1)
    by_cases hiD : i + 1 ∈ D
    · rw [predCut_succ_of_mem hiD] at hx
      have h1 : (autMat (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))).submatrix
          (plusEIdx (a := predCut D (i + 1)) (hD _ hiD))
          (plusEIdx (a := predCut D (i + 1)) (hD _ hiD)) = 1 := by
        rw [← coe_plusEBlockHom hD hiD, hblock _ hiD, Units.val_one]
      have hgx : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) x ∈
          plusCutSpace r K (i + 1) := by
        rw [← flag_eq_plusCutSpace (hD _ hiD), ← smul_flag_of_mem_plusFlagStab g.2 (Or.inr hiD)]
        rw [← flag_eq_plusCutSpace (hD _ hiD)] at hx
        exact ⟨x, hx, rfl⟩
      exact sub_mem_plusCutSpace_of_block_eq_one (mem_range_plusEIdx (hD _ hiD))
        (plusCut_of_mem_plusFlagStab hD g.2 hpred).1 h1 hx hgx
    · rw [predCut_succ_of_not_mem hiD] at hx
      have hgx : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) x ∈
          plusCutSpace r K (predCut D (i + 1)) := by
        rw [← flag_eq_plusCutSpace (hpredr _), ← smul_flag_of_mem_plusFlagStab g.2 hpred]
        rw [← flag_eq_plusCutSpace (hpredr _)] at hx
        exact ⟨x, hx, rfl⟩
      exact sub_mem hgx hx
  · have hFt : F t = flag r K t := by
      change plusCutSpace r K (predCut D (t + 1)) = flag r K t
      rw [ht, predCut_sup_succ, ← ht, flag_eq_plusCutSpace htr]
    rw [hFt, mem_orthogonal_flag_iff htr] at hx
    rw [hFt, flag_eq_plusCutSpace htr]
    exact htop x hx

theorem sub_mem_of_plusResBlockHom_eq_one {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) {g : ↥(plusFlagStab K r D)}
    (hg : plusResBlockHom hD ht htm g = 1) {x : Fin r ⊕ Fin r → K}
    (hx : x ∈ plusCutSpace r K (2 * r - t)) :
    (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) x - x ∈ plusCutSpace r K t := by
  have h1 : (autMat (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))).submatrix
      (plusResIdx htm) (plusResIdx htm) = 1 := by
    rw [← coe_plusResBlockHom hD ht htm, hg, Units.val_one]
  have hgx : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) x ∈
      plusCutSpace r K (2 * r - t) := by
    rcases ht with rfl | ht
    · intro u hu
      exact absurd (plusPos_lt u) (by omega)
    · exact mapsTo_orthogonal_of_smul_eq (mem_orthogonalGroup_of_mem_plusFlagStab g.2) (by omega)
        (smul_flag_of_mem_plusFlagStab g.2 (Or.inr ht)) x hx
  exact sub_mem_plusCutSpace_of_block_eq_one (mem_range_plusResIdx htm)
    (plusCut_of_mem_plusFlagStab hD g.2 ht).1 h1 hx hgx

end CFSG.AGLEmbedding.LeviBlock
