module

import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusBlocks
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLevi

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type} [Field K]

theorem maxStab_le_orthElementaryGroup [Finite K] [CharP K 2] (hr : 3 ≤ r) :
    maxStab r K ≤ orthElementaryGroup (quadPlus r K) := by
  obtain ⟨-, -, -, ⟨χ, hE, hS, hs⟩, -⟩ :=
    orthogonal_geometry_split_maximal_family_character (K := K) hr
  have hn0 : 0 < r := by omega
  have hnd := nondegenerate_polarBilin_quadPlus r K
  have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) =
      2 * Nat.card (orthElementaryGroup (quadPlus r K)) :=
    CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_eq_two_mul hnd
      (plusPair_orth (K := K) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
      (regular_quadPlus (by omega)).2
      (orthogonalGroup_le_closure_of_two_eq_zero (plusFamily_orth hn0) hnd CharTwo.two_eq_zero
        (fun x hx _ => eq_zero_of_mem_tailSpace_plusFamily hn0 hx)
        (fun x hx hx0 => absurd (eq_zero_of_mem_tailSpace_plusFamily hn0 hx) hx0) (by omega))
  have : Finite (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) :=
      Nat.finite_of_card_ne_zero (by
    rw [hcard]
    have : Finite (orthElementaryGroup (quadPlus r K)) := finite_orthElementaryGroup
    exact mul_ne_zero two_ne_zero Nat.card_pos.ne')
  have hrange : χ.range = ⊤ := by
    refine eq_top_iff.2 fun u _ => ?_
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one χ⟩
    · exact ⟨_, hs⟩
  have hidx : χ.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have hEcard : Nat.card ((orthElementaryGroup (quadPlus r K)).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K))) =
      Nat.card (orthElementaryGroup (quadPlus r K)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (orthElementaryGroup_le _)).toEquiv
  have heq : (orthElementaryGroup (quadPlus r K)).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) = χ.ker := by
    refine Subgroup.eq_of_le_of_card_ge hE ?_
    have h1 := Subgroup.card_mul_index χ.ker
    rw [hidx, hcard] at h1
    rw [hEcard]
    omega
  intro g hg
  have hgO := (mem_maxStab.1 hg).1
  have h := hS (Subgroup.mem_subgroupOf.2 hg :
    (⟨g, hgO⟩ : TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) ∈ _)
  rw [← heq, Subgroup.mem_subgroupOf] at h
  exact h

section Extend

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

@[expose] noncomputable def plusExtGL {φ : ι → κ} (hφ : Function.Injective φ) :
    GL ι K →* GL κ K :=
  Units.map { toFun := extendMat hφ, map_one' := extendMat_one hφ, map_mul' := extendMat_mul hφ }

theorem coe_plusExtGL {φ : ι → κ} (hφ : Function.Injective φ) (A : GL ι K) :
    ((plusExtGL hφ A : GL κ K) : Matrix κ κ K) = extendMat hφ (A : Matrix ι ι K) :=
  rfl

omit [DecidableEq ι] in
theorem extendMat_mulVec_map {φ : ι → κ} (hφ : Function.Injective φ) (M : Matrix ι ι K)
    (v : κ → K) (s : ι) : (extendMat hφ M *ᵥ v) (φ s) = (M *ᵥ (v ∘ φ)) s := by
  simp only [mulVec, dotProduct, Function.comp_apply]
  symm
  refine Fintype.sum_of_injective φ hφ _ _ (fun y hy => ?_) fun s' => ?_
  · rw [extendMat_apply_of_not_mem hφ M (Or.inr hy), one_apply_ne (fun h => hy ⟨s, h⟩),
      zero_mul]
  · rw [extendMat_apply_map]

omit [Fintype ι] [DecidableEq ι] in
theorem extendMat_mulVec_of_not_mem {φ : ι → κ} (hφ : Function.Injective φ) (M : Matrix ι ι K)
    (v : κ → K) {x : κ} (hx : x ∉ Set.range φ) : (extendMat hφ M *ᵥ v) x = v x := by
  have h : ∀ y, extendMat hφ M x y = (1 : Matrix κ κ K) x y := fun y =>
    extendMat_apply_of_not_mem hφ M (Or.inl hx)
  simp only [mulVec, dotProduct, h]
  exact congrFun (one_mulVec v) x

end Extend

theorem extendMat_apply_eq_zero {ι κ : Type} [DecidableEq κ] {φ : ι → κ}
    (hφ : Function.Injective φ) (pos : κ → ℕ) {a b : ℕ}
    (hrange : ∀ x ∈ Set.range φ, a ≤ pos x ∧ pos x < b) (M : Matrix ι ι K) {c : ℕ}
    (hc : c ≤ a ∨ b ≤ c) {u w : κ} (hw : pos w < c) (hu : c ≤ pos u) :
    extendMat hφ M u w = 0 := by
  have huw : u ≠ w := fun h => by rw [h] at hu; omega
  have hnot : u ∉ Set.range φ ∨ w ∉ Set.range φ := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    have h1 := hrange u h.1
    have h2 := hrange w h.2
    omega
  rw [extendMat_apply_of_not_mem hφ M hnot, one_apply_ne huw]

theorem mapsTo_of_plusCut {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} {c : ℕ}
    (hg : PlusCut g c) : ∀ v ∈ plusCutSpace r K c, g v ∈ plusCutSpace r K c := by
  intro v hv u hu
  rw [apply_eq_autMat_mulVec, mulVec, dotProduct]
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases hw : plusPos r w < c
  · rw [hg u w hw hu, zero_mul]
  · rw [hv w (not_lt.mp hw), mul_zero]

theorem smul_flag_of_plusCut {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} {d : ℕ}
    (hd : d ≤ r) (hg : PlusCut g d) (hg' : PlusCut g⁻¹ d) : g • flag r K d = flag r K d := by
  rw [flag_eq_plusCutSpace hd]
  refine le_antisymm ?_ fun v hv => ⟨g⁻¹ v, mapsTo_of_plusCut hg' v hv, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact mapsTo_of_plusCut hg v hv
  · change g (g⁻¹ v) = v
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl

@[expose] def plusFinIdx {a b : ℕ} (hb : b ≤ r) (k : Fin (b - a)) : Fin r :=
  ⟨a + k, by have := k.isLt; omega⟩

theorem plusFinIdx_injective {a b : ℕ} (hb : b ≤ r) :
    Function.Injective (plusFinIdx (a := a) hb) := fun k k' h =>
  Fin.ext (by simpa [plusFinIdx] using congrArg Fin.val h)

theorem plusEIdx_eq {a b : ℕ} (hb : b ≤ r) : plusEIdx (a := a) hb = Sum.inl ∘ plusFinIdx hb :=
  rfl

variable (K) in
@[expose] noncomputable def plusFlagLevi {a b : ℕ} (hb : b ≤ r) :
    GL (Fin (b - a)) K →* ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  (levi r K).comp (plusExtGL (plusFinIdx_injective hb))

theorem autMat_plusFlagLevi {a b : ℕ} (hb : b ≤ r) (A : GL (Fin (b - a)) K) :
    autMat (plusFlagLevi K hb A) = fromBlocks
      (extendMat (plusFinIdx_injective hb) (A : Matrix (Fin (b - a)) (Fin (b - a)) K)) 0 0
      (extendMat (plusFinIdx_injective hb)
        ((A⁻¹ : GL (Fin (b - a)) K) : Matrix (Fin (b - a)) (Fin (b - a)) K)ᵀ) := by
  rw [autMat_apply, plusFlagLevi, MonoidHom.comp_apply, toMatrix'_levi, blockDiagInv, coe_plusExtGL,
    extendMat_inv _ (Matrix.isUnit_det_of_invertible _), extendMat_transpose, Matrix.coe_units_inv]

theorem plusCut_plusFlagLevi {a b : ℕ} (hb : b ≤ r) (A : GL (Fin (b - a)) K) {c : ℕ} (hcr : c ≤ r)
    (hc : c ≤ a ∨ b ≤ c) : PlusCut (plusFlagLevi K hb A) c := by
  have hrange : ∀ x ∈ Set.range (plusFinIdx (a := a) hb), a ≤ x.val ∧ x.val < b := by
    rintro _ ⟨k, rfl⟩
    simp only [plusFinIdx]
    have := k.isLt
    omega
  intro u w hw hu
  rw [autMat_plusFlagLevi]
  rcases w with j | j
  · rcases u with i | i
    · exact extendMat_apply_eq_zero _ Fin.val hrange _ hc hw hu
    · rfl
  · rw [plusPos_inr] at hw
    have := j.isLt
    omega

theorem plusFlagLevi_mem_plusFlagStab [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, d ≤ r) {b : ℕ} (hbD : b ∈ D) (A : GL (Fin (b - predCut D b)) K) :
    plusFlagLevi K (hD b hbD) A ∈ plusFlagStab K r D := by
  refine mem_plusFlagStab.2 ⟨maxStab_le_orthElementaryGroup hr (levi_mem_maxStab _),
    fun d hd => smul_flag_of_plusCut (hD d hd) (plusCut_plusFlagLevi _ _ (hD d hd) ?_) ?_⟩
  · by_cases hdb : d < b
    · exact Or.inl (le_predCut hd hdb)
    · exact Or.inr (not_lt.mp hdb)
  · rw [← map_inv]
    refine plusCut_plusFlagLevi _ _ (hD d hd) ?_
    by_cases hdb : d < b
    · exact Or.inl (le_predCut hd hdb)
    · exact Or.inr (not_lt.mp hdb)

theorem fromBlocks_submatrix_inl {ι : Type} (ψ : ι → Fin r)
    (M N : Matrix (Fin r) (Fin r) K) :
    (fromBlocks M 0 0 N).submatrix (Sum.inl ∘ ψ) (Sum.inl ∘ ψ) = M.submatrix ψ ψ :=
  rfl

theorem plusEBlockHom_plusFlagLevi_self [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, d ≤ r) {b : ℕ} (hbD : b ∈ D) (A : GL (Fin (b - predCut D b)) K) :
    plusEBlockHom hD hbD ⟨plusFlagLevi K (hD b hbD) A, plusFlagLevi_mem_plusFlagStab hr hD hbD A⟩ =
      A := by
  refine Units.ext ?_
  rw [coe_plusEBlockHom]
  change (autMat (plusFlagLevi K (hD b hbD) A)).submatrix (Sum.inl ∘ plusFinIdx (hD b hbD))
    (Sum.inl ∘ plusFinIdx (hD b hbD)) = _
  rw [autMat_plusFlagLevi, fromBlocks_submatrix_inl, submatrix_extendMat]

theorem plusFinIdx_ne_of_ne {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {b b' : ℕ} (hbD : b ∈ D)
    (hb'D : b' ∈ D) (hne : b' ≠ b) (k : Fin (b' - predCut D b')) (k' : Fin (b - predCut D b)) :
    plusFinIdx (hD b' hb'D) k ≠ plusFinIdx (hD b hbD) k' := by
  intro h
  have h' := congrArg Fin.val h
  simp only [plusFinIdx] at h'
  have hk := k.isLt
  have hk' := k'.isLt
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := le_predCut hb'D hlt
    omega
  · have := le_predCut hbD hlt
    omega

theorem plusEBlockHom_plusFlagLevi_of_ne [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, d ≤ r) {b b' : ℕ} (hbD : b ∈ D) (hb'D : b' ∈ D) (hne : b' ≠ b)
    (A : GL (Fin (b - predCut D b)) K) :
    plusEBlockHom hD hb'D ⟨plusFlagLevi K (hD b hbD) A, plusFlagLevi_mem_plusFlagStab hr hD hbD A⟩ =
      1 := by
  refine Units.ext ?_
  rw [coe_plusEBlockHom, Units.val_one]
  change (autMat (plusFlagLevi K (hD b hbD) A)).submatrix (Sum.inl ∘ plusFinIdx (hD b' hb'D))
    (Sum.inl ∘ plusFinIdx (hD b' hb'D)) = 1
  rw [autMat_plusFlagLevi, fromBlocks_submatrix_inl]
  exact submatrix_extendMat_of_disjoint _ (plusFinIdx_injective _)
    (plusFinIdx_ne_of_ne hD hbD hb'D hne) _

theorem plusResBlockHom_plusFlagLevi [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ} (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) {b : ℕ} (hbD : b ∈ D)
    (hbt : b ≤ t) (A : GL (Fin (b - predCut D b)) K) :
    plusResBlockHom hD ht htm
      ⟨plusFlagLevi K (hD b hbD) A, plusFlagLevi_mem_plusFlagStab hr hD hbD A⟩ = 1 := by
  refine Units.ext ?_
  rw [coe_plusResBlockHom, Units.val_one, autMat_plusFlagLevi]
  have hout : ∀ s : Fin m, (⟨t + s, by have := s.isLt; omega⟩ : Fin r) ∉
      Set.range (plusFinIdx (a := predCut D b) (hD b hbD)) := by
    rintro s ⟨k, hk⟩
    have h1 := congrArg Fin.val hk
    simp only [plusFinIdx] at h1
    have := k.isLt
    omega
  have hinj : ∀ s s' : Fin m, s ≠ s' →
      (⟨t + s, by have := s.isLt; omega⟩ : Fin r) ≠ ⟨t + s', by have := s'.isLt; omega⟩ :=
    fun s s' hss h => hss (Fin.ext (by simpa using congrArg Fin.val h))
  ext x y
  rcases x with s | s <;> rcases y with s' | s' <;>
    simp only [submatrix_apply, plusResIdx_inl, plusResIdx_inr, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply,
      one_apply_ne Sum.inl_ne_inr, one_apply_ne Sum.inr_ne_inl]
  · rw [extendMat_apply_of_not_mem _ _ (Or.inl (hout s))]
    by_cases hss : s = s'
    · rw [hss, one_apply_eq, one_apply_eq]
    · rw [one_apply_ne (hinj s s' hss), one_apply_ne (fun h => hss (Sum.inl_injective h))]
  · rw [extendMat_apply_of_not_mem _ _ (Or.inl (hout s))]
    by_cases hss : s = s'
    · rw [hss, one_apply_eq, one_apply_eq]
    · rw [one_apply_ne (hinj s s' hss), one_apply_ne (fun h => hss (Sum.inr_injective h))]

end CFSG.AGLEmbedding.LeviBlock
