module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Witt
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups

section Inverse

variable {K : Type} [Field K] {n : ℕ}

theorem mat_inv_eq_sp (g : StatedSp n K) :
    mat n K g⁻¹ = -(gram K n * (mat n K g)ᵀ * gram K n) := by
  have h1 : -(gram K n * (mat n K g)ᵀ * gram K n) * mat n K g = 1 := by
    calc -(gram K n * (mat n K g)ᵀ * gram K n) * mat n K g =
        -(gram K n * ((mat n K g)ᵀ * gram K n * mat n K g)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [mat_transpose_mul_gram_mul, gram_mul_gram, neg_neg]
  have h2 : mat n K g * mat n K g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc mat n K g⁻¹ = -(gram K n * (mat n K g)ᵀ * gram K n) * mat n K g * mat n K g⁻¹ := by
        rw [h1, Matrix.one_mul]
    _ = -(gram K n * (mat n K g)ᵀ * gram K n) := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem mat_inv_apply_sp (g : StatedSp n K) (r t : Fin n ⊕ Fin n) :
    mat n K g⁻¹ r t = -(sgn K r * mat n K g (par t) (par r) * sgn K (par t)) := by
  rw [mat_inv_eq_sp, Matrix.neg_apply, Matrix.mul_apply, Finset.sum_eq_single (par t)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (par r),
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, transpose_apply]
    · simp
    · intro a _ ha
      rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
        ite_eq_right_iff.mpr (fun h => absurd (by rw [h]) ha), zero_mul]
    · simp
  · intro b _ hb
    rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
      ite_eq_right_iff.mpr (fun h => absurd (by rw [h, par_par]) hb), mul_zero]
  · simp

end Inverse

section Commute

variable {K : Type} [Field K] {n : ℕ}

theorem blockMat_mulVec_inl (k : Fin n) (X : Matrix (Fin 2) (Fin 2) K)
    (v : Fin n ⊕ Fin n → K) :
    (blockMat (Sum.inl k) (Sum.inr k) X *ᵥ v) (Sum.inl k) =
      X 0 0 * v (Sum.inl k) + X 0 1 * v (Sum.inr k) := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  simp only [Matrix.mulVec, dotProduct, blockMat, Matrix.of_apply, ite_true]
  rw [Finset.sum_eq_add (Sum.inl k) (Sum.inr k) hpq]
  · simp [hpq.symm]
  · intro c _ hc
    simp [hc.1, hc.2]
  · simp
  · simp

theorem blockMat_mulVec_inr (k : Fin n) (X : Matrix (Fin 2) (Fin 2) K)
    (v : Fin n ⊕ Fin n → K) :
    (blockMat (Sum.inl k) (Sum.inr k) X *ᵥ v) (Sum.inr k) =
      X 1 0 * v (Sum.inl k) + X 1 1 * v (Sum.inr k) := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  simp only [Matrix.mulVec, dotProduct, blockMat, Matrix.of_apply, hpq.symm, ite_false,
    ite_true]
  rw [Finset.sum_eq_add (Sum.inl k) (Sum.inr k) hpq]
  · simp [hpq.symm]
  · intro c _ hc
    simp [hc.1, hc.2]
  · simp
  · simp

theorem eq_zero_of_fixed_longBlock {k : Fin n} {X : SL(2, K)}
    (hX : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0) {v : Fin n ⊕ Fin n → K}
    (hv : mat n K (longBlock K n k X) *ᵥ v = v) : v (Sum.inl k) = 0 ∧ v (Sum.inr k) = 0 := by
  have e1 := congrFun hv (Sum.inl k)
  have e2 := congrFun hv (Sum.inr k)
  rw [mat_longBlock, blockMat_mulVec_inl] at e1
  rw [mat_longBlock, blockMat_mulVec_inr] at e2
  set w : Fin 2 → K := ![v (Sum.inl k), v (Sum.inr k)] with hw
  have hw0 : ((X : Matrix (Fin 2) (Fin 2) K) - 1) *ᵥ w = 0 := by
    ext i
    fin_cases i
    · simp only [hw, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply]
      simp [Matrix.one_apply]
      linear_combination e1
    · simp only [hw, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply]
      simp [Matrix.one_apply]
      linear_combination e2
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hX))
  have h0 : w = 0 := hinj (by rw [hw0, Matrix.mulVec_zero])
  exact ⟨by simpa [hw] using congrFun h0 0, by simpa [hw] using congrFun h0 1⟩

theorem mat_apply_eq_zero_of_commute {k : Fin n} {X : SL(2, K)}
    (hX : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0) {g : StatedSp n K}
    (hc : g * longBlock K n k X = longBlock K n k X * g) {r c : Fin n ⊕ Fin n}
    (hr : r ∈ coords k) (hcn : c ∉ coords k) : mat n K g r c = 0 := by
  set v : Fin n ⊕ Fin n → K := Pi.single c 1 with hv
  have hfix : mat n K (longBlock K n k X) *ᵥ v = v :=
    mulVec_eq_self_of_isSupp (isSupp_longBlock k X) fun t ht => by
      rw [hv]
      exact Pi.single_eq_of_ne (fun h : t = c => hcn (h ▸ ht)) 1
  have hgv : mat n K (longBlock K n k X) *ᵥ (mat n K g *ᵥ v) = mat n K g *ᵥ v := by
    rw [mulVec_mulVec, ← map_mul, ← hc, map_mul, ← mulVec_mulVec, hfix]
  obtain ⟨h1, h2⟩ := eq_zero_of_fixed_longBlock hX hgv
  rcases mem_coords.1 hr with rfl | rfl
  · rwa [hv, mulVec_single_one_apply] at h1
  · rwa [hv, mulVec_single_one_apply] at h2

theorem mat_apply_eq_zero_of_commute' {k : Fin n} {X : SL(2, K)}
    (hX : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0) {g : StatedSp n K}
    (hc : g * longBlock K n k X = longBlock K n k X * g) {r c : Fin n ⊕ Fin n}
    (hr : r ∉ coords k) (hcm : c ∈ coords k) : mat n K g r c = 0 := by
  have hci : g⁻¹ * longBlock K n k X = longBlock K n k X * g⁻¹ :=
    (Commute.inv_left (show Commute g (longBlock K n k X) from hc)).eq
  have h := mat_apply_eq_zero_of_commute hX hci (parClosed_coords k _ hcm)
    (fun h => hr (by have h' := parClosed_coords k _ h; rwa [par_par] at h'))
  rw [mat_inv_apply_sp, par_par, par_par, neg_eq_zero, mul_eq_zero, mul_eq_zero] at h
  rcases h with (h | h) | h
  · exact absurd h (sgn_ne_zero _)
  · exact h
  · exact absurd h (sgn_ne_zero _)

theorem exists_longBlock_mul_of_col {k : Fin n} {g : StatedSp n K}
    (hcol : ∀ r, r ∉ coords k → ∀ c ∈ coords k, mat n K g r c = 0) :
    ∃ a : SL(2, K), (longBlock K n k a)⁻¹ * g ∈ suppGroup (coords k)ᶜ ∧
      (a : Matrix (Fin 2) (Fin 2) K) = stdBlock k (mat n K g) := by
  have hdet : (stdBlock k (mat n K g)).det = 1 :=
    det_stdBlock_eq_one g k fun c hc => hcol c hc _ (inl_mem_coords k)
  refine ⟨mkSL _ hdet, ?_, rfl⟩
  rw [mem_suppGroup_iff (parClosed_coords k).compl]
  intro t ht r
  have htk : t ∈ coords k := not_not.mp ht
  have hcolEq : mat n K (longBlock K n k (mkSL _ hdet)) *ᵥ Pi.single t 1 =
      mat n K g *ᵥ Pi.single t 1 := by
    ext r'
    rw [mulVec_single_one_apply, mulVec_single_one_apply, mat_longBlock, coe_mkSL]
    by_cases hr' : r' ∈ coords k
    · rcases mem_coords.1 hr' with rfl | rfl <;> rcases mem_coords.1 htk with rfl | rfl <;>
        simp [blockMat, stdBlock]
    · rw [hcol r' hr' t htk, blockMat_apply_of_not_mem k _ (fun h => hr' h.1),
        Matrix.one_apply_ne (fun h : r' = t => hr' (h ▸ htk))]
  have h1 : mat n K ((longBlock K n k (mkSL _ hdet))⁻¹ * g) *ᵥ Pi.single t 1 = Pi.single t 1 := by
    rw [map_mul, ← mulVec_mulVec, ← hcolEq, mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one,
      one_mulVec]
  have h2 := congrFun h1 r
  rwa [mulVec_single_one_apply, Pi.single_apply, ← Matrix.one_apply] at h2

end Commute

section Four

variable {K : Type} [Field K]

theorem coords_zero_compl : (coords (0 : Fin (1 + 1)))ᶜ = coords 1 := by
  ext a
  rcases a with i | i <;> fin_cases i <;> simp [coords]

theorem coords_one_compl : (coords (1 : Fin (1 + 1)))ᶜ = coords 0 := by
  rw [← compl_compl (coords (0 : Fin (1 + 1))), coords_zero_compl]

theorem exists_longBlock_mul_longBlock {X : SL(2, K)}
    (hX : ((X : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0) {g : StatedSp (1 + 1) K}
    (hc : g * longBlock K (1 + 1) 0 X = longBlock K (1 + 1) 0 X * g) :
    ∃ a b : SL(2, K), g = longBlock K (1 + 1) 0 a * longBlock K (1 + 1) 1 b ∧ a * X = X * a := by
  obtain ⟨a, ha, -⟩ := exists_longBlock_mul_of_col (k := 0) fun r hr c hc' =>
    mat_apply_eq_zero_of_commute' hX hc hr hc'
  rw [coords_zero_compl, ← range_longBlock] at ha
  obtain ⟨b, hb⟩ := ha
  have hg : g = longBlock K (1 + 1) 0 a * longBlock K (1 + 1) 1 b := by
    rw [hb, mul_inv_cancel_left]
  refine ⟨a, b, hg, ?_⟩
  have hcomm : ∀ Y Z : SL(2, K),
      longBlock K (1 + 1) 1 Y * longBlock K (1 + 1) 0 Z =
        longBlock K (1 + 1) 0 Z * longBlock K (1 + 1) 1 Y := fun Y Z =>
    commute_longRootSp2 (by decide) ⟨Y, rfl⟩ ⟨Z, rfl⟩
  have e1 : longBlock K (1 + 1) 0 a * longBlock K (1 + 1) 1 b * longBlock K (1 + 1) 0 X =
      longBlock K (1 + 1) 0 (a * X) * longBlock K (1 + 1) 1 b := by
    rw [mul_assoc, hcomm, ← mul_assoc, ← map_mul]
  have e2 : longBlock K (1 + 1) 0 X * (longBlock K (1 + 1) 0 a * longBlock K (1 + 1) 1 b) =
      longBlock K (1 + 1) 0 (X * a) * longBlock K (1 + 1) 1 b := by
    rw [← mul_assoc, ← map_mul]
  rw [hg, e1, e2] at hc
  exact longBlock_injective _ (mul_right_cancel hc)

theorem mem_suppGroup_iff_fix {n : ℕ} {S : Set (Fin n ⊕ Fin n)} (hS : ParClosed S)
    {x : StatedSp n K} :
    x ∈ suppGroup S ↔ ∀ t ∉ S, mat n K x *ᵥ Pi.single t 1 = Pi.single t 1 := by
  rw [mem_suppGroup_iff hS]
  refine forall₂_congr fun t _ => ?_
  constructor
  · intro h
    ext r
    rw [mulVec_single_one_apply, h r, Matrix.one_apply, Pi.single_apply]
  · intro h r
    have := congrFun h r
    rwa [mulVec_single_one_apply, Pi.single_apply, ← Matrix.one_apply] at this

@[expose] def swapCoord : Fin (1 + 1) ⊕ Fin (1 + 1) → Fin (1 + 1) ⊕ Fin (1 + 1) :=
  Sum.map (Equiv.swap 0 1) (Equiv.swap 0 1)

theorem swapCoord_swapCoord (t : Fin (1 + 1) ⊕ Fin (1 + 1)) : swapCoord (swapCoord t) = t := by
  rcases t with i | i <;> simp [swapCoord]

theorem swapCoord_mem_coords_iff (k : Fin (1 + 1)) (t : Fin (1 + 1) ⊕ Fin (1 + 1)) :
    swapCoord t ∈ coords (Equiv.swap 0 1 k) ↔ t ∈ coords k := by
  rcases t with i | i <;> simp [swapCoord, mem_coords]

theorem exists_spSwap : ∃ s : StatedSp (1 + 1) K, (∀ t, mat _ K s *ᵥ Pi.single t 1 =
    Pi.single (swapCoord t) 1) ∧ s * s = 1 := by
  obtain ⟨s, h1, h2, h3, h4⟩ := exists_sp_apply_eq_two (m := 0) (K := K)
    (Pi.single (Sum.inl 1) 1) (Pi.single (Sum.inr 1) 1) (Pi.single (Sum.inl 0) 1)
    (Pi.single (Sum.inr 0) 1) (by rw [form_single_right]; simp)
    (by rw [form_single_right]; simp) (by rw [form_single_right]; simp)
    (by rw [form_single_right]; simp) (by rw [form_single_right]; simp)
    (by rw [form_single_right]; simp)
  have hs : ∀ t, mat _ K s *ᵥ Pi.single t 1 = Pi.single (swapCoord t) 1 := by
    intro t
    rcases t with i | i <;> fin_cases i
    · exact h1
    · exact h3
    · exact h2
    · exact h4
  refine ⟨s, hs, mat_injective ?_⟩
  rw [map_mul, map_one]
  ext r t
  have := congrFun
    (show mat _ K s *ᵥ (mat _ K s *ᵥ Pi.single t 1) = Pi.single t 1 by
      rw [hs, hs, swapCoord_swapCoord]) r
  rwa [mulVec_mulVec, mulVec_single_one_apply, Pi.single_apply, ← Matrix.one_apply] at this

theorem conj_mem_suppGroup_coords_iff {s : StatedSp (1 + 1) K}
    (hs : ∀ t, mat _ K s *ᵥ Pi.single t 1 = Pi.single (swapCoord t) 1) (k : Fin (1 + 1))
    (x : StatedSp (1 + 1) K) :
    s * x * s⁻¹ ∈ suppGroup (coords (Equiv.swap 0 1 k)) ↔ x ∈ suppGroup (coords k) := by
  rw [mem_suppGroup_iff_fix (parClosed_coords _), mem_suppGroup_iff_fix (parClosed_coords _)]
  have hsi : ∀ t, mat _ K s⁻¹ *ᵥ Pi.single (swapCoord t) 1 = Pi.single t 1 := fun t =>
    ((mulVec_eq_iff s _ _).1 (hs t)).symm
  constructor
  · intro h t ht
    have h1 := h (swapCoord t) (by rwa [swapCoord_mem_coords_iff])
    rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hsi] at h1
    apply mulVec_inj s
    rw [h1, hs]
  · intro h t ht
    have ht' : swapCoord t ∉ coords k := fun h' =>
      ht ((swapCoord_mem_coords_iff (Equiv.swap 0 1 k) t).mp (by rwa [Equiv.swap_apply_self]))
    rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, ← swapCoord_swapCoord t, hsi,
      h _ ht', hs]

end Four

end CFSG.ComponentClassification.RankTwoClassical
