module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagTriangular

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply elt mat_elt E)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent upperUnipotentSp
  coe_upperUnipotentSp blockMat IsUnitriangular)

variable {K : Type} [Field K] {m : ℕ}

section Siegel

theorem fromBlocks_one_eq_blockMat (C : Matrix (Fin m) (Fin m) K) :
    fromBlocks 1 C 0 1 = blockMat 1 C := by
  simp [blockMat]

theorem mat_upperUnipotentSp {C : Matrix (Fin m) (Fin m) K} (hC : Cᵀ = C) :
    mat m K (upperUnipotentSp m K hC) = fromBlocks 1 C 0 1 :=
  coe_upperUnipotentSp hC

theorem upperUnipotentSp_mem_unipotent {C : Matrix (Fin m) (Fin m) K} (hC : Cᵀ = C) :
    upperUnipotentSp m K hC ∈ unipotent m K :=
  ⟨1, C, SymplecticFlag.isUnitriangular_one, hC, by
    rw [coe_upperUnipotentSp, fromBlocks_one_eq_blockMat]⟩

theorem upperUnipotentSp_mul {C C' : Matrix (Fin m) (Fin m) K} (hC : Cᵀ = C) (hC' : C'ᵀ = C') :
    upperUnipotentSp m K hC * upperUnipotentSp m K hC' =
      upperUnipotentSp m K (C := C + C') (by rw [transpose_add, hC, hC']) := by
  apply mat_injective
  rw [map_mul, mat_upperUnipotentSp, mat_upperUnipotentSp, mat_upperUnipotentSp,
    fromBlocks_multiply]
  simp [add_comm]

theorem upperUnipotentSp_zero :
    upperUnipotentSp m K (C := (0 : Matrix (Fin m) (Fin m) K)) (transpose_zero) = 1 := by
  apply mat_injective
  rw [mat_upperUnipotentSp, map_one, fromBlocks_one]

theorem elt_positiveLong_eq_upperUnipotentSp (i : Fin m) (c : K) :
    elt (.positiveLong i) c =
      upperUnipotentSp m K (C := single i i c) (transpose_single i i c) := by
  apply mat_injective
  rw [mat_elt, mat_upperUnipotentSp]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [E, Matrix.single_apply, Matrix.one_apply]

theorem elt_positiveSum_eq_upperUnipotentSp {i j : Fin m} (hij : i < j) (c : K) :
    elt (.positiveSum i j hij) c =
      upperUnipotentSp m K (C := single i j c + single j i c)
        (by rw [transpose_add, transpose_single, transpose_single, add_comm]) := by
  apply mat_injective
  rw [mat_elt, mat_upperUnipotentSp]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [E, Matrix.single_apply, Matrix.one_apply]

theorem elt_positiveLong_mem_unipotent (i : Fin m) (c : K) :
    elt (.positiveLong i) c ∈ unipotent m K := by
  rw [elt_positiveLong_eq_upperUnipotentSp]
  exact upperUnipotentSp_mem_unipotent _

end Siegel

section TwoCentral

@[expose] def twoCentralMat (i j : Fin m) (a b : K) : Matrix (Fin m) (Fin m) K :=
  single i i a + single i j b + single j i b

theorem twoCentralMat_apply (i j : Fin m) (a b : K) (x y : Fin m) :
    twoCentralMat i j a b x y =
      (if i = x ∧ i = y then a else 0) + (if i = x ∧ j = y then b else 0) +
        (if j = x ∧ i = y then b else 0) := by
  simp only [twoCentralMat, Matrix.add_apply, Matrix.single_apply]

theorem twoCentralMat_transpose (i j : Fin m) (a b : K) :
    (twoCentralMat i j a b)ᵀ = twoCentralMat i j a b := by
  simp only [twoCentralMat, transpose_add, transpose_single]
  abel

theorem twoCentralMat_add (i j : Fin m) (a b a' b' : K) :
    twoCentralMat i j a b + twoCentralMat i j a' b' = twoCentralMat i j (a + a') (b + b') := by
  simp only [twoCentralMat, single_add]
  abel

variable (m) in
@[expose] noncomputable def twoCentralElt (i j : Fin m) (a b : K) : StatedSp m K :=
  upperUnipotentSp m K (twoCentralMat_transpose i j a b)

theorem mat_twoCentralElt (i j : Fin m) (a b : K) :
    mat m K (twoCentralElt m i j a b) = fromBlocks 1 (twoCentralMat i j a b) 0 1 :=
  mat_upperUnipotentSp _

theorem twoCentralElt_mul (i j : Fin m) (a b a' b' : K) :
    twoCentralElt m i j a b * twoCentralElt m i j a' b' =
      twoCentralElt m i j (a + a') (b + b') := by
  apply mat_injective
  rw [map_mul, mat_twoCentralElt, mat_twoCentralElt, mat_twoCentralElt, fromBlocks_multiply,
    ← twoCentralMat_add]
  simp [add_comm]

theorem twoCentralElt_zero (i j : Fin m) : twoCentralElt m i j (0 : K) 0 = 1 := by
  apply mat_injective
  rw [mat_twoCentralElt, map_one]
  simp [twoCentralMat, fromBlocks_one]

theorem twoCentralElt_mem_unipotent (i j : Fin m) (a b : K) :
    twoCentralElt m i j a b ∈ unipotent m K :=
  upperUnipotentSp_mem_unipotent _

theorem twoCentralElt_eq_elt_mul_elt {i j : Fin m} (hij : i < j) (a b : K) :
    twoCentralElt m i j a b = elt (.positiveLong i) a * elt (.positiveSum i j hij) b := by
  rw [elt_positiveLong_eq_upperUnipotentSp, elt_positiveSum_eq_upperUnipotentSp,
    upperUnipotentSp_mul]
  apply mat_injective
  rw [mat_twoCentralElt, mat_upperUnipotentSp, twoCentralMat, add_assoc]

theorem twoCentralElt_eq_one_iff {i j : Fin m} (hij : i ≠ j) {a b : K} :
    twoCentralElt m i j a b = 1 ↔ a = 0 ∧ b = 0 := by
  refine ⟨fun h => ?_, fun ⟨ha, hb⟩ => by rw [ha, hb, twoCentralElt_zero]⟩
  have h1 := congrArg (mat m K) h
  rw [mat_twoCentralElt, map_one] at h1
  have ha := congrFun (congrFun h1 (Sum.inl i)) (Sum.inr i)
  have hb := congrFun (congrFun h1 (Sum.inl i)) (Sum.inr j)
  simp only [fromBlocks_apply₁₂, twoCentralMat_apply] at ha hb
  simp [hij, Ne.symm hij] at ha hb
  exact ⟨ha, hb⟩

end TwoCentral

@[expose] noncomputable def spHighRootCenter (m : ℕ) (K : Type) [Field K] :
    Subgroup (StatedSp (m + 2) K) where
  carrier := {g | ∃ a b : K, twoCentralElt (m + 2) 0 1 a b = g}
  one_mem' := ⟨0, 0, twoCentralElt_zero 0 1⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    exact ⟨a + a', b + b', (twoCentralElt_mul 0 1 a b a' b').symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    rw [eq_inv_iff_mul_eq_one, twoCentralElt_mul, neg_add_cancel, neg_add_cancel,
      twoCentralElt_zero]

section Center

theorem mul_single_mul_transpose_apply (B : Matrix (Fin m) (Fin m) K) (u v : Fin m) (c : K)
    (x y : Fin m) : (B * single u v c * Bᵀ) x y = B x u * c * B y v := by
  rw [Matrix.mul_apply, Finset.sum_eq_single v]
  · rw [Matrix.mul_single_apply_same, Matrix.transpose_apply]
  · intro w _ hw
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hw, zero_mul]
  · simp

theorem fin_zero_ne_one : (0 : Fin (m + 2)) ≠ 1 := by
  simp

theorem fin_zero_lt_of_ne {x : Fin (m + 2)} (hx : x ≠ 0) : (0 : Fin (m + 2)) < x := by
  rw [Fin.lt_def, Fin.val_zero]
  rw [Ne, Fin.ext_iff, Fin.val_zero] at hx
  omega

theorem fin_one_lt_of_ne {x : Fin (m + 2)} (hx0 : x ≠ 0) (hx1 : x ≠ 1) : (1 : Fin (m + 2)) < x := by
  rw [Fin.lt_def, Fin.val_one]
  rw [Ne, Fin.ext_iff, Fin.val_zero] at hx0
  rw [Ne, Fin.ext_iff, Fin.val_one] at hx1
  omega

variable [CharP K 2]

theorem unitriangular_mul_twoCentralMat_mul_transpose {B : Matrix (Fin (m + 2)) (Fin (m + 2)) K}
    (hB : IsUnitriangular B) (a b : K) :
    B * twoCentralMat 0 1 a b * Bᵀ = twoCentralMat 0 1 a b := by
  have h0 : ∀ x, B x 0 = if x = 0 then 1 else 0 := by
    intro x
    split_ifs with hx
    · rw [hx, hB.2]
    · exact hB.1 (fin_zero_lt_of_ne hx)
  have h1 : ∀ x, x ≠ 0 → B x 1 = if x = 1 then 1 else 0 := by
    intro x hx0
    split_ifs with hx
    · rw [hx, hB.2]
    · exact hB.1 (fin_one_lt_of_ne hx0 hx)
  have h01 := fin_zero_ne_one (m := m)
  ext x y
  simp only [twoCentralMat, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply,
    mul_single_mul_transpose_apply, Matrix.single_apply, h0]
  by_cases hx0 : x = 0
  · subst hx0
    by_cases hy0 : y = 0
    · subst hy0
      have hc : b * B 0 1 + B 0 1 * b = 0 := by
        rw [mul_comm (B 0 1) b]
        exact CharTwo.add_self_eq_zero _
      simp [Ne.symm h01]
      linear_combination hc
    · rw [h1 y hy0]
      by_cases hy1 : y = 1
      · subst hy1
        simp [h01, Ne.symm h01]
      · simp [hy0, hy1, Ne.symm hy0, Ne.symm hy1]
  · by_cases hy0 : y = 0
    · subst hy0
      rw [h1 x hx0]
      by_cases hx1 : x = 1
      · subst hx1
        simp [h01, Ne.symm h01]
      · simp [hx0, hx1, Ne.symm hx0, Ne.symm hx1]
    · simp [hx0, hy0, Ne.symm hx0, Ne.symm hy0]

omit [CharP K 2] in
theorem mem_spHighRootCenter {g : StatedSp (m + 2) K} :
    g ∈ spHighRootCenter m K ↔ ∃ a b : K, twoCentralElt (m + 2) 0 1 a b = g := Iff.rfl

theorem spHighRootCenter_le_centralizer_unipotent :
    spHighRootCenter m K ≤ centralizer (unipotent (m + 2) K : Set (StatedSp (m + 2) K)) := by
  rintro _ ⟨a, b, rfl⟩
  rw [mem_centralizer_iff]
  rintro g ⟨A, C, hA, hC, hg⟩
  apply mat_injective
  rw [map_mul, map_mul, mat_twoCentralElt, mat_apply g, hg, fromBlocks_one_eq_blockMat,
    SymplecticFlag.blockMat_mul (by rw [det_one]; exact isUnit_one),
    SymplecticFlag.blockMat_mul hA.isUnit_det, unitriangular_mul_twoCentralMat_mul_transpose hA.inv]
  simp [add_comm]

theorem eq_one_of_mul_self_eq_one_of_charTwo {x : K} (h : x * x = 1) : x = 1 := by
  have h2 : (x + 1) * (x + 1) = 0 := by
    have e : (x + 1) * (x + 1) = x * x + 1 + 2 * x := by ring
    rw [e, h, CharTwo.two_eq_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero]
  have h3 : x + 1 = 0 := mul_self_eq_zero.1 h2
  calc x = x + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h3, zero_add]

omit [CharP K 2] in
theorem isUnitriangular_one_add_single {i j : Fin m} (hij : i < j) :
    IsUnitriangular (1 + single i j (1 : K)) := by
  refine ⟨fun x z hzx => ?_, fun x => ?_⟩
  · have hxz : x ≠ z := fun h => by subst h; exact lt_irrefl _ hzx
    rw [Matrix.add_apply, Matrix.one_apply_ne hxz, zero_add, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact absurd hzx (not_lt.2 hij.le)
    · rfl
  · simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply]
    split_ifs with h
    · exact absurd (h.1.trans h.2.symm) (ne_of_lt hij)
    · rw [add_zero]

theorem centralizer_unipotent_le :
    centralizer (unipotent (m + 2) K : Set (StatedSp (m + 2) K)) ≤ spHighRootCenter m K := by
  intro g hg
  rw [mem_centralizer_iff] at hg
  set G := mat (m + 2) K g with hG
  have hcomm : ∀ i : Fin (m + 2), Commute (single (Sum.inl i) (Sum.inr i) (1 : K)) G := by
    intro i
    have h := congrArg (mat (m + 2) K) (hg _ (elt_positiveLong_mem_unipotent i (1 : K)))
    rw [map_mul, map_mul, mat_elt, one_smul] at h
    simp only [E, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      add_right_inj] at h
    exact h
  have hcol : ∀ i x, x ≠ Sum.inl i → G x (Sum.inl i) = 0 := fun i x hx =>
    col_eq_zero_of_commute_single (hcomm i) hx
  have hrow : ∀ i y, y ≠ Sum.inr i → G (Sum.inr i) y = 0 := fun i y hy =>
    row_eq_zero_of_commute_single (hcomm i) hy
  have hdiag : ∀ i, G (Sum.inl i) (Sum.inl i) = G (Sum.inr i) (Sum.inr i) := fun i =>
    diag_eq_of_commute_single (hcomm i)
  have h21 : G.toBlocks₂₁ = 0 := by
    ext x y
    exact hcol y (Sum.inr x) Sum.inr_ne_inl
  have hsp : Gᵀ * fromBlocks 0 1 (-1) 0 * G = fromBlocks 0 1 (-1) 0 :=
    SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  have hGb : G = fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ 0 G.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks G]
    rw [h21]
  rw [hGb] at hsp
  obtain ⟨hAD, hED⟩ := SymplecticFlag.fromBlocks_symplectic_of_lower_zero hsp
  have hlam : ∀ i, G (Sum.inl i) (Sum.inl i) = 1 := by
    intro i
    have h := congrFun (congrFun hAD i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.one_apply_eq] at h
    · simp only [Matrix.transpose_apply, toBlocks₁₁, toBlocks₂₂, of_apply] at h
      rw [← hdiag] at h
      exact eq_one_of_mul_self_eq_one_of_charTwo h
    · intro k _ hk
      simp only [Matrix.transpose_apply, toBlocks₁₁, of_apply]
      rw [hcol i (Sum.inl k) (fun e => hk (Sum.inl_injective e)), zero_mul]
    · simp
  have h11 : G.toBlocks₁₁ = 1 := by
    ext x y
    simp only [toBlocks₁₁, of_apply]
    by_cases hxy : x = y
    · subst hxy
      rw [hlam, Matrix.one_apply_eq]
    · rw [hcol y (Sum.inl x) (fun e => hxy (Sum.inl_injective e)), Matrix.one_apply_ne hxy]
  have h22 : G.toBlocks₂₂ = 1 := by
    ext x y
    simp only [toBlocks₂₂, of_apply]
    by_cases hxy : x = y
    · subst hxy
      rw [← hdiag, hlam, Matrix.one_apply_eq]
    · rw [hrow x (Sum.inr y) (fun e => hxy (Sum.inr_injective e).symm), Matrix.one_apply_ne hxy]
  set Q := G.toBlocks₁₂ with hQ
  have hQs : Qᵀ = Q := by
    rw [h22, Matrix.mul_one, transpose_one, Matrix.one_mul] at hED
    exact hED
  have hGQ : G = fromBlocks 1 Q 0 1 := by
    rw [hGb, h11, h22]
  have hzero : ∀ i j : Fin (m + 2), i < j → ∀ y, y ≠ i → Q j y = 0 := by
    intro i j hij y hy
    have hA := isUnitriangular_one_add_single (K := K) hij
    set A := 1 + single i j (1 : K) with hAdef
    obtain ⟨V, hV, hVmat⟩ := SymplecticFlag.exists_mem_unipotent hA (C := 0) transpose_zero
    have h := congrArg (mat (m + 2) K) (hg V hV)
    rw [map_mul, map_mul, mat_apply V, hVmat, ← hG, hGQ, fromBlocks_one_eq_blockMat,
      SymplecticFlag.blockMat_mul (by rw [det_one]; exact isUnit_one),
      SymplecticFlag.blockMat_mul hA.isUnit_det] at h
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, zero_add,
      add_zero] at h
    obtain ⟨-, hQA⟩ := SymplecticFlag.blockMat_inj hA.isUnit_det h
    have hAQ : A * Q * Aᵀ = Q := by
      calc A * Q * Aᵀ = A * (A⁻¹ * Q * A⁻¹ᵀ) * Aᵀ := by rw [← hQA]
        _ = (A * A⁻¹) * Q * (A * A⁻¹)ᵀ := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
        _ = Q := by
          rw [Matrix.mul_nonsing_inv _ hA.isUnit_det, transpose_one, Matrix.one_mul,
            Matrix.mul_one]
    have h2 := congrFun (congrFun hAQ i) y
    simp only [hAdef, transpose_add, transpose_one, transpose_single, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.add_apply,
      Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne _ _ _ _ _ hy] at h2
    linear_combination h2
  have h01 := fin_zero_ne_one (m := m)
  have hQ1 : ∀ y, y ≠ 0 → Q 1 y = 0 := fun y hy =>
    hzero 0 1 (fin_zero_lt_of_ne (Ne.symm h01)) y hy
  have hQx : ∀ x, x ≠ 0 → x ≠ 1 → ∀ y, Q x y = 0 := by
    intro x hx0 hx1 y
    by_cases hy : y = 0
    · subst hy
      exact hzero 1 x (fin_one_lt_of_ne hx0 hx1) 0 h01
    · exact hzero 0 x (fin_zero_lt_of_ne hx0) y hy
  have hsymm : ∀ x y, Q x y = Q y x := fun x y =>
    (congrFun (congrFun hQs.symm x) y).trans (transpose_apply Q x y)
  have hQeq : Q = twoCentralMat 0 1 (Q 0 0) (Q 0 1) := by
    ext x y
    rw [twoCentralMat_apply]
    by_cases hx0 : x = 0
    · subst hx0
      by_cases hy0 : y = 0
      · subst hy0
        simp [Ne.symm h01]
      · by_cases hy1 : y = 1
        · subst hy1
          simp [h01, Ne.symm h01]
        · rw [hsymm, hQx y hy0 hy1 0]
          simp [Ne.symm hy0, Ne.symm hy1]
    · by_cases hx1 : x = 1
      · subst hx1
        by_cases hy0 : y = 0
        · subst hy0
          rw [hsymm]
          simp [h01, Ne.symm h01]
        · rw [hQ1 y hy0]
          simp [Ne.symm hy0]
      · rw [hQx x hx0 hx1 y]
        simp [Ne.symm hx0, Ne.symm hx1]
  refine ⟨Q 0 0, Q 0 1, mat_injective ?_⟩
  rw [mat_twoCentralElt, ← hQeq, ← hGQ]

theorem centralizer_unipotent :
    centralizer (unipotent (m + 2) K : Set (StatedSp (m + 2) K)) = spHighRootCenter m K :=
  le_antisymm centralizer_unipotent_le spHighRootCenter_le_centralizer_unipotent

omit [CharP K 2] in
theorem spHighRootCenter_le_unipotent : spHighRootCenter m K ≤ unipotent (m + 2) K := by
  rintro _ ⟨a, b, rfl⟩
  exact twoCentralElt_mem_unipotent 0 1 a b

theorem map_center_unipotent :
    (center (unipotent (m + 2) K)).map (unipotent (m + 2) K).subtype = spHighRootCenter m K := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    rw [← centralizer_unipotent, mem_centralizer_iff]
    intro u hu
    exact congrArg Subtype.val (mem_center_iff.1 hz ⟨u, hu⟩)
  · intro z hz
    refine ⟨⟨z, spHighRootCenter_le_unipotent hz⟩, mem_center_iff.2 fun u => ?_, rfl⟩
    rw [← centralizer_unipotent, mem_centralizer_iff] at hz
    exact Subtype.ext (hz u u.2)

end Center

section Conj

theorem diag_mul_twoCentralMat_mul_diag_apply (d : Fin m → K) (i j : Fin m) (a b : K)
    (x y : Fin m) :
    d x * twoCentralMat i j a b x y * d y =
      twoCentralMat i j (d i * d i * a) (d i * d j * b) x y := by
  rw [twoCentralMat_apply, twoCentralMat_apply]
  have e1 : d x * (if i = x ∧ i = y then a else 0) * d y =
      if i = x ∧ i = y then d i * d i * a else 0 := by
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      ring
    · simp
  have e2 : d x * (if i = x ∧ j = y then b else 0) * d y =
      if i = x ∧ j = y then d i * d j * b else 0 := by
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      ring
    · simp
  have e3 : d x * (if j = x ∧ i = y then b else 0) * d y =
      if j = x ∧ i = y then d i * d j * b else 0 := by
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      ring
    · simp
  rw [mul_add, mul_add, add_mul, add_mul, e1, e2, e3]

theorem conj_diagSp_twoCentralElt (t : Fin m → Kˣ) (i j : Fin m) (a b : K) :
    diagSp K m t * twoCentralElt m i j a b * (diagSp K m t)⁻¹ =
      twoCentralElt m i j ((t i : K) * t i * a) ((t i : K) * t j * b) := by
  apply mat_injective
  rw [map_mul, map_mul, ← map_inv, mat_diagSp, mat_diagSp, mat_twoCentralElt, mat_twoCentralElt]
  ext x y
  rw [mul_diagonal, diagonal_mul]
  rcases x with x | x <;> rcases y with y | y
  · simp only [fromBlocks_apply₁₁, diagSpEntry_inl, Matrix.one_apply]
    split_ifs with h
    · subst h
      simp
    · simp
  · simp only [fromBlocks_apply₁₂, diagSpEntry_inl, diagSpEntry_inr, Pi.inv_apply, inv_inv]
    exact diag_mul_twoCentralMat_mul_diag_apply (fun k => (t k : K)) i j a b x y
  · simp
  · simp only [fromBlocks_apply₂₂, diagSpEntry_inr, Matrix.one_apply, Pi.inv_apply, inv_inv]
    split_ifs with h
    · subst h
      simp
    · simp

theorem conj_permSp_twoCentralElt (π : Equiv.Perm (Fin m)) (i j : Fin m) (a b : K) :
    permSp K π * twoCentralElt m i j a b * (permSp K π)⁻¹ = twoCentralElt m (π i) (π j) a b := by
  apply mat_injective
  ext p q
  obtain ⟨x, rfl⟩ := (sumMap_bijective π).surjective p
  obtain ⟨y, rfl⟩ := (sumMap_bijective π).surjective q
  rw [mat_conj_permSp_apply, mat_twoCentralElt, mat_twoCentralElt]
  rcases x with x | x <;> rcases y with y | y
  · simp only [Sum.map_inl, fromBlocks_apply₁₁, Matrix.one_apply, π.injective.eq_iff]
  · simp only [Sum.map_inl, Sum.map_inr, fromBlocks_apply₁₂, twoCentralMat_apply,
      π.injective.eq_iff]
  · simp only [Sum.map_inl, Sum.map_inr, fromBlocks_apply₂₁, Matrix.zero_apply]
  · simp only [Sum.map_inr, fromBlocks_apply₂₂, Matrix.one_apply, π.injective.eq_iff]

end Conj

inductive SpTwoCentral
  | b1
  | a2
  | c2

@[expose] def SpTwoCentral.params (K : Type) [Field K] : SpTwoCentral → K × K
  | .b1 => (1, 0)
  | .a2 => (0, 1)
  | .c2 => (1, 1)

variable (m) in
@[expose] noncomputable def twoCentralRep (i j : Fin m) (κ : SpTwoCentral) : StatedSp m K :=
  twoCentralElt m i j (κ.params K).1 (κ.params K).2

theorem twoCentralRep_eq_elt {i j : Fin m} (hij : i < j) :
    twoCentralRep (K := K) m i j .b1 = elt (.positiveLong i) 1 ∧
      twoCentralRep (K := K) m i j .a2 = elt (.positiveSum i j hij) 1 ∧
      twoCentralRep (K := K) m i j .c2 =
        elt (.positiveLong i) 1 * elt (.positiveSum i j hij) 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [twoCentralRep, twoCentralElt_eq_elt_mul_elt hij] <;>
    simp [SpTwoCentral.params, CFSG.LieType.Universal.Symplectic.SpExtras.elt_zero]

theorem SpTwoCentral.params_ne (κ : SpTwoCentral) :
    ¬((κ.params K).1 = 0 ∧ (κ.params K).2 = 0) := by
  cases κ <;> simp [SpTwoCentral.params]

variable (n : ℕ) in
@[expose] noncomputable def spRep (κ : SpTwoCentral) : StatedSp (n + 3) K :=
  twoCentralRep (n + 3) 1 2 κ

theorem spRep_mem_complSp (n : ℕ) (κ : SpTwoCentral) : spRep (K := K) n κ ∈ complSp K 0 := by
  rw [mem_complSp]
  intro p q hpq
  rw [spRep, twoCentralRep, mat_twoCentralElt]
  have h10 : (1 : Fin (n + 3)) ≠ 0 := by simp
  have h20 : (2 : Fin (n + 3)) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_two, Fin.val_zero] at h'
    omega
  rcases p with x | x <;> rcases q with y | y
  · rw [fromBlocks_apply₁₁]
    simp [Matrix.one_apply]
  · have hxy : x = 0 ∨ y = 0 := by
      by_contra h
      push Not at h
      exact hpq ⟨by simp [coords, h.1], by simp [coords, h.2]⟩
    rw [fromBlocks_apply₁₂, twoCentralMat_apply, Matrix.one_apply_ne Sum.inl_ne_inr]
    rcases hxy with rfl | rfl <;> simp [h10, h20]
  · rw [fromBlocks_apply₂₁]
    simp
  · rw [fromBlocks_apply₂₂]
    simp [Matrix.one_apply]

end CFSG.SeitzReduction.SymplecticPilot
