module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelLagStd

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LieType.BorelTits (spJ transpose_mul_mul_of_mem_statedSp)
open scoped MatrixGroups

variable {m : ℕ} {F : Type} [Field F]

section Transvection

variable (F) in
@[expose] noncomputable def lagLowerTv (p : Fin m) : StatedSp m F :=
  ⟨(CFSG.ClassicalGroups.Symplectic.lowerUnipotent (C := single p p (1 : F))
      (transpose_single p p 1) : GL (Fin m ⊕ Fin m) F), by
    rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact (CFSG.ClassicalGroups.Symplectic.lowerUnipotent _).2⟩

theorem mat_lagLowerTv (p : Fin m) :
    mat m F (lagLowerTv F p) = 1 + single (Sum.inr p) (Sum.inl p) 1 := by
  rw [mat_apply, lagLowerTv]
  simp only [CFSG.ClassicalGroups.Symplectic.coe_lowerUnipotent]
  ext r t
  rcases r with x | x <;> rcases t with y | y <;>
    simp [Matrix.one_apply, Matrix.single_apply, and_comm]

variable (F) in
@[expose] noncomputable def lagTv : Fin m ⊕ Fin m → StatedSp m F
  | .inl p => siegDiag F p 1
  | .inr p => lagLowerTv F p

theorem mat_lagTv (a : Fin m ⊕ Fin m) :
    mat m F (lagTv F a) = 1 + single a a.swap 1 := by
  rcases a with p | p
  · exact mat_siegDiag_one p
  · exact mat_lagLowerTv p

theorem mat_lagTv_mulVec (a : Fin m ⊕ Fin m) (v : Fin m ⊕ Fin m → F) :
    mat m F (lagTv F a) *ᵥ v = v + v a.swap • Pi.single a 1 := by
  rw [mat_lagTv, add_mulVec, one_mulVec]
  congr 1
  ext x
  simp only [mulVec, dotProduct, Matrix.single_apply, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul]
  by_cases hx : x = a
  · subst hx
    simp
  · simp [hx, Ne.symm hx]

theorem mat_lagTv_row_self (a : Fin m ⊕ Fin m) :
    (fun p => mat m F (lagTv F a) a p) = Pi.single a 1 + Pi.single a.swap 1 := by
  funext p
  rw [mat_lagTv, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Pi.add_apply,
    Pi.single_apply, Pi.single_apply]
  by_cases h1 : p = a
  · subst h1
    have : p.swap ≠ p := by rcases p with p | p <;> simp
    simp [this, Ne.symm this]
  · by_cases h2 : p = a.swap
    · subst h2
      simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem mat_lagTv_row_of_ne {a x : Fin m ⊕ Fin m} (hx : x ≠ a) :
    (fun p => mat m F (lagTv F a) x p) = Pi.single x 1 := by
  funext p
  rw [mat_lagTv, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Pi.single_apply]
  by_cases h1 : p = x
  · subst h1
    simp [Ne.symm hx]
  · simp [h1, Ne.symm h1, Ne.symm hx]

end Transvection

section Generation

theorem lagRad_smul_lagEl_mem_two [CharP F 2] {a b : Fin m ⊕ Fin m} (hab : b ≠ a)
    (hb : b ≠ a.swap) (c : F) :
    lagRad m F (Multiplicative.ofAdd (c • (lagEl a b : Matrix _ _ F))) ∈
      ⁅lagR0Grp m F, lagX m F⁆ := by
  have hC : c • (lagEl a.swap b : Matrix _ _ F) ∈ lagR0 m F :=
    ⟨Submodule.smul_mem _ _ (lagE_mem_lagAlt _ _), by
      show lagOmegaStar m F _ = 0
      rw [map_smul, lagOmegaStar_lagEl_of_ne_swap (by rwa [Sum.swap_swap]), smul_zero]⟩
  have key := lagRad_sub_conj_mem_commutator hC (lagTv F a)
  convert key using 3
  have h1 : mat m F (lagTv F a) *ᵥ (Pi.single a.swap 1 : Fin m ⊕ Fin m → F) =
      Pi.single a.swap 1 + Pi.single a 1 := by
    rw [mat_lagTv_mulVec, Pi.single_eq_same, one_smul]
  have h2 : mat m F (lagTv F a) *ᵥ (Pi.single b 1 : Fin m ⊕ Fin m → F) = Pi.single b 1 := by
    rw [mat_lagTv_mulVec, Pi.single_eq_of_ne (Ne.symm hb), zero_smul, add_zero]
  rw [Matrix.mul_smul, Matrix.smul_mul, conj_lagE, h1, h2, lagE_add_left, smul_add,
    sub_add_eq_sub_sub, sub_self, zero_sub, lag_neg_eq]

theorem lagRad_smul_pair_mem_two [CharP F 2] {i j : Fin m} (hij : i ≠ j) (c : F) :
    lagRad m F (Multiplicative.ofAdd (c • ((lagEl (Sum.inl i) (Sum.inr i) : Matrix _ _ F) -
      lagEl (Sum.inl j) (Sum.inr j)))) ∈ ⁅lagR0Grp m F, lagX m F⁆ := by
  have hC : c • (lagEl (Sum.inl j) (Sum.inr i) : Matrix _ _ F) ∈ lagR0 m F :=
    ⟨Submodule.smul_mem _ _ (lagE_mem_lagAlt _ _), by
      show lagOmegaStar m F _ = 0
      rw [map_smul, lagOmegaStar_lagEl_of_ne_swap (by simp [Sum.swap, hij]), smul_zero]⟩
  have key := lagRad_sub_conj_mem_commutator hC (leviTv F hij 1)
  have key2 := lagRad_smul_lagEl_mem_two (a := Sum.inl i) (b := Sum.inr j) (by simp)
    (by simp [Sum.swap, Ne.symm hij]) c
  have := mul_mem key2 (inv_mem key)
  convert this using 1
  rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
  congr 2
  rw [Matrix.mul_smul, Matrix.smul_mul, conj_lagE, mat_leviTv_mulVec_inl, mat_leviTv_mulVec_inr,
    lagE_add_left, lagE_sub_right, lagE_sub_right]
  simp only [smul_sub, smul_add]
  abel

theorem lagRad_mem_commutator_of_mem_lagR0_two [CharP F 2] (hm : 1 ≤ m)
    {C : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F} (hC : C ∈ lagR0 m F) :
    lagRad m F (Multiplicative.ofAdd C) ∈ ⁅lagR0Grp m F, lagX m F⁆ := by
  set i₀ : Fin m := ⟨0, hm⟩
  set P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F := ∑ i, C (Sum.inl i) (Sum.inr i) •
    ((lagEl (Sum.inl i) (Sum.inr i) : Matrix _ _ F) - lagEl (Sum.inl i₀) (Sum.inr i₀)) with hPdef
  have hP : Multiplicative.ofAdd P ∈ (⁅lagR0Grp m F, lagX m F⁆).comap (lagRad m F) := by
    rw [hPdef, ofAdd_sum]
    refine Subgroup.prod_mem _ fun i _ => ?_
    rw [Subgroup.mem_comap]
    by_cases hi : i = i₀
    · rw [hi, sub_self, smul_zero, ofAdd_zero, map_one]
      exact one_mem _
    · exact lagRad_smul_pair_mem_two hi _
  set D := C - P with hDdef
  have hDalt : D ∈ lagAlt m F := sub_mem hC.1 (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (sub_mem (lagE_mem_lagAlt _ _) (lagE_mem_lagAlt _ _)))
  have hω : ∑ i, C (Sum.inl i) (Sum.inr i) = 0 := hC.2
  have hDpair : ∀ k, D (Sum.inl k) (Sum.inr k) = 0 := by
    intro k
    rw [hDdef, hPdef, Matrix.sub_apply, Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.sub_apply, lagEl_pair_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    by_cases hk : k = i₀ <;> simp [hk, hω]
  have hD : Multiplicative.ofAdd D ∈ (⁅lagR0Grp m F, lagX m F⁆).comap (lagRad m F) := by
    rw [eq_sum_lagUpper_smul_lagEl hDalt, ofAdd_sum]
    refine Subgroup.prod_mem _ fun a _ => ?_
    rw [ofAdd_sum]
    refine Subgroup.prod_mem _ fun b _ => ?_
    rw [Subgroup.mem_comap]
    by_cases hab : b = a
    · rw [hab, lagUpper_apply, ite_eq_right (lt_irrefl _), zero_smul, ofAdd_zero, map_one]
      exact one_mem _
    by_cases hb : b = a.swap
    · have h0 : lagUpper D a b = 0 := by
        rw [hb, lagUpper_apply]
        rcases a with k | k
        · simp [Sum.swap, hDpair]
        · rw [ite_eq_right]
          simp [Sum.swap, lagNum]
      rw [h0, zero_smul, ofAdd_zero, map_one]
      exact one_mem _
    · exact lagRad_smul_lagEl_mem_two hab hb _
  have hCD : C = D + P := by rw [hDdef, sub_add_cancel]
  rw [hCD, ofAdd_add, ← Subgroup.mem_comap]
  exact mul_mem hD hP

theorem commutator_lagR0Grp_lagX_two [CharP F 2] (hm : 1 ≤ m) :
    ⁅lagR0Grp m F, lagX m F⁆ = lagR0Grp m F := by
  apply le_antisymm
  · rw [commutator_le]
    rintro _ ⟨C, hC, rfl⟩ _ ⟨A, rfl⟩
    rw [commutatorElement_lagRad_lagLevi]
    exact ⟨_, sub_mem hC (conj_mem_lagR0 hC A), rfl⟩
  · rintro _ ⟨C, hC, rfl⟩
    exact lagRad_mem_commutator_of_mem_lagR0_two hm hC

end Generation

section Centralizer

theorem eq_one_of_commute_lagX_two [CharP F 2] (hmo : Odd m)
    {g : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F} (hg : g ∈ lagR0Grp m F)
    (hc : ∀ x ∈ lagX m F, x * g = g * x) : g = 1 := by
  obtain ⟨C, hC, rfl⟩ := hg
  have hfix : ∀ A : StatedSp m F, mat m F A * C * (mat m F A)ᵀ = C := by
    intro A
    have h := hc _ ⟨A, rfl⟩
    rw [lagLevi_mul_lagRad] at h
    exact congrArg Multiplicative.toAdd (lagRad_injective (mul_right_cancel h))
  have hnp : ∀ x y : Fin m ⊕ Fin m, y ≠ x.swap → C x y = 0 := by
    intro x y hy
    have h := congrFun (congrFun (hfix (lagTv F x.swap)) x.swap) y
    rw [conj_apply_eq_dotProduct, mat_lagTv_row_self, mat_lagTv_row_of_ne hy] at h
    simp only [add_dotProduct, mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply,
      Sum.swap_swap] at h
    linear_combination h
  have hpe : ∀ i j : Fin m, C (Sum.inl i) (Sum.inr i) = C (Sum.inl j) (Sum.inr j) := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have h := congrFun (congrFun (hfix (leviTv F hij 1)) (Sum.inl i)) (Sum.inr j)
    rw [conj_apply_eq_dotProduct, mat_leviTv_row_inl hij, mat_leviTv_row_inr hij] at h
    simp only [add_dotProduct, mulVec_sub, mulVec_single_one, dotProduct_sub, single_dotProduct,
      one_mul, Matrix.col_apply] at h
    have h1 : C (Sum.inl i) (Sum.inr j) = 0 := hnp _ _ (by simp [Sum.swap, Ne.symm hij])
    have h2 : C (Sum.inl j) (Sum.inr i) = 0 := hnp _ _ (by simp [Sum.swap, hij])
    rw [h1, h2] at h
    linear_combination -h
  have hω : ∑ i, C (Sum.inl i) (Sum.inr i) = 0 := hC.2
  have hm1 : (m : F) = 1 := by
    obtain ⟨k, rfl⟩ := hmo
    push_cast
    rw [CharTwo.two_eq_zero, zero_mul, zero_add]
  have hc0 : ∀ i : Fin m, C (Sum.inl i) (Sum.inr i) = 0 := by
    intro i
    have h : ∑ j, C (Sum.inl j) (Sum.inr j) = (m : F) * C (Sum.inl i) (Sum.inr i) := by
      rw [Finset.sum_congr rfl fun j _ => hpe j i, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hω, hm1, one_mul] at h
    exact h.symm
  have hC0 : C = 0 := by
    ext x y
    rw [Matrix.zero_apply]
    by_cases hy : y = x.swap
    · rw [hy]
      rcases x with k | k
      · exact hc0 k
      · rw [Sum.swap_inr, ← transpose_apply C, hC.1.1]
        exact hc0 k
    · exact hnp x y hy
  rw [hC0, ofAdd_zero, map_one]

end Centralizer

section Perfect

theorem commutator_lagP_two [CharP F 2] [Group.IsPerfect (StatedSp m F)] (hm : 1 ≤ m) :
    ⁅lagP m F, lagP m F⁆ = lagP m F := by
  have hX : ⁅lagX m F, lagX m F⁆ = lagX m F := by
    have : Group.IsPerfect (lagX m F) := Group.IsPerfect.range _
    exact Subgroup.commutator_eq_self
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  apply sup_le
  · calc lagR0Grp m F = ⁅lagR0Grp m F, lagX m F⁆ := (commutator_lagR0Grp_lagX_two hm).symm
      _ ≤ ⁅lagP m F, lagP m F⁆ := Subgroup.commutator_mono le_sup_left le_sup_right
  · calc lagX m F = ⁅lagX m F, lagX m F⁆ := hX.symm
      _ ≤ ⁅lagP m F, lagP m F⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

end Perfect

end CFSG.SeitzReduction.SymplecticPilot
