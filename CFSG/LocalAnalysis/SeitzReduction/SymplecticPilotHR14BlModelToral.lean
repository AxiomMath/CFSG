module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlModelLevi
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerB1
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

section Diag

variable (K n) in
@[expose] def spADiag (j : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal fun k => if k.val < 2 * j then 1 else 0

variable {j : ℕ}

theorem spADiag_transpose : (spADiag K n j)ᵀ = spADiag K n j := Matrix.diagonal_transpose _

theorem spADiag_mul_self : spADiag K n j * spADiag K n j = spADiag K n j := by
  rw [spADiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  split_ifs <;> simp

theorem spADiag_mul_spARepMat : spADiag K n j * spARepMat n j = spARepMat n j := by
  ext k l
  rw [spADiag, Matrix.diagonal_mul, spARepMat, of_apply]
  split_ifs with h1 h2 <;> simp_all

theorem spARepMat_mul_spADiag : spARepMat n j * spADiag K n j = spARepMat n j := by
  ext k l
  rw [spADiag, Matrix.mul_diagonal, spARepMat, of_apply]
  split_ifs with h1 h2 <;> simp_all

theorem spARepMat_mul_self (hjn : 2 * j ≤ n) :
    (spARepMat n j : Matrix (Fin n) (Fin n) K) * spARepMat n j = spADiag K n j := by
  ext k l
  rw [Matrix.mul_apply,
    sum_spARepMat_mul hjn (fun m => (spARepMat n j : Matrix (Fin n) (Fin n) K) m l) k,
    spADiag, Matrix.diagonal_apply]
  by_cases hk : k.val < 2 * j
  · rw [ite_eq_left hk, spARepMat_apply hjn]
    by_cases hkl : k = l
    · subst hkl
      rw [ite_eq_left ⟨hk, rfl⟩, ite_eq_left rfl, ite_eq_left hk]
    · rw [ite_eq_right hkl, ite_eq_right]
      rintro ⟨hl, h⟩
      apply hkl
      rw [← spAPar_spAPar hjn hk, h, spAPar_spAPar hjn hl]
  · rw [ite_eq_right hk]
    split_ifs <;> simp_all

theorem spADiag_mul_one_sub : spADiag K n j * (1 - spADiag K n j) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, spADiag_mul_self, sub_self]

theorem one_sub_mul_spADiag : (1 - spADiag K n j) * spADiag K n j = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, spADiag_mul_self, sub_self]

theorem one_sub_spADiag_mul_self :
    (1 - spADiag K n j) * (1 - spADiag K n j) = 1 - spADiag K n j := by
  rw [Matrix.sub_mul, Matrix.one_mul, spADiag_mul_one_sub, sub_zero]

theorem one_sub_spADiag_mul_spARepMat : (1 - spADiag K n j) * spARepMat n j = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, spADiag_mul_spARepMat, sub_self]

theorem spARepMat_mul_one_sub_spADiag : spARepMat n j * (1 - spADiag K n j) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, spARepMat_mul_spADiag, sub_self]

end Diag

section Partner

variable (K n) in
@[expose] def spAPartnerMat (j : ℕ) (X : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks (X 0 0 • spADiag K n j + (1 - spADiag K n j)) (X 0 1 • spARepMat n j)
    (X 1 0 • spARepMat n j) (X 1 1 • spADiag K n j + (1 - spADiag K n j))

variable {j : ℕ}

theorem spAPartnerMat_one : spAPartnerMat K n j 1 = 1 := by
  rw [spAPartnerMat, ← fromBlocks_one]
  simp

theorem spAPartnerMat_mul (hjn : 2 * j ≤ n) (X Y : Matrix (Fin 2) (Fin 2) K) :
    spAPartnerMat K n j (X * Y) = spAPartnerMat K n j X * spAPartnerMat K n j Y := by
  simp only [spAPartnerMat, fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, spADiag_mul_self, spADiag_mul_one_sub, one_sub_mul_spADiag,
    one_sub_spADiag_mul_self, spARepMat_mul_self hjn, spADiag_mul_spARepMat,
    spARepMat_mul_spADiag, one_sub_spADiag_mul_spARepMat, spARepMat_mul_one_sub_spADiag,
    smul_zero, add_zero, zero_add, Matrix.mul_apply, Fin.sum_univ_two]
  congr 1 <;> module

theorem spAPartnerMat_symplectic (hjn : 2 * j ≤ n) {X : Matrix (Fin 2) (Fin 2) K}
    (hX : X.det = 1) :
    (spAPartnerMat K n j X)ᵀ * gram K n * spAPartnerMat K n j X = gram K n := by
  rw [Matrix.det_fin_two] at hX
  have hT1 : (1 - spADiag K n j)ᵀ = 1 - spADiag K n j := by
    rw [transpose_sub, transpose_one, spADiag_transpose]
  simp only [spAPartnerMat, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram,
    fromBlocks_transpose, transpose_add, transpose_smul,
    spADiag_transpose, hT1, spARepMat_transpose, fromBlocks_multiply, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_zero,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, spADiag_mul_self,
    spADiag_mul_one_sub, one_sub_mul_spADiag, one_sub_spADiag_mul_self, spARepMat_mul_self hjn,
    spADiag_mul_spARepMat, spARepMat_mul_spADiag, one_sub_spADiag_mul_spARepMat,
    spARepMat_mul_one_sub_spADiag, smul_zero, smul_neg, add_zero, zero_add, neg_zero]
  congr 1
  · module
  · linear_combination (norm := module) hX • spADiag K n j
  · linear_combination (norm := module) (-1 : K) • (hX • spADiag K n j)
  · module

variable (K n) in
@[expose] noncomputable def spAPartnerHom (hjn : 2 * j ≤ n) : SL(2, K) →* StatedSp n K where
  toFun X := ofSymplecticMat (spAPartnerMat K n j (X : Matrix (Fin 2) (Fin 2) K))
    (spAPartnerMat_symplectic hjn X.2)
  map_one' := mat_injective (by
    rw [mat_ofSymplecticMat, map_one]
    exact spAPartnerMat_one)
  map_mul' X Y := mat_injective (by
    rw [mat_ofSymplecticMat, map_mul, mat_ofSymplecticMat, mat_ofSymplecticMat]
    exact spAPartnerMat_mul hjn _ _)

theorem mat_spAPartnerHom (hjn : 2 * j ≤ n) (X : SL(2, K)) :
    mat n K (spAPartnerHom K n hjn X) = spAPartnerMat K n j (X : Matrix (Fin 2) (Fin 2) K) := rfl

@[expose] def spAPartnerDiag (j : ℕ) (X : Matrix (Fin 2) (Fin 2) K) : Fin n ⊕ Fin n → K :=
  Sum.elim (fun k => if k.val < 2 * j then X 0 0 else 1)
    (fun k => if k.val < 2 * j then X 1 1 else 1)

theorem spAPartnerDiag_eq (X : Matrix (Fin 2) (Fin 2) K) (r : Fin n ⊕ Fin n) :
    spAPartnerDiag j X r = ![X 0 0, X 1 1, 1] (spABlk j r) := by
  rcases r with k | k <;> by_cases hk : k.val < 2 * j <;> simp [spAPartnerDiag, hk]

theorem spAPartnerMat_eq_sum (X : Matrix (Fin 2) (Fin 2) K) :
    spAPartnerMat K n j X = Matrix.diagonal (spAPartnerDiag j X) + X 0 1 • spANil K n j +
      X 1 0 • (spANil K n j)ᵀ := by
  ext r t
  rcases r with k | k <;> rcases t with l | l <;>
    simp only [spAPartnerMat, spANil, spAPartnerDiag, spADiag, fromBlocks_transpose,
      spARepMat_transpose, transpose_zero, Matrix.add_apply, Matrix.smul_apply, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.diagonal_apply,
      Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, Sum.inl.injEq, Sum.inr.injEq,
      Sum.elim_inl, Sum.elim_inr, smul_eq_mul, mul_zero, add_zero, zero_add, reduceCtorEq,
      ite_false] <;>
    split_ifs <;> simp_all

end Partner

section Centralize

variable {j : ℕ}

theorem commute_diagonal_of_blockDiag {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hG : ∀ r t, spABlk j r ≠ spABlk j t → G r t = 0) {w : Fin n ⊕ Fin n → K}
    (hw : ∀ r t, spABlk j r = spABlk j t → w r = w t) :
    G * Matrix.diagonal w = Matrix.diagonal w * G := by
  ext r t
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : spABlk j r = spABlk j t
  · rw [hw r t h, mul_comm]
  · rw [hG r t h, mul_zero, zero_mul]

theorem commute_spANil_transpose_of_blockDiag (hjn : 2 * j ≤ n)
    {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hG : ∀ r t, spABlk j r ≠ spABlk j t → G r t = 0)
    (hN : G * spANil K n j = spANil K n j * G) :
    G * (spANil K n j)ᵀ = (spANil K n j)ᵀ * G := by
  ext r t
  rcases t with l | l
  · rw [mul_spANil_transpose_inl hjn]
    rcases r with k | k
    · rw [spANil_transpose_mul_inl]
      split_ifs with hl
      · refine hG _ _ ?_
        have := spAPar_lt hjn hl
        by_cases hk : k.val < 2 * j <;> simp [hk, this]
      · rfl
    · rw [spANil_transpose_mul_inr hjn]
      by_cases hl : l.val < 2 * j <;> by_cases hk : k.val < 2 * j
      · have e := congrFun (congrFun hN (Sum.inl (spAPar k))) (Sum.inr (spAPar l))
        rw [mul_spANil_inr hjn, spANil_mul_inl hjn, ite_eq_left (spAPar_lt hjn hl),
          ite_eq_left (spAPar_lt hjn hk), spAPar_spAPar hjn hl, spAPar_spAPar hjn hk] at e
        rw [ite_eq_left hl, ite_eq_left hk, e]
      · rw [ite_eq_left hl, ite_eq_right hk]
        refine hG _ _ ?_
        simp [hk, spAPar_lt hjn hl]
      · rw [ite_eq_right hl, ite_eq_left hk]
        refine (hG _ _ ?_).symm
        simp [hl, spAPar_lt hjn hk]
      · rw [ite_eq_right hl, ite_eq_right hk]
  · rw [mul_spANil_transpose_inr]
    rcases r with k | k
    · rw [spANil_transpose_mul_inl]
    · rw [spANil_transpose_mul_inr hjn]
      split_ifs with hk
      · refine (hG _ _ ?_).symm
        have := spAPar_lt hjn hk
        by_cases hl : l.val < 2 * j <;> simp [hl, this]
      · rfl

theorem commute_spAPartnerMat_of_blockDiag (hjn : 2 * j ≤ n)
    {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hG : ∀ r t, spABlk j r ≠ spABlk j t → G r t = 0)
    (hN : G * spANil K n j = spANil K n j * G) (X : Matrix (Fin 2) (Fin 2) K) :
    G * spAPartnerMat K n j X = spAPartnerMat K n j X * G := by
  have hD := commute_diagonal_of_blockDiag hG (w := spAPartnerDiag j X) (by
    intro r t h
    rw [spAPartnerDiag_eq, spAPartnerDiag_eq, h])
  have hT := commute_spANil_transpose_of_blockDiag hjn hG hN
  rw [spAPartnerMat_eq_sum, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
    Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, hD, hN, hT]

theorem range_spALeviHom_le_centralizer_partner (hjn : 2 * j ≤ n) :
    (spALeviHom hjn).range ≤
      centralizer ((spAPartnerHom K n hjn).range : Set (StatedSp n K)) := by
  rintro _ ⟨g, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨X, rfl⟩
  apply mat_injective
  rw [map_mul, map_mul, mat_spALeviHom, mat_spAPartnerHom]
  refine (commute_spAPartnerMat_of_blockDiag hjn (fun r t h => ?_) ?_ _).symm
  · rw [spALeviPart_apply, ite_eq_right h]
  · exact spALeviPart_commute hjn (commute_spARep_iff.1 (mem_centralizer_singleton_iff.1 g.2))

end Centralize

section Props

variable {j : ℕ}

theorem commutator_range_spAPartnerHom [Finite K] (hK : 4 ≤ Nat.card K) (hjn : 2 * j ≤ n) :
    ⁅(spAPartnerHom K n hjn).range, (spAPartnerHom K n hjn).range⁆ =
      (spAPartnerHom K n hjn).range := by
  have : Group.IsPerfect (StatedSp 1 K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 1 K (Or.inl (exists_finset_card_four hK))
  have : Group.IsPerfect SL(2, K) :=
    Group.IsPerfect.ofSurjective (f := (longBlockEquivOne K).symm.toMonoidHom)
      (MulEquiv.surjective _)
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
    Group.IsPerfect.commutator_eq_top]

@[expose] def spAPartnerLowerSL2 : SL(2, K) :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem spAPartnerHom_lower_not_mem_centralizer (hj : 1 ≤ j) (hjn : 2 * j ≤ n) :
    spAPartnerHom K n hjn spAPartnerLowerSL2 ∉ centralizer ({spARep n j} : Set (StatedSp n K)) := by
  intro h
  have h1 := commute_spARep_iff.1 (mem_centralizer_singleton_iff.1 h)
  have e := congrFun (congrFun h1 (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
  rw [mul_spANil_inl, spANil_mul_inl hjn, ite_eq_left (show (0 : ℕ) < 2 * j by omega),
    mat_spAPartnerHom, spAPartnerMat, fromBlocks_apply₂₁, Matrix.smul_apply,
    spARepMat_apply hjn, ite_eq_left ⟨show (0 : ℕ) < 2 * j by omega, rfl⟩] at e
  simp [spAPartnerLowerSL2] at e

end Props

theorem exists_perfect_le_centralizer_of_odd_spARep [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {j : ℕ} (hj : 1 ≤ j) (hjn : 2 * j ≤ n) {S : Subgroup (StatedSp n K)}
    (hS : S ≤ centralizer ({spARep n j} : Set (StatedSp n K))) (hodd : Odd (Nat.card S)) :
    ∃ P : Subgroup (StatedSp n K), P ≤ centralizer (S : Set (StatedSp n K)) ∧ ⁅P, P⁆ = P ∧
      ¬ P ≤ centralizer ({spARep n j} : Set (StatedSp n K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card S) := Nat.coprime_two_left.2 hodd
  obtain ⟨u, hu, hle⟩ := F4Pilot.exists_mem_map_conj_le_of_le_sup (isPGroup_spARadical hjn)
    (range_spALeviHom_le_normalizer hjn) (spARadical_inf_range_eq_bot hjn)
    (hS.trans (centralizer_spARep_le_sup hjn)) hcop
  have hua : u * spARep n j = spARep n j * u :=
    mem_centralizer_singleton_iff.1 (spARadical_le_centralizer hjn hu)
  set P₀ := (spAPartnerHom K n hjn).range with hP₀
  refine ⟨P₀.map (MulAut.conj u⁻¹).toMonoidHom, ?_, ?_, fun hP => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    intro s hs
    have hus : u * s * u⁻¹ ∈ (spALeviHom hjn).range := hle ⟨s, hs, rfl⟩
    have hc := mem_centralizer_iff.1 (range_spALeviHom_le_centralizer_partner hjn hus) y hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc s * (u⁻¹ * y * u) = u⁻¹ * ((u * s * u⁻¹) * y) * u := by group
      _ = u⁻¹ * (y * (u * s * u⁻¹)) * u := by rw [hc]
      _ = u⁻¹ * y * u * s := by group
  · rw [← Subgroup.map_commutator, hP₀, commutator_range_spAPartnerHom hK hjn]
  · have hmem := hP ⟨_, ⟨spAPartnerLowerSL2, rfl⟩, rfl⟩
    apply spAPartnerHom_lower_not_mem_centralizer (K := K) hj hjn
    rw [mem_centralizer_singleton_iff] at hmem ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hmem
    set p := spAPartnerHom K n hjn spAPartnerLowerSL2
    have hconj : u * spARep n j * u⁻¹ = spARep n j := by rw [hua, mul_inv_cancel_right]
    calc p * spARep n j = p * (u * spARep n j * u⁻¹) := by rw [hconj]
      _ = u * ((u⁻¹ * p * u) * spARep n j) * u⁻¹ := by group
      _ = u * (spARep n j * (u⁻¹ * p * u)) * u⁻¹ := by rw [hmem]
      _ = (u * spARep n j * u⁻¹) * p := by group
      _ = spARep n j * p := by rw [hconj]

theorem spAToralInput_holds : SpAToralInput := by
  intro n j K _ _ _ hK hj hjn S hS hodd
  exact exists_perfect_le_centralizer_of_odd_spARep hK hj hjn hS hodd

end CFSG.SeitzReduction.SymplecticPilot
