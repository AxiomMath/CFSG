module

public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionSymmetric
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

instance decidableMemBinarySymMatrices (n : ℕ) :
    DecidablePred (· ∈ binarySymMatrices n) :=
  fun X => decidable_of_iff (Xᵀ = X) Iff.rfl

instance decidableMemBinaryAltMatrices (n : ℕ) :
    DecidablePred (· ∈ binaryAltMatrices n) :=
  fun X => decidable_of_iff (Xᵀ = X ∧ ∀ i, X i i = 0) mem_binaryAltMatrices.symm

@[expose] def binarySymDetThree (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : ZMod 2 :=
  B 0 0 * B 1 1 * B 2 2 + B 0 0 * B 1 2 + B 1 1 * B 0 2 + B 2 2 * B 0 1

theorem det_eq_binarySymDetThree {B : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hB : B ∈ binarySymMatrices 3) : B.det = binarySymDetThree B := by
  have h10 : B 1 0 = B 0 1 := congrFun (congrFun hB 0) 1
  have h20 : B 2 0 = B 0 2 := congrFun (congrFun hB 0) 2
  have h21 : B 2 1 = B 1 2 := congrFun (congrFun hB 1) 2
  rw [det_fin_three, binarySymDetThree, h10, h20, h21]
  generalize B 0 0 = x, B 1 1 = y, B 2 2 = w, B 0 1 = a, B 0 2 = b, B 1 2 = c
  revert x y w a b c
  decide

theorem card_image_mulVec_eq_pow_rank {m n K : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    [Field K] [Fintype K] [DecidableEq K] (A : Matrix m n K) :
    (Finset.univ.image A.mulVec).card = Fintype.card K ^ A.rank := by
  rw [Matrix.rank, ← Module.card_eq_pow_finrank, ← Set.toFinset_range, Set.toFinset_card]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => by rw [LinearMap.mem_range]; rfl)

theorem rank_eq_one_iff_card_image_mulVec {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n (ZMod 2)) : A.rank = 1 ↔ (Finset.univ.image A.mulVec).card = 2 := by
  rw [card_image_mulVec_eq_pow_rank, ZMod.card]
  constructor
  · intro h
    rw [h, pow_one]
  · intro h
    exact Nat.pow_right_injective le_rfl (h.trans (pow_one 2).symm)

@[expose] noncomputable def zeroSumIncidence {A : Type*} [AddCommMonoid A] (Λ : Set A) (k : ℕ)
    (p : A) : ℕ :=
  Set.ncard {X : Finset A | (X : Set A) ⊆ Λ ∧ X.card = k ∧ p ∈ X ∧ ∑ x ∈ X, x = 0}

theorem zeroSumIncidence_apply_equiv {A : Type*} [AddCommMonoid A] (e : A ≃ A) {Λ : Set A}
    (hΛ : ∀ x, e x ∈ Λ ↔ x ∈ Λ) (k : ℕ)
    (hsum : ∀ X : Finset A, X.card = k → ((∑ x ∈ X, e x) = 0 ↔ ∑ x ∈ X, x = 0)) (p : A) :
    zeroSumIncidence Λ k (e p) = zeroSumIncidence Λ k p := by
  unfold zeroSumIncidence
  symm
  apply Set.ncard_congr (fun X _ => X.map e.toEmbedding)
  · rintro X ⟨hXΛ, hXk, hpX, hX0⟩
    refine ⟨?_, ?_, Finset.mem_map_of_mem _ hpX, ?_⟩
    · intro y hy
      rw [Finset.coe_map, Equiv.coe_toEmbedding] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact (hΛ x).2 (hXΛ hx)
    · rw [Finset.card_map, hXk]
    · rw [Finset.sum_map, Equiv.coe_toEmbedding]
      exact (hsum X hXk).2 hX0
  · intro X Y _ _ h
    exact Finset.map_injective _ h
  · rintro Y ⟨hYΛ, hYk, hpY, hY0⟩
    have hmap : (Y.map e.symm.toEmbedding).map e.toEmbedding = Y := by
      ext y
      simp
    have hk : (Y.map e.symm.toEmbedding).card = k := by rw [Finset.card_map, hYk]
    refine ⟨Y.map e.symm.toEmbedding, ⟨?_, hk, ?_, ?_⟩, hmap⟩
    · intro x hx
      rw [Finset.coe_map, Equiv.coe_toEmbedding] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (hΛ _).1 (by rw [Equiv.apply_symm_apply]; exact hYΛ hy)
    · exact Finset.mem_map.2 ⟨e p, hpY, by simp⟩
    · refine (hsum _ hk).1 ?_
      have h := Finset.sum_map (Y.map e.symm.toEmbedding) e.toEmbedding (fun y => y)
      rw [hmap] at h
      exact h.symm.trans hY0

theorem apply_mem_iff_of_image_eq {α : Type*} (e : α ≃ α) {s : Set α} (h : ⇑e '' s = s)
    (x : α) : e x ∈ s ↔ x ∈ s := by
  conv_lhs => rw [← h]
  exact e.injective.mem_set_image

theorem zeroSumIncidence_addEquiv {A : Type*} [AddCommMonoid A] (g : A ≃+ A) {Λ : Set A}
    (hΛ : ⇑g '' Λ = Λ) (k : ℕ) (p : A) :
    zeroSumIncidence Λ k (g p) = zeroSumIncidence Λ k p :=
  zeroSumIncidence_apply_equiv g.toEquiv (apply_mem_iff_of_image_eq g.toEquiv hΛ) k
    (fun X _ => by
      change ∑ x ∈ X, g x = 0 ↔ _
      rw [← map_sum, AddEquiv.map_eq_zero_iff]) p

theorem zeroSumIncidence_affine {A : Type*} [AddCommMonoid A] (g : A ≃+ A) {a : A}
    (ha : a + a = 0) {Λ : Set A} (hΛ : (fun x => g x + a) '' Λ = Λ) {k : ℕ} (hk : k • a = 0)
    (p : A) : zeroSumIncidence Λ k (g p + a) = zeroSumIncidence Λ k p :=
  let e : A ≃ A :=
    { toFun := fun x => g x + a
      invFun := fun y => g.symm (y + a)
      left_inv := fun x => by simp [add_assoc, ha]
      right_inv := fun y => by simp [add_assoc, ha] }
  zeroSumIncidence_apply_equiv e (apply_mem_iff_of_image_eq e hΛ) k (fun X hX => by
      change ∑ x ∈ X, (g x + a) = 0 ↔ _
      rw [Finset.sum_add_distrib, Finset.sum_const, hX, hk, add_zero, ← map_sum,
        AddEquiv.map_eq_zero_iff]) p

theorem zeroSumIncidence_eq_card_erase {A : Type*} [AddCommMonoid A] [DecidableEq A]
    {Λ : Set A} (S : Finset A) (hS : ↑S = Λ) {k : ℕ} (hk : 1 ≤ k) {p : A} (hpΛ : p ∈ Λ) :
    zeroSumIncidence Λ k p =
      (((S.erase p).powersetCard (k - 1)).filter fun Y => p + ∑ y ∈ Y, y = 0).card := by
  subst hS
  have hp : p ∈ S := Finset.mem_coe.1 hpΛ
  unfold zeroSumIncidence
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun X _ => X.erase p)
  · rintro X ⟨hXS, hXk, hpX, hX0⟩
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.erase_subset_erase p (Finset.coe_subset.1 hXS), ?_⟩, ?_⟩
    · rw [Finset.card_erase_of_mem hpX, hXk]
    · exact (Finset.add_sum_erase X id hpX).trans hX0
  · rintro X Y ⟨-, -, hpX, -⟩ ⟨-, -, hpY, -⟩ h
    rw [← Finset.insert_erase hpX, ← Finset.insert_erase hpY, h]
  · intro Y hY
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hY
    obtain ⟨⟨hYS, hYk⟩, hY0⟩ := hY
    have hpY : p ∉ Y := fun h => Finset.notMem_erase p S (hYS h)
    refine ⟨insert p Y, ⟨?_, ?_, Finset.mem_insert_self p Y, ?_⟩, Finset.erase_insert hpY⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hp fun y hy => Finset.mem_of_mem_erase (hYS hy)
    · rw [Finset.card_insert_of_notMem hpY, hYk]
      omega
    · rw [Finset.sum_insert hpY]
      exact hY0

theorem not_transitive_of_zeroSumIncidence_ne {A : Type*} [AddCommMonoid A] {Λ : Set A} {k : ℕ}
    {p q : A} (hp : p ∈ Λ) (hq : q ∈ Λ) (hne : zeroSumIncidence Λ k p ≠ zeroSumIncidence Λ k q)
    (G : Type*) [Group G] [DistribMulAction G A] (hG : ∀ g : G, (fun x => g • x) '' Λ = Λ) :
    ¬ ∀ p ∈ Λ, ∀ q ∈ Λ, ∃ g : G, g • p = q := by
  intro h
  obtain ⟨g, hg⟩ := h p hp q hq
  have he : ⇑(DistribMulAction.toAddEquiv A g) '' Λ = Λ := by
    have hfun : ⇑(DistribMulAction.toAddEquiv A g) = fun x => g • x :=
      funext fun x => DistribMulAction.toAddEquiv_apply A g x
    rw [hfun]
    exact hG g
  apply hne
  rw [← hg, ← DistribMulAction.toAddEquiv_apply A g p, zeroSumIncidence_addEquiv _ he]

end CFSG.LocalAnalysis.ComponentInitial
