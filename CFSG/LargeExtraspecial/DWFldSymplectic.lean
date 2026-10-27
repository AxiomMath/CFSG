module

public import CFSG.LargeExtraspecial.DWFldLinear
public import CFSG.ClassicalGroups.Symplectic.Model

public section

namespace CFSG.LargeExtraspecial.DW

open Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint

section SymplecticForm

variable {K : Type} [Field K] {n : ℕ}

abbrev spJ (n : ℕ) (K : Type) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 1 (-1) 0

@[expose] noncomputable def spB (n : ℕ) (K : Type) [Field K] :
    LinearMap.BilinForm K (Fin n ⊕ Fin n → K) :=
  Matrix.toBilin' (spJ n K)

theorem spB_apply (x y : Fin n ⊕ Fin n → K) :
    spB n K x y = ∑ i, (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i)) := by
  rw [spB, Matrix.toBilin'_apply']
  simp [dotProduct, Fintype.sum_sum_type, Matrix.mulVec, Matrix.one_apply, sub_eq_add_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem spB_self (x : Fin n ⊕ Fin n → K) : spB n K x x = 0 := by
  rw [spB_apply]
  exact Finset.sum_eq_zero fun i _ => by ring

theorem spB_comm [CharP K 2] (x y : Fin n ⊕ Fin n → K) : spB n K x y = spB n K y x := by
  rw [spB_apply, spB_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i)) * h2

theorem eq_zero_of_spB {w : Fin n ⊕ Fin n → K} (h : ∀ y, spB n K w y = 0) : w = 0 := by
  funext i
  rcases i with i | i
  · have hi := h (Pi.single (Sum.inr i) 1)
    rw [spB_apply] at hi
    simpa [Pi.single_apply] using hi
  · have hi := h (Pi.single (Sum.inl i) 1)
    rw [spB_apply] at hi
    simpa [Pi.single_apply] using hi

theorem mem_statedSp_iff_spB {A : GL (Fin n ⊕ Fin n) K} :
    A ∈ StatedSp n K ↔ ∀ x y, spB n K ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x)
      ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ y) = spB n K x y := by
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
    TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup,
    ← CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup]
  have hcomp : ∀ x y, spB n K ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x)
      ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ y) =
        Matrix.toBilin' ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * spJ n K *
          (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) x y := by
    intro x y
    rw [← Matrix.toBilin'_comp]
    rfl
  constructor
  · intro h x y
    rw [hcomp, h]
    rfl
  · intro h
    apply Matrix.toBilin'.injective
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [← hcomp, h]
    rfl

@[expose] noncomputable def spTMat (a : Fin n ⊕ Fin n → K) (c : K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  1 + c • vecMulVec a (spJ n K *ᵥ a)

theorem spTMat_mulVec (a : Fin n ⊕ Fin n → K) (c : K) (y : Fin n ⊕ Fin n → K) :
    spTMat a c *ᵥ y = y + (c * spB n K y a) • a := by
  rw [spTMat, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul,
    spB, Matrix.toBilin'_apply', dotProduct_comm]

theorem spTMat_mul (a : Fin n ⊕ Fin n → K) (c d : K) :
    spTMat a c * spTMat a d = spTMat a (c + d) := by
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, spTMat_mulVec, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, spB_self, smul_eq_mul, mul_zero, add_zero]
  rw [add_assoc, ← add_smul]
  congr 2
  ring

theorem spTMat_zero (a : Fin n ⊕ Fin n → K) : spTMat a 0 = 1 := by
  rw [spTMat, zero_smul, add_zero]

@[expose] noncomputable def spT (a : Fin n ⊕ Fin n → K) (c : K) : GL (Fin n ⊕ Fin n) K where
  val := spTMat a c
  inv := spTMat a (-c)
  val_inv := by rw [spTMat_mul, add_neg_cancel, spTMat_zero]
  inv_val := by rw [spTMat_mul, neg_add_cancel, spTMat_zero]

theorem spT_mulVec (a : Fin n ⊕ Fin n → K) (c : K) (y : Fin n ⊕ Fin n → K) :
    ((spT a c : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ y =
      y + (c * spB n K y a) • a :=
  spTMat_mulVec a c y

theorem spT_mem_statedSp (a : Fin n ⊕ Fin n → K) (c : K) : spT a c ∈ StatedSp n K := by
  rw [mem_statedSp_iff_spB]
  intro x y
  rw [spT_mulVec, spT_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, spB_self]
  have hs : spB n K a y = - spB n K y a := by
    rw [spB_apply, spB_apply, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs]
  ring

end SymplecticForm

section Plane

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

theorem exists_plane_symplectic {T : GL (Fin n ⊕ Fin n) K} (hT : T ∈ StatedSp n K)
    (hT2 : (T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * T = 1)
    (hT1 : (T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ≠ 1) (x : K) :
    ∃ (w u : Fin n ⊕ Fin n → K) (H : GL (Fin n ⊕ Fin n) K), H ∈ StatedSp n K ∧
      (∀ a b : K, a • w + b • u = 0 → a = 0 ∧ b = 0) ∧
      (T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w = w ∧
      (T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u = u + w ∧
      (H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w = w + x • u ∧
      (H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u = u := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨w, u, hw0, hTw, hTu⟩ := exists_pair_of_involution hT2 hT1
  have hind := independent_of_pair hw0 hTw hTu
  have hinv := mem_statedSp_iff_spB.1 hT
  have huu : spB n K u u = 0 := spB_self u
  by_cases hδ : spB n K w u = 0
  ·
    obtain ⟨y₀, hwy₀⟩ : ∃ y₀, spB n K w y₀ = 1 := by
      obtain ⟨y, hy⟩ : ∃ y, spB n K w y ≠ 0 := by
        by_contra! h
        exact hw0 (eq_zero_of_spB h)
      exact ⟨(spB n K w y)⁻¹ • y, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]⟩
    have hwt : spB n K w ((T : Matrix _ _ K) *ᵥ y₀) = spB n K w y₀ := by
      conv_lhs => rw [← hTw]
      exact hinv w y₀
    have hut : spB n K u ((T : Matrix _ _ K) *ᵥ y₀) = spB n K u y₀ + 1 := by
      have := hinv u y₀
      rw [hTu, map_add, LinearMap.add_apply, hwt, hwy₀] at this
      linear_combination this - h2
    obtain ⟨f, hwf, huf⟩ : ∃ f, spB n K w f = 1 ∧ spB n K u f = 0 := by
      refine ⟨y₀ + spB n K u y₀ • ((T : Matrix _ _ K) *ᵥ y₀ - y₀), ?_, ?_⟩
      · rw [map_add, map_smul, map_sub, hwt, sub_self, smul_zero, add_zero, hwy₀]
      · rw [map_add, map_smul, map_sub, hut, smul_eq_mul]
        linear_combination spB n K u y₀ * h2
    have hff : spB n K f f = 0 := spB_self f
    have hfu : spB n K f u = 0 := by rw [spB_comm, huf]
    refine ⟨w, u, spT (u + f) x * spT u x * spT f x, ?_, hind, hTw, hTu, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (spT_mem_statedSp _ _)
        (spT_mem_statedSp _ _)) (spT_mem_statedSp _ _)
    · simp only [Units.val_mul, ← mulVec_mulVec, spT_mulVec]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hwf,
        hδ, hfu, hff, mul_zero, mul_one, add_zero, zero_add, zero_smul]
      match_scalars <;> first | ring1 | linear_combination x * h2
    · simp only [Units.val_mul, ← mulVec_mulVec, spT_mulVec]
      simp only [map_add, huf, huu, mul_zero, add_zero, zero_smul]
  ·
    refine ⟨w, u, spT u (x * (spB n K w u)⁻¹), spT_mem_statedSp _ _, hind, hTw, hTu, ?_, ?_⟩
    · rw [spT_mulVec, mul_assoc, inv_mul_cancel₀ hδ, mul_one]
    · rw [spT_mulVec, huu, mul_zero, zero_smul, add_zero]

end Plane

section Model

variable {X : Type} [Group X] {D : Set X}

theorem false_of_statedProj_statedSp [Finite X] {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {s : K} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (e : X ≃* StatedProj (StatedSp n K))
    (hD : IsTransClass34 D) : False := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨B, hBD, ⟨l, hl⟩, hB1⟩ := hD.exists_lift e
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (((B : GL (Fin n ⊕ Fin n) K)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) with hMdef
  have hMM : M * M = l • 1 := by
    rw [← hl, hMdef]
    simp
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    subst this
    exact hB1 0 (Subsingleton.elim _ _)
  have hl1 : l = 1 := by
    have hBB := mem_statedSp_iff_spB.1 (B * B).2 (Pi.single (Sum.inl ⟨0, hn⟩) 1)
      (Pi.single (Sum.inr ⟨0, hn⟩) 1)
    have hcoe : (((B * B : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = l • 1 := hl
    rw [hcoe, smul_mulVec, smul_mulVec, one_mulVec, one_mulVec, map_smul, map_smul,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at hBB
    have h1 : spB n K (Pi.single (Sum.inl ⟨0, hn⟩) 1) (Pi.single (Sum.inr ⟨0, hn⟩) 1) = 1 := by
      rw [spB_apply, Finset.sum_eq_single ⟨0, hn⟩]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    rw [h1, mul_one] at hBB
    have h' : (l - 1) ^ 2 = 0 := by linear_combination hBB + (1 - l) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h')
  rw [hl1, one_smul] at hMM
  have hM1 : M ≠ 1 := fun h => hB1 1 (by rw [h, one_smul])
  obtain ⟨w, u, H, hHSp, hind, hTw, hTu, hHw, hHu⟩ :=
    exists_plane_symplectic (T := (B : GL (Fin n ⊕ Fin n) K)) B.2 hMM hM1 s
  let C : StatedSp n K := ⟨H, hHSp⟩
  have hCi : (((C⁻¹ : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * H = 1 := by
    simp [C]
  refine hD.false_of_statedProj e hBD (C := C) fun k hk1 hk4 hmem => ?_
  obtain ⟨c, hc⟩ := mem_statedScalars_iff.1 hmem
  exact conj_pow_ne_smul_one hCi hind hs0 hs1 hTw hTu hHw hHu hk1 hk4 c
    (by simpa [C, mul_assoc] using hc)

theorem false_of_lieModel_PSp [Finite X] {n f : ℕ} (hf : 2 ≤ f) (h : LieModel X .PSp n 2 f)
    (hD : IsTransClass34 D) : False := by
  rcases h with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
    have := charP_two_of_card_eq hK
    obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne_one_of_card hK hf
    exact false_of_statedProj_statedSp hs0 hs1 e hD
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end Model

end CFSG.LargeExtraspecial.DW
