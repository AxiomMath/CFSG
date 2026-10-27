module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ModelBridge
public import CFSG.Open.StatedDefs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Matrix

section Sp

variable {K : Type*} [Field K] {n : ℕ}

def symJ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Matrix.fromBlocks 0 1 (-1) 0

def symB (x y : Fin n ⊕ Fin n → K) : K := x ⬝ᵥ ((symJ : Matrix _ _ K) *ᵥ y)

theorem symB_eq (x y : Fin n ⊕ Fin n → K) :
    symB x y = ∑ i : Fin n, (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i)) := by
  simp [symB, symJ, dotProduct, Fintype.sum_sum_type, Matrix.mulVec, fromBlocks, Matrix.one_apply, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]


theorem symB_add_left (x x' y : Fin n ⊕ Fin n → K) :
    symB (x + x') y = symB x y + symB x' y := by simp [symB, add_dotProduct]

theorem symB_add_right (x y y' : Fin n ⊕ Fin n → K) :
    symB x (y + y') = symB x y + symB x y' := by
  simp [symB, dotProduct_add, Matrix.mulVec_add]

theorem symB_sub_right (x y y' : Fin n ⊕ Fin n → K) :
    symB x (y - y') = symB x y - symB x y' := by
  simp [symB, dotProduct_sub, Matrix.mulVec_sub]

theorem symB_smul_left (c : K) (x y : Fin n ⊕ Fin n → K) :
    symB (c • x) y = c * symB x y := by simp [symB, smul_dotProduct]

theorem symB_smul_right (c : K) (x y : Fin n ⊕ Fin n → K) :
    symB x (c • y) = c * symB x y := by
  simp [symB, Matrix.mulVec_smul, dotProduct_smul]

theorem symB_comm (x y : Fin n ⊕ Fin n → K) : symB y x = - symB x y := by
  rw [symB_eq, symB_eq, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symB_self (x : Fin n ⊕ Fin n → K) : symB x x = 0 := by
  rw [symB_eq]
  exact Finset.sum_eq_zero fun i _ => by ring

theorem symJ_mul_symJ : (symJ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * symJ = -1 := by
  simp [symJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]
  simp


theorem exists_symB_ne_zero {x : Fin n ⊕ Fin n → K} (hx : x ≠ 0) :
    ∃ y, symB x y ≠ 0 := by
  obtain ⟨s, hs⟩ := Function.ne_iff.mp hx
  refine ⟨-((symJ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ Pi.single s 1), ?_⟩
  have : (symJ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
      (-((symJ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ (Pi.single s 1 : _ → K))) =
      Pi.single s 1 := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, symJ_mul_symJ, Matrix.neg_mulVec,
      Matrix.one_mulVec, neg_neg]
  simp only [symB, this, dotProduct_single, mul_one]
  simpa using hs

theorem form_to_matrix (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (h : ∀ x y, symB (M *ᵥ x) (M *ᵥ y) = symB x y) :
    Mᵀ * symJ * M = symJ := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  funext i
  have key : ∀ x : Fin n ⊕ Fin n → K,
      x ⬝ᵥ ((Mᵀ * symJ * M) *ᵥ v) = x ⬝ᵥ ((symJ : Matrix _ _ K) *ᵥ v) := by
    intro x
    have := h x v
    simp only [symB] at this
    rw [← this]
    simp only [← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simpa using key (Pi.single i 1)


def spGroup (n : ℕ) (K : Type*) [Field K] : Subgroup (Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) K) where
  carrier := {A | ∀ x y, symB ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x)
    ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ y) = symB x y}
  mul_mem' := by
    intro A B hA hB x y
    simp only [Set.mem_ofPred_eq, Units.val_mul, ← Matrix.mulVec_mulVec] at *
    rw [hA, hB]
  one_mem' := by simp
  inv_mem' := by
    intro A hA x y
    have h1 : ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
        ((↑A⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x)) = x := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have h2 : ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
        ((↑A⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ y)) = y := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have := hA ((↑A⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x)
      ((↑A⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ y)
    rw [h1, h2] at this
    exact this.symm

theorem mem_spGroup {A : Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) K} :
    A ∈ spGroup n K ↔ ∀ x y, symB ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x)
      ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ y) = symB x y := Iff.rfl

theorem exists_spGroup_of_form (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (h : ∀ x y, symB (M *ᵥ x) (M *ᵥ y) = symB x y) :
    ∃ g ∈ spGroup n K, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = M := by
  have hM := form_to_matrix M h
  have h1 : (-(symJ * Mᵀ * symJ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * M = 1 := by
    have : (-(symJ * Mᵀ * symJ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * M =
        -(symJ * (Mᵀ * symJ * M)) := by
      simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [this, hM, symJ_mul_symJ, neg_neg]
  have h2 := mul_eq_one_comm.mp h1
  exact ⟨⟨M, _, h2, h1⟩, h, rfl⟩

theorem exists_transvection (w : Fin n ⊕ Fin n → K) (c : K) :
    ∃ g ∈ spGroup n K, ∀ x, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x =
      x + (c * symB x w) • w := by
  have hM : ∀ x, ((1 + c • vecMulVec w ((symJ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x = x + (c * symB x w) • w := by
    intro x
    simp [Matrix.add_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, symB, dotProduct_comm,
      mul_smul]
  obtain ⟨g, hg, hgM⟩ := exists_spGroup_of_form
    (1 + c • vecMulVec w ((symJ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w)) (by
      intro x y
      rw [hM, hM, symB_add_left, symB_add_right, symB_add_right, symB_smul_left,
        symB_smul_right, symB_smul_left, symB_smul_right, symB_self, symB_comm y w]
      ring)
  exact ⟨g, hg, fun x => by rw [hgM, hM]⟩


theorem exists_spGroup_mulVec_eq_of_symB_ne {u v : Fin n ⊕ Fin n → K} (h : symB u v ≠ 0) :
    ∃ g ∈ spGroup n K, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u = v := by
  obtain ⟨g, hg, hgx⟩ := exists_transvection (u - v) (symB u v)⁻¹
  refine ⟨g, hg, ?_⟩
  rw [hgx, symB_sub_right, symB_self, zero_sub, mul_neg, inv_mul_cancel₀ h]
  simp

theorem exists_spGroup_mulVec_eq {u v : Fin n ⊕ Fin n → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g ∈ spGroup n K, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ u = v := by
  by_cases huv : symB u v = 0
  · obtain ⟨p, hp⟩ := exists_symB_ne_zero hu
    obtain ⟨q, hq⟩ := exists_symB_ne_zero hv
    have hq' : symB q v ≠ 0 := by
      rw [symB_comm]; exact neg_ne_zero.mpr hq
    have key : ∃ w, symB u w ≠ 0 ∧ symB w v ≠ 0 := by
      by_cases h1 : symB u q = 0
      · by_cases h2 : symB p v = 0
        · refine ⟨p + q, ?_, ?_⟩
          · rw [symB_add_right, h1, add_zero]; exact hp
          · rw [symB_add_left, h2, zero_add]; exact hq'
        · exact ⟨p, hp, h2⟩
      · exact ⟨q, h1, hq'⟩
    obtain ⟨w, hw1, hw2⟩ := key
    obtain ⟨g₁, hg₁, hg₁u⟩ := exists_spGroup_mulVec_eq_of_symB_ne hw1
    obtain ⟨g₂, hg₂, hg₂w⟩ := exists_spGroup_mulVec_eq_of_symB_ne hw2
    refine ⟨g₂ * g₁, (spGroup n K).mul_mem hg₂ hg₁, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₁u, hg₂w]
  · exact exists_spGroup_mulVec_eq_of_symB_ne huv


def rot3 (p : Fin n) : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) where
  toFun x := fun i => if i = Sum.inl p then -x (Sum.inr p)
    else if i = Sum.inr p then x (Sum.inl p) - x (Sum.inr p) else x i
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem rot3_form (p : Fin n) (x y : Fin n ⊕ Fin n → K) :
    symB (rot3 p x) (rot3 p y) = symB x y := by
  rw [symB_eq, symB_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = p
  · subst hi
    simp [rot3]
    ring
  · simp [rot3, hi]

theorem rot3_cube (p : Fin n) (x : Fin n ⊕ Fin n → K) : rot3 p (rot3 p (rot3 p x)) = x := by
  funext i
  by_cases h1 : i = Sum.inl p
  · subst h1; simp [rot3]
  · by_cases h2 : i = Sum.inr p
    · subst h2; simp [rot3]; ring
    · simp [rot3, h1, h2]

theorem exists_rot3 (p : Fin n) :
    ∃ g ∈ spGroup n K, (∀ x, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x = rot3 p x) := by
  obtain ⟨g, hg, hgM⟩ := exists_spGroup_of_form (LinearMap.toMatrix' (rot3 p : _ →ₗ[K] _)) (by
    intro x y
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, rot3_form])
  exact ⟨g, hg, fun x => by rw [hgM, LinearMap.toMatrix'_mulVec]⟩


end Sp

open Matrix in
theorem threeFixedModel_of_symplectic {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) K))
    (hΓ : ∀ A : Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) K,
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Matrix.fromBlocks 0 1 (-1) 0 →
        A ∈ Γ) :
    ThreeFixedModel Γ (Fin n ⊕ Fin n → K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsp : spGroup n K ≤ Γ := fun A hA => hΓ A (form_to_matrix _ hA)
  let p : Fin n := ⟨1, hn⟩
  let q : Fin n := ⟨0, by omega⟩
  have hqp : q ≠ p := by simp [p, q, Fin.ext_iff]
  obtain ⟨g₀, hg₀, hg₀x⟩ := exists_rot3 (K := K) p
  have hg₀3 : g₀ ^ 3 = 1 := by
    apply Units.ext
    simp only [pow_succ, pow_zero, one_mul, Units.val_mul, Units.val_one]
    rw [Matrix.ext_iff_mulVec]
    intro x
    simp [← Matrix.mulVec_mulVec, hg₀x, rot3_cube]
  have hg₀1 : g₀ ≠ 1 := by
    intro h
    have := congrFun (hg₀x (Pi.single (Sum.inr p) 1)) (Sum.inl p)
    rw [h] at this
    simp [rot3] at this
  have hg₀ord : orderOf g₀ = 3 := orderOf_eq_prime hg₀3 hg₀1
  set e : Fin n ⊕ Fin n → K := Pi.single (Sum.inl q) 1 with he
  have hfix : (g₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ e = e := by
    rw [hg₀x]
    funext i
    by_cases h1 : i = Sum.inl p
    · subst h1
      simp [rot3, he, hqp.symm]
    · by_cases h2 : i = Sum.inr p
      · subst h2
        simp [rot3, he, hqp.symm]
      · simp [rot3, h1, h2]
  have mk : ∀ (g : Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) K) (v : Fin n ⊕ Fin n → K),
      g ∈ spGroup n K → orderOf g = 3 →
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v = v →
      ∃ g' : Γ, orderOf g' = 3 ∧ g' • v = v := by
    intro g v hg h3 hv
    exact ⟨⟨g, hsp hg⟩, by rw [Subgroup.orderOf_mk]; exact h3, hv⟩
  intro v
  by_cases hv : v = 0
  · subst hv
    exact mk g₀ 0 hg₀ hg₀ord (Matrix.mulVec_zero _)
  · have he0 : e ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl q)
      simp [he] at this
    obtain ⟨C, hC, hCe⟩ := exists_spGroup_mulVec_eq he0 hv
    refine mk (C * g₀ * C⁻¹) v ((spGroup n K).mul_mem ((spGroup n K).mul_mem hC hg₀)
      ((spGroup n K).inv_mem hC)) ?_ ?_
    · refine orderOf_eq_prime ?_ ?_
      · rw [conj_pow, hg₀3]; simp
      · intro h
        apply hg₀1
        have : C⁻¹ * (C * g₀ * C⁻¹) * C = 1 := by rw [h]; simp
        simpa [mul_assoc] using this
    · have hCe' : (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ e = v := hCe
      have hinv : (↑C⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v = e := by
        rw [← hCe', Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv,
        hfix, hCe']

theorem threeFixedModel_statedSp {K : Type} [Field K] {n : ℕ} (hn : 2 ≤ n) :
    ThreeFixedModel (CFSG.Open.StatedSp n K) (Fin n ⊕ Fin n → K) :=
  threeFixedModel_of_symplectic hn _ fun _ hA => Subgroup.subset_closure hA

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
