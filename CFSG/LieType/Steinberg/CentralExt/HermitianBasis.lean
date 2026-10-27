module

public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.LieType.Steinberg

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

section General

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ} {G : Matrix (Fin n) (Fin n) F}

theorem herm_mulVec_conj (hσ : ∀ c, σ (σ c) = c) (hG : conjTr σ G = G) (x y : Fin n → F) :
    herm σ y (G *ᵥ x) = σ (herm σ x (G *ᵥ y)) := by
  have hGij : ∀ i j, σ (G i j) = G j i := fun i j => by
    simpa [conjTr] using congrFun (congrFun hG j) i
  simp only [herm, mulVec, dotProduct, map_sum, map_mul, hσ, hGij, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem eq_zero_of_herm_mulVec (hdet : G.det ≠ 0) {x : Fin n → F}
    (h : ∀ y, herm σ x (G *ᵥ y) = 0) : x = 0 := by
  have h1 : (fun i => σ (x i)) ᵥ* G = 0 := by
    funext i
    have hi := h (Pi.single i 1)
    have e : herm σ x (G *ᵥ Pi.single i 1) = (fun i => σ (x i)) ⬝ᵥ (G *ᵥ Pi.single i 1) := rfl
    rw [e, dotProduct_mulVec, dotProduct_single, mul_one] at hi
    exact hi
  have h2 := eq_zero_of_vecMul_eq_zero hdet h1
  funext i
  simpa using congrFun h2 i

private theorem herm_mulVec_sum {k : ℕ} (x : Fin n → F) (c : Fin k → F)
    (v : Fin k → Fin n → F) :
    herm σ x (G *ᵥ ∑ i, c i • v i) = ∑ i, c i * herm σ x (G *ᵥ v i) := by
  have h := map_sum ((hermL σ x).comp G.mulVecLin) (fun i => c i • v i) Finset.univ
  simp only [LinearMap.comp_apply, mulVecLin_apply, hermL_apply, map_smul, smul_eq_mul] at h
  exact h

private theorem herm_mulVec_eq_zero_of_isotropic (hσ : IsUnitaryInvolution σ)
    (hG : conjTr σ G = G) (P : (Fin n → F) →ₗ[F] Fin n → F)
    (hP : ∀ y, herm σ (P y) (G *ᵥ P y) = 0) (y y' : Fin n → F) :
    herm σ (P y) (G *ᵥ P y') = 0 := by
  obtain ⟨c, hc⟩ := hσ.exists_ne
  have h1 := hP (y + y')
  have h2 := hP (y + c • y')
  have hconj := herm_mulVec_conj hσ.invol hG (P y) (P y')
  simp only [map_add, map_smul, mulVec_add, mulVec_smul, herm_add_left, herm_add_right,
    herm_smul_left, herm_smul_right, hP y, hP y', hconj] at h1 h2
  have h3 : (c - σ c) * herm σ (P y) (G *ᵥ P y') = 0 := by linear_combination h2 - σ c * h1
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hc
  · exact h

private theorem exists_norm_one_perp_of_lt (hσ : IsUnitaryInvolution σ) (hG : conjTr σ G = G)
    (hdet : G.det ≠ 0) {k : ℕ} (hk : k < n) (b : Fin k → Fin n → F)
    (hb : ∀ i j, herm σ (b i) (G *ᵥ b j) = if i = j then 1 else 0) :
    ∃ v, herm σ v (G *ᵥ v) = 1 ∧ ∀ i, herm σ (b i) (G *ᵥ v) = 0 := by
  let P : (Fin n → F) →ₗ[F] Fin n → F :=
    LinearMap.id - ∑ i, ((hermL σ (b i)).comp G.mulVecLin).smulRight (b i)
  have hPy : ∀ y, P y = y - ∑ i, herm σ (b i) (G *ᵥ y) • b i := fun y => by simp [P]
  have hbP : ∀ y j, herm σ (b j) (G *ᵥ P y) = 0 := by
    intro y j
    rw [hPy, mulVec_sub, herm_sub_right, herm_mulVec_sum]
    simp [hb]
  suffices ∃ y, herm σ (P y) (G *ᵥ P y) ≠ 0 by
    obtain ⟨y, hy⟩ := this
    have hfix : σ (herm σ (P y) (G *ᵥ P y))⁻¹ = (herm σ (P y) (G *ᵥ P y))⁻¹ := by
      rw [map_inv₀, ← herm_mulVec_conj hσ.invol hG]
    obtain ⟨c, hc⟩ := hσ.norm_surj _ hfix (inv_ne_zero hy)
    refine ⟨c • P y, ?_, fun j => ?_⟩
    · rw [mulVec_smul, herm_smul_left, herm_smul_right, ← mul_assoc, hc, inv_mul_cancel₀ hy]
    · rw [mulVec_smul, herm_smul_right, hbP, mul_zero]
  by_contra! h
  have hpol := herm_mulVec_eq_zero_of_isotropic hσ hG P h
  have hP0 : ∀ y, P y = 0 := by
    intro y
    apply eq_zero_of_herm_mulVec hdet
    intro y'
    have hy' : y' = P y' + ∑ i, herm σ (b i) (G *ᵥ y') • b i := by rw [hPy]; abel
    rw [hy', mulVec_add, herm_add_right, hpol, herm_mulVec_sum]
    simp [herm_mulVec_conj hσ.invol hG _ (P y), hbP]
  have htop : Submodule.span F (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y = ∑ i, herm σ (b i) (G *ᵥ y) • b i := by
      have := hPy y
      rw [hP0] at this
      exact sub_eq_zero.mp this.symm
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hle := finrank_range_le_card (R := F) b
  rw [Set.finrank, htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at hle
  omega

theorem exists_herm_orthonormal (hσ : IsUnitaryInvolution σ) (hG : conjTr σ G = G)
    (hdet : G.det ≠ 0) :
    ∃ b : Fin n → Fin n → F, LinearIndependent F b ∧
      ∀ i j, herm σ (b i) (G *ᵥ b j) = if i = j then 1 else 0 := by
  have key : ∀ k ≤ n, ∃ b : Fin k → Fin n → F,
      ∀ i j, herm σ (b i) (G *ᵥ b j) = if i = j then 1 else 0 := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨Fin.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨b, hb⟩ := ih (by omega)
      obtain ⟨v, hv, hbv⟩ := exists_norm_one_perp_of_lt hσ hG hdet (by omega) b hb
      have hvb : ∀ i, herm σ v (G *ᵥ b i) = 0 := fun i => by
        rw [herm_mulVec_conj hσ.invol hG (b i) v, hbv i, map_zero]
      refine ⟨Fin.cons v b, fun i j => ?_⟩
      cases i using Fin.cases <;> cases j using Fin.cases <;>
        simp [hv, hbv, hvb, hb, (Fin.succ_ne_zero _).symm]
  obtain ⟨b, hb⟩ := key n le_rfl
  refine ⟨b, Fintype.linearIndependent_iff.mpr fun g hg j => ?_, hb⟩
  have := congrArg (fun y => herm σ (b j) (G *ᵥ y)) hg
  simp only [mulVec_zero, herm_zero_right, herm_mulVec_sum, hb] at this
  simpa using this

theorem exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution (hσ : IsUnitaryInvolution σ)
    (hG : conjTr σ G = G) (hdet : G.det ≠ 0) :
    ∃ P : GL (Fin n) F, conjTr σ (P : Matrix (Fin n) (Fin n) F) * G *
      (P : Matrix (Fin n) (Fin n) F) = 1 := by
  obtain ⟨b, -, hb⟩ := exists_herm_orthonormal hσ hG hdet
  have hP : conjTr σ (of b)ᵀ * G * (of b)ᵀ = 1 := by
    ext i j
    rw [one_apply, ← hb i j]
    simp only [conjTr, mul_apply, transpose_apply, map_apply, of_apply, herm, mulVec, dotProduct,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  exact ⟨⟨(of b)ᵀ, conjTr σ (of b)ᵀ * G, mul_eq_one_comm.mp hP, hP⟩, hP⟩

end General

theorem exists_conjTr_mul_mul_eq_one {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} {G : Matrix (Fin n) (Fin n) F}
    (hG : conjTr (unitaryInvolution F p f) G = G) (hdet : G.det ≠ 0) :
    ∃ P : GL (Fin n) F, conjTr (unitaryInvolution F p f) (P : Matrix (Fin n) (Fin n) F) * G *
      (P : Matrix (Fin n) (Fin n) F) = 1 :=
  exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution
    (isUnitaryInvolution_unitaryInvolution hF) hG hdet

end CFSG.LieType.Steinberg
