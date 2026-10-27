module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open scoped Matrix

private theorem matrix_add_self_eq_zero_of_charTwo {K : Type*} [Field K] [CharP K 2] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : M + M = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

private theorem sub_one_mul_sub_one_eq_zero_of_involution {K : Type*} [Field K] [CharP K 2] {n : ℕ}
    (t : Matrix (Fin n) (Fin n) K) (ht2 : t * t = 1) : (t - 1) * (t - 1) = 0 := by
  have h : (t - 1) * (t - 1) = t * t + 1 - (t + t) := by noncomm_ring
  rw [h, ht2, matrix_add_self_eq_zero_of_charTwo t, sub_zero]
  exact matrix_add_self_eq_zero_of_charTwo 1

private theorem involution_mulVec_sub_one_mulVec {K : Type*} [Field K] [CharP K 2] {n : ℕ}
    (t : Matrix (Fin n) (Fin n) K) (ht2 : t * t = 1) (x : Fin n → K) :
    t *ᵥ ((t - 1) *ᵥ x) = (t - 1) *ᵥ x := by
  have hz : (t - 1) *ᵥ ((t - 1) *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, sub_one_mul_sub_one_eq_zero_of_involution t ht2, Matrix.zero_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hz
  exact sub_eq_zero.mp hz

private theorem vecMulVec_mulVec_eq_smul {K : Type*} [Field K] {n : ℕ} (c γ x : Fin n → K) :
    Matrix.vecMulVec c γ *ᵥ x = (γ ⬝ᵥ x) • c := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem eq_vecMulVec_of_mulVec_eq_smul {K : Type*} [Field K] {n : ℕ}
    {c : Fin n → K} {A : Matrix (Fin n) (Fin n) K} (hA : ∀ x, ∃ s : K, A *ᵥ x = s • c) :
    ∃ γ : Fin n → K, A = Matrix.vecMulVec c γ := by
  choose s hs using hA
  refine ⟨fun j => s (Pi.single j 1), ?_⟩
  ext i j
  have hj := congrFun (hs (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hj
  rw [Matrix.vecMulVec_apply, hj, mul_comm]

private theorem exists_dotProduct_eq_zero_of_notMem_span_pair {K : Type*} [Field K] {n : ℕ}
    (c v w : Fin n → K) (hw : ¬∃ a b : K, a • c + b • v = w) :
    ∃ γ : Fin n → K, γ ⬝ᵥ c = 0 ∧ γ ⬝ᵥ v = 0 ∧ γ ⬝ᵥ w ≠ 0 := by
  have hwp : w ∉ Submodule.span K ({c, v} : Set (Fin n → K)) := by
    rw [Submodule.mem_span_pair]
    exact hw
  obtain ⟨f, hfw, hf⟩ := Submodule.exists_le_ker_of_notMem hwp
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → K, ∀ x : Fin n → K, f x = γ ⬝ᵥ x := by
    refine ⟨fun i => f (fun j => if i = j then 1 else 0), fun x => ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp only [dotProduct, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨γ, ?_, ?_, ?_⟩
  · have hcs : c ∈ Submodule.span K ({c, v} : Set (Fin n → K)) :=
      Submodule.subset_span (Set.mem_insert _ _)
    rw [← hγ c]
    exact LinearMap.mem_ker.mp (hf hcs)
  · have hvs : v ∈ Submodule.span K ({c, v} : Set (Fin n → K)) :=
      Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rw [← hγ v]
    exact LinearMap.mem_ker.mp (hf hvs)
  · rw [← hγ w]
    exact hfw

private theorem exists_smul_eq_of_eq_smul_add_smul {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (c v z : Fin n → K)
    (hc : ∃ x, M *ᵥ x = c) (hz : ∃ x, M *ᵥ x = z) (hv : ∀ x, M *ᵥ x = v → v = 0)
    (a b : K) (hzab : z = a • c + b • v) : ∃ s : K, z = s • c := by
  by_cases hb : b = 0
  · exact ⟨a, by rw [hzab, hb, zero_smul, add_zero]⟩
  · obtain ⟨xc, hxc⟩ := hc
    obtain ⟨xz, hxz⟩ := hz
    have hvR : M *ᵥ (b⁻¹ • (xz - a • xc)) = v := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hxz, hxc, hzab,
        show a • c + b • v - a • c = b • v by abel, inv_smul_smul₀ hb]
    exact ⟨a, by rw [hzab, hv _ hvR, smul_zero, add_zero]⟩

private theorem notMem_span_pair_of_forall_smul {K : Type*} [Field K] {n : ℕ}
    (c v c0 w0 : Fin n → K) (hc0 : c0 ≠ 0) (hw0 : ∀ s : K, w0 ≠ s • c0)
    (hH : ∀ z, (z = c0 ∨ z = w0) → ∀ a b : K, z = a • c + b • v → ∃ s : K, z = s • c) :
    (¬∃ a b : K, a • c + b • v = c0) ∨ (¬∃ a b : K, a • c + b • v = w0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a1, b1, h1⟩, ⟨a2, b2, h2⟩⟩ := hcon
  obtain ⟨s1, hs1⟩ := hH c0 (Or.inl rfl) a1 b1 h1.symm
  obtain ⟨s2, hs2⟩ := hH w0 (Or.inr rfl) a2 b2 h2.symm
  have hs1' : s1 ≠ 0 := by
    rintro rfl
    apply hc0
    rw [hs1, zero_smul]
  apply hw0 (s2 * s1⁻¹)
  rw [hs1, smul_smul, mul_assoc, inv_mul_cancel₀ hs1', mul_one]
  exact hs2

theorem involution_comm_transvection_identity {K : Type*} [Field K] {n : ℕ}
    (t : Matrix (Fin n) (Fin n) K) (ht2 : t * t = 1) (c γ : Fin n → K)
    (htc : t *ᵥ c = c) (hγc : γ ⬝ᵥ c = 0) :
    t * (1 + Matrix.vecMulVec c γ) * t * (1 + Matrix.vecMulVec c γ) =
      1 + Matrix.vecMulVec c (γ ᵥ* t + γ) := by
  have hT : t * Matrix.vecMulVec c γ * t = Matrix.vecMulVec c (γ ᵥ* t) := by
    rw [Matrix.mul_vecMulVec, htc, Matrix.vecMulVec_mul]
  have hL : t * (1 + Matrix.vecMulVec c γ) * t = 1 + Matrix.vecMulVec c (γ ᵥ* t) := by
    rw [mul_add, mul_one, add_mul, ht2, hT]
  have hγtc : (γ ᵥ* t) ⬝ᵥ c = 0 := by
    rw [← Matrix.dotProduct_mulVec, htc, hγc]
  have hPM : Matrix.vecMulVec c (γ ᵥ* t) * Matrix.vecMulVec c γ = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hγtc, zero_smul, Matrix.vecMulVec_zero]
  rw [hL, add_mul, one_mul, mul_add, mul_one, hPM, add_zero, Matrix.vecMulVec_add]
  abel

open Matrix in
theorem exists_transvection_comm_of_involution {K : Type*} [Field K] [CharP K 2] {n : ℕ}
    (t : Matrix (Fin n) (Fin n) K) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (v α : Fin n → K) (hαv : α ⬝ᵥ v = 0) :
    (∃ c γ : Fin n → K, c ≠ 0 ∧ γ ≠ 0 ∧ γ ⬝ᵥ c = 0 ∧ t = 1 + vecMulVec c γ) ∨
    ∃ c γ : Fin n → K, c ≠ 0 ∧ γ ⬝ᵥ c = 0 ∧ γ ⬝ᵥ v = 0 ∧ α ⬝ᵥ c = 0 ∧
      γ ᵥ* t + γ ≠ 0 ∧ (γ ᵥ* t + γ) ⬝ᵥ c = 0 ∧
      t * (1 + vecMulVec c γ) * t * (1 + vecMulVec c γ) = 1 + vecMulVec c (γ ᵥ* t + γ) := by
  have hNN := sub_one_mul_sub_one_eq_zero_of_involution t ht2
  obtain ⟨x0, hx0⟩ : ∃ x0 : Fin n → K, (t - 1) *ᵥ x0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply ht1
    have hz : t - 1 = 0 := by
      ext i j
      have hj := congrFun (hcon (Pi.single j 1)) i
      rw [Matrix.mulVec_single_one, Matrix.col_apply] at hj
      simpa using hj
    exact sub_eq_zero.mp hz
  by_cases h : ∀ y : Fin n → K, ∃ s : K, (t - 1) *ᵥ y = s • (t - 1) *ᵥ x0
  ·
    obtain ⟨γ, hγ⟩ := eq_vecMulVec_of_mulVec_eq_smul h
    have hmv : ∀ x, (t - 1) *ᵥ x = (γ ⬝ᵥ x) • (t - 1) *ᵥ x0 := fun x => by
      conv_lhs => rw [hγ]
      exact vecMulVec_mulVec_eq_smul _ _ _
    have hc0 : (t - 1) *ᵥ ((t - 1) *ᵥ x0) = 0 := by
      rw [Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
    have hγc : γ ⬝ᵥ (t - 1) *ᵥ x0 = 0 := by
      have h1 := hmv ((t - 1) *ᵥ x0)
      rw [hc0] at h1
      exact (smul_eq_zero.mp h1.symm).resolve_right hx0
    refine Or.inl ⟨(t - 1) *ᵥ x0, γ, hx0, ?_, hγc, ?_⟩
    · intro hγ0
      apply ht1
      have h2 : t - 1 = 0 := by rw [hγ, hγ0, Matrix.vecMulVec_zero]
      exact sub_eq_zero.mp h2
    · rw [← hγ]
      abel
  ·
    push Not at h
    obtain ⟨y0, hy0⟩ := h
    obtain ⟨c, hcR, hc0, hαc, hH⟩ : ∃ c : Fin n → K, (∃ x, (t - 1) *ᵥ x = c) ∧ c ≠ 0 ∧
        α ⬝ᵥ c = 0 ∧ ∀ z, (z = (t - 1) *ᵥ x0 ∨ z = (t - 1) *ᵥ y0) → ∀ a b : K,
          z = a • c + b • v → ∃ s : K, z = s • c := by
      by_cases hvR : ∃ x, (t - 1) *ᵥ x = v ∧ v ≠ 0
      · obtain ⟨xv, hxv, hv0⟩ := hvR
        refine ⟨v, ⟨xv, hxv⟩, hv0, hαv, ?_⟩
        rintro z - a b hz
        exact ⟨a + b, by rw [hz, add_smul]⟩
      · have hv : ∀ x, (t - 1) *ᵥ x = v → v = 0 := by
          intro x hx
          by_contra hv0
          exact hvR ⟨x, hx, hv0⟩
        obtain ⟨c, hcR, hc0', hαc⟩ : ∃ c : Fin n → K, (∃ x, (t - 1) *ᵥ x = c) ∧ c ≠ 0 ∧
            α ⬝ᵥ c = 0 := by
          by_cases hp : α ⬝ᵥ (t - 1) *ᵥ x0 = 0
          · exact ⟨(t - 1) *ᵥ x0, ⟨x0, rfl⟩, hx0, hp⟩
          · refine ⟨(α ⬝ᵥ (t - 1) *ᵥ y0) • (t - 1) *ᵥ x0 -
                (α ⬝ᵥ (t - 1) *ᵥ x0) • (t - 1) *ᵥ y0,
              ⟨(α ⬝ᵥ (t - 1) *ᵥ y0) • x0 - (α ⬝ᵥ (t - 1) *ᵥ x0) • y0, ?_⟩, ?_, ?_⟩
            · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
            · intro hcomb
              have hpw : (α ⬝ᵥ (t - 1) *ᵥ x0) • (t - 1) *ᵥ y0 =
                  (α ⬝ᵥ (t - 1) *ᵥ y0) • (t - 1) *ᵥ x0 := (sub_eq_zero.mp hcomb).symm
              apply hy0 ((α ⬝ᵥ (t - 1) *ᵥ x0)⁻¹ * (α ⬝ᵥ (t - 1) *ᵥ y0))
              calc (t - 1) *ᵥ y0
                  = (α ⬝ᵥ (t - 1) *ᵥ x0)⁻¹ • ((α ⬝ᵥ (t - 1) *ᵥ x0) • (t - 1) *ᵥ y0) :=
                    (inv_smul_smul₀ hp _).symm
                _ = (α ⬝ᵥ (t - 1) *ᵥ x0)⁻¹ • ((α ⬝ᵥ (t - 1) *ᵥ y0) • (t - 1) *ᵥ x0) := by
                    rw [hpw]
                _ = ((α ⬝ᵥ (t - 1) *ᵥ x0)⁻¹ * (α ⬝ᵥ (t - 1) *ᵥ y0)) • (t - 1) *ᵥ x0 :=
                    smul_smul _ _ _
            · simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
              ring
        refine ⟨c, hcR, hc0', hαc, ?_⟩
        rintro z (rfl | rfl) a b hz
        · exact exists_smul_eq_of_eq_smul_add_smul (t - 1) c v _ hcR ⟨x0, rfl⟩ hv a b hz
        · exact exists_smul_eq_of_eq_smul_add_smul (t - 1) c v _ hcR ⟨y0, rfl⟩ hv a b hz
    obtain ⟨w, hwR, hwspan⟩ : ∃ w : Fin n → K, (∃ x, (t - 1) *ᵥ x = w) ∧
        ¬∃ a b : K, a • c + b • v = w := by
      rcases notMem_span_pair_of_forall_smul c v ((t - 1) *ᵥ x0) ((t - 1) *ᵥ y0) hx0 hy0 hH
        with hw | hw
      · exact ⟨_, ⟨x0, rfl⟩, hw⟩
      · exact ⟨_, ⟨y0, rfl⟩, hw⟩
    obtain ⟨xw, hxw⟩ := hwR
    obtain ⟨γ, hγc, hγv, hγw⟩ := exists_dotProduct_eq_zero_of_notMem_span_pair c v w hwspan
    obtain ⟨xc, hxc⟩ := hcR
    have htc : t *ᵥ c = c := by
      rw [← hxc]
      exact involution_mulVec_sub_one_mulVec t ht2 xc
    have hkey : ∀ (g x : Fin n → K), (g ᵥ* t + g) ⬝ᵥ x = g ⬝ᵥ (t - 1) *ᵥ x := by
      intro g x
      rw [add_dotProduct, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
        ← Matrix.dotProduct_mulVec, CharTwo.sub_eq_add]
    refine Or.inr ⟨c, γ, hc0, hγc, hγv, hαc, ?_, ?_, ?_⟩
    · intro h0
      apply hγw
      rw [← hxw, ← hkey, h0, zero_dotProduct]
    · rw [add_dotProduct, ← Matrix.dotProduct_mulVec, htc, hγc, add_zero]
    · exact involution_comm_transvection_identity t ht2 c γ htc hγc

end CFSG.ClassicalGroups.SpecialLinear
