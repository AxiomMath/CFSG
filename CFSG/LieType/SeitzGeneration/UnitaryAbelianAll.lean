module

public import CFSG.LieType.SeitzGeneration.UnitaryAbelianGen
public import CFSG.LieType.SeitzGeneration.UnitaryNonCube

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem closure_planeFixUn_abelian (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1)
    (hq : ℓ ^ f ≠ 2) (hn : 3 ≤ n) {x y : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n))
    (hy : y ∈ primeFormUnitary h (idGram K n)) (hxy : x * y = y * x) {α β : K} (hα : α ≠ 0)
    (hβ : β ≠ 0) (hx3 : ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hy3 : ((y ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1)
    (hind : ∀ a b : ℕ,
      (∃ c : K, ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) →
        3 ∣ a ∧ 3 ∣ b) :
    Subgroup.closure (FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = ⊤ := by
  classical
  have hfin := h.finite
  have hnx : ∀ c : K, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1 := fun c hc => by
    have := hind 1 0 ⟨c, by simpa using hc⟩
    omega
  have hny : ∀ c : K, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1 := fun c hc => by
    have := hind 0 1 ⟨c, by simpa using hc⟩
    omega
  have hnxy : ∀ c : K, ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1 := fun c hc => by
    have := hind 1 1 ⟨c, by simpa using hc⟩
    omega
  have hnxy2 : ∀ c : K, ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1 :=
    fun c hc => by
      have := hind 1 2 ⟨c, by simpa using hc⟩
      omega
  have hxyU : x * y ∈ primeFormUnitary h (idGram K n) := mul_mem hx hy
  have hxy2U : x * y ^ 2 ∈ primeFormUnitary h (idGram K n) := mul_mem hx (pow_mem hy 2)
  have hxy3 : ((x * y) ^ 3 : GL (Fin n) K) = x ^ 3 * y ^ 3 := by
    rw [(Commute.mul_pow (show Commute x y from hxy) 3)]
  have hxy23 : ((x * y ^ 2) ^ 3 : GL (Fin n) K) = x ^ 3 * (y ^ 3) ^ 2 := by
    rw [Commute.mul_pow (show Commute x (y ^ 2) from (show Commute x y from hxy).pow_right 2) 3,
      ← pow_mul, ← pow_mul, mul_comm 2 3]
  have hcom : ∀ a b : GL (Fin n) K, (((a * b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (a : Matrix (Fin n) (Fin n) K) * (b : Matrix (Fin n) (Fin n) K) := fun a b => rfl
  have hc1 : (((x * y) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (α * β) • 1 := by
    rw [hxy3, hcom, hx3, hy3, smul_mul_smul_comm, mul_one]
  have hc2 : (((x * y ^ 2) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (α * β ^ 2) • 1 := by
    rw [hxy23, hcom, hx3, Units.val_pow_eq_pow_val, hy3, _root_.smul_pow, one_pow,
      smul_mul_smul_comm, mul_one]
  have hfull : ∀ S : Set (unitarySU ℓ f K n),
      S ⊆ (FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪
        FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K) ∪
        FixUn ℓ f n K ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∪
        FixUn ℓ f n K ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) →
      Subgroup.closure S = ⊤ →
      Subgroup.closure (FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪
        FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K) ∪
        FixUn ℓ f n K ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∪
        FixUn ℓ f n K ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = ⊤ :=
    fun S hS hT => top_unique (by rw [← hT]; exact Subgroup.closure_mono hS)
  by_cases hcx : ∃ μ : K, μ ^ 3 = α
  · by_cases hcy : ∃ ν : K, ν ^ 3 = β
    · exact closure_planeFixUn_abelian_of_cube_roots h hq3 hq hn hx hy hxy hα hβ hx3 hy3 hind
        hcx hcy
    ·
      refine hfull _ ?_ (closure_planeFixUn_abelian_noncube h hq3 hq hn hy hx hxy.symm hα hy3
        hx3 hnx hcy hcx)
      intro g hg
      simp only [Set.mem_union] at hg ⊢
      tauto
  · by_cases hcy : ∃ ν : K, ν ^ 3 = β
    ·
      refine hfull _ ?_ (closure_planeFixUn_abelian_noncube h hq3 hq hn hx hy hxy hβ hx3 hy3
        hny hcx hcy)
      intro g hg
      simp only [Set.mem_union] at hg ⊢
      tauto
    · rcases NonCube.cube_dichotomy hα hβ hcx hcy with hρ | hρ
      ·
        refine hfull _ ?_ (closure_planeFixUn_abelian_noncube h hq3 hq hn hx hxyU
          ((Commute.refl x).mul_right (show Commute x y from hxy)).eq (mul_ne_zero hα hβ) hx3
          hc1 hnxy hcx hρ)
        intro g hg
        simp only [Set.mem_union] at hg ⊢
        tauto
      ·
        refine hfull _ ?_ (closure_planeFixUn_abelian_noncube h hq3 hq hn hx hxy2U
          ((Commute.refl x).mul_right ((show Commute x y from hxy).pow_right 2)).eq
          (mul_ne_zero hα (pow_ne_zero 2 hβ)) hx3 hc2 hnxy2 hcx hρ)
        intro g hg
        simp only [Set.mem_union] at hg ⊢
        tauto



end CFSG.LieType.SeitzGeneration
