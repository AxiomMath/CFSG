module

public import CFSG.LocalAnalysis.Mason73.L4SylowTransport
public import CFSG.LocalAnalysis.Mason73.L4SL2Witness
public import CFSG.RankThree.PartOne.SLB4A.Basic
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow Matrix

namespace SymplecticWitness

variable {K : Type} [Field K]

@[expose] def spPair (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks (Matrix.diagonal ![A 0 0, 1]) (Matrix.diagonal ![A 0 1, 0])
    (Matrix.diagonal ![A 1 0, 0]) (Matrix.diagonal ![A 1 1, 1])

theorem spPair_mul (A B : Matrix (Fin 2) (Fin 2) K) : spPair A * spPair B = spPair (A * B) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spPair, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem spPair_one : spPair (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spPair]

theorem spPair_symplectic {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    (spPair A)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * spPair A = Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [Matrix.det_fin_two] at hA
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spPair, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hA | linear_combination (-1 : K) * hA

@[expose] def spPairGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 2 ⊕ Fin 2) K where
  toFun A := ⟨spPair A, spPair ↑A⁻¹,
    by
      rw [spPair_mul]
      exact (congrArg (fun X : SpecialLinearGroup (Fin 2) K => spPair X.val)
        (mul_inv_cancel A)).trans spPair_one,
    by
      rw [spPair_mul]
      exact (congrArg (fun X : SpecialLinearGroup (Fin 2) K => spPair X.val)
        (inv_mul_cancel A)).trans spPair_one⟩
  map_one' := by
    apply Units.ext
    show spPair ((1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    exact spPair_one
  map_mul' A B := by
    apply Units.ext
    show spPair ((A * B : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      spPair (A : Matrix (Fin 2) (Fin 2) K) * spPair (B : Matrix (Fin 2) (Fin 2) K)
    rw [spPair_mul]
    rfl

theorem spPairGL_coe (A : SpecialLinearGroup (Fin 2) K) :
    (spPairGL A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = spPair A := rfl

theorem spPairGL_mem (A : SpecialLinearGroup (Fin 2) K) : spPairGL A ∈ Open.StatedSp 2 K := by
  refine Subgroup.subset_closure ?_
  show ((spPairGL A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      Matrix.fromBlocks 0 1 (-1) 0 *
    ((spPairGL A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.fromBlocks 0 1 (-1) 0
  rw [spPairGL_coe]
  exact spPair_symplectic A.2

@[expose] noncomputable def spPairProj :
    SpecialLinearGroup (Fin 2) K →* Open.StatedProj (Open.StatedSp 2 K) :=
  (QuotientGroup.mk' _).comp (spPairGL.codRestrict _ spPairGL_mem)

theorem spPairProj_injective : Function.Injective (spPairProj (K := K)) := by
  refine (injective_iff_map_eq_one _).mpr fun A hA => ?_
  have h1 : spPairGL A ∈ Open.StatedScalars (Fin 2 ⊕ Fin 2) K := by
    have h := (QuotientGroup.eq_one_iff _).mp hA
    exact Subgroup.mem_subgroupOf.mp h
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartOne.SLB4A.mem_statedScalars_iff.mp h1
  rw [spPairGL_coe] at hc
  have e1 := congrFun (congrFun hc (.inl 1)) (.inl 1)
  have e00 := congrFun (congrFun hc (.inl 0)) (.inl 0)
  have e01 := congrFun (congrFun hc (.inl 0)) (.inr 0)
  have e10 := congrFun (congrFun hc (.inr 0)) (.inl 0)
  have e11 := congrFun (congrFun hc (.inr 0)) (.inr 0)
  simp only [spPair, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply_eq,
    Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (Sum.inl_ne_inr), Matrix.diagonal_apply_ne _
      (Sum.inr_ne_inl)] at e1 e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

theorem orderOf_spPairProj (A : SpecialLinearGroup (Fin 2) K) :
    orderOf (spPairProj A) = orderOf A :=
  orderOf_injective _ spPairProj_injective A

end SymplecticWitness

open SymplecticWitness

variable {G : Type} [Group G] [Finite G] {n p f : ℕ}

theorem three_le_pow_of_odd_prime (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) : 3 ≤ p ^ f := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact h3.trans (Nat.le_self_pow (by omega) p)

theorem false_of_lieModel_psp_three_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .PSp 3 p f) : False := by
  have hf : 1 ≤ f := hL.admissible.2.1
  have hcard := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
    (hL.statedClassicalModel (by decide))).2.2.1 rfl
  have h2 := factorization_two_card_of_l4Sylow (by omega) P hP
  rw [hcard, factorization_two_ordBC_three ((hp.eq_two_or_odd'.resolve_left hp2).pow)
    (three_le_pow_of_odd_prime hp hp2 hf)] at h2
  omega

theorem false_of_lieModel_psp_two_of_l4Sylow (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel G .PSp 2 p f) : False := by
  have hf : 1 ≤ f := hL.admissible.2.1
  have hq : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hM := hL.statedClassicalModel (by decide)
  have hcard := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hM).2.2.1 rfl
  have h2 := factorization_two_card_of_l4Sylow (by omega) P hP
  rw [hcard, factorization_two_ordBC_two hq (three_le_pow_of_odd_prime hp hp2 hf)] at h2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hM
  obtain ⟨R, S, hR, hS, hSR⟩ := exists_sl2_inverted_pair (F := K) (by rw [hK]; exact hq)
  rw [hK] at hR
  refine false_of_inverted_of_l4Sylow_of_mulEquiv hn P hP e (R := spPairProj R)
    (S := spPairProj S) (k := ((p ^ f) ^ 2 - 1).factorization 2 - 1) (j := 2) ?_ ?_ ?_ ?_
  · rw [orderOf_spPairProj, hR]
  · rw [orderOf_spPairProj, hS]
    norm_num
  · simpa only [map_mul, map_inv] using congrArg spPairProj hSR
  · omega

end CFSG.LocalAnalysis.Mason73
