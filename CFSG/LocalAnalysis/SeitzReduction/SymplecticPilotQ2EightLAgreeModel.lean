module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightLAgreeCent
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)

variable {K : Type} [Field K]

section Blocks

variable {n : ℕ}

theorem mat_nsElt_eq_fromBlocks (k : Fin n) :
    mat n K (nsElt k) = fromBlocks (1 - single k k 1) (single k k 1) (-single k k 1)
      (1 - single k k 1 - single k k 1) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    by_cases hi : i = k <;> by_cases hj : j = k <;>
      (try subst hi) <;> (try subst hj) <;>
      simp [mat_nsElt, blockMat, zThreeMat, Matrix.one_apply, *, Ne.symm]

theorem mat_nsElt_mul_nsElt_eq_fromBlocks {p p' : Fin n} (hpp : p ≠ p') :
    mat n K (nsElt p * nsElt p') =
      fromBlocks (1 - (single p p 1 + single p' p' 1)) (single p p 1 + single p' p' 1)
        (-(single p p 1 + single p' p' 1))
        (1 - (single p p 1 + single p' p' 1) - (single p p 1 + single p' p' 1)) := by
  have h1 : single p p (1 : K) * single p' p' 1 = 0 := single_mul_single_of_ne _ _ _ _ hpp _
  rw [map_mul, mat_nsElt_eq_fromBlocks, mat_nsElt_eq_fromBlocks, fromBlocks_multiply]
  congr 1 <;>
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
      Matrix.neg_mul, h1, neg_zero, sub_zero] <;> abel

end Blocks

section Embed

variable {N ε : ℕ}

theorem q2EmbedMat_mem_q2Block {R : Finset (Fin N)} {Y : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K}
    {x : SpecialLinearGroup (Fin (2 * N + ε)) K}
    (hx : (x : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) = q2EmbedMat ε Y)
    (hY : ∀ u v, (u ∈ planeCoords R ∨ v ∈ planeCoords R) →
      Y u v = (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) u v) :
    x ∈ q2Block ε K R := by
  rw [q2Block, mem_blockSpecialLinear]
  intro a b hab
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
  rw [hx, q2EmbedMat_apply, Matrix.one_apply]
  simp only [(q2Coord N ε).injective.eq_iff]
  simp only [Finset.mem_compl, not_not, q2Coord_mem_planeCoordsQ2] at hab
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, hY u v (by
      simp only [mem_planeCoords]
      rcases hab with h | h
      · exact Or.inl h
      · exact Or.inr h), Matrix.one_apply]
    simp only [Sum.inl.injEq]
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    simp
  · simp at hab

theorem q2EmbedMat_injective : Function.Injective (q2EmbedMat (K := K) (N := N) ε) := by
  intro Y Z h
  ext u v
  have := congrFun (congrFun h (q2Coord N ε (Sum.inl u))) (q2Coord N ε (Sum.inl v))
  rwa [q2EmbedMat_apply, q2EmbedMat_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₁] at this

end Embed

section Sigma

@[expose] def q2SigmaPlane : Matrix (Fin 4) (Fin 4) K :=
  Matrix.transvection 2 3 1 * Matrix.transvection 3 2 1

@[expose] def q2SigmaMat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  fromBlocks q2SigmaPlane 0 0 q2SigmaPlane

theorem det_q2SigmaPlane : (q2SigmaPlane (K := K)).det = 1 := by
  rw [q2SigmaPlane, det_mul, det_transvection_of_ne (i := (2 : Fin 4)) (j := 3) (by decide),
    det_transvection_of_ne (i := (3 : Fin 4)) (j := 2) (by decide), mul_one]

theorem det_q2EmbedMat_q2SigmaMat : (q2EmbedMat 0 (q2SigmaMat (K := K))).det = 1 := by
  rw [det_q2EmbedMat, q2SigmaMat, det_fromBlocks_zero₂₁, det_q2SigmaPlane, mul_one]

@[expose] noncomputable def q2SigmaE : SpecialLinearGroup (Fin (2 * 4 + 0)) K :=
  ⟨q2EmbedMat 0 q2SigmaMat, det_q2EmbedMat_q2SigmaMat⟩

theorem q2SigmaPlane_apply_of_lt {i j : Fin 4} (h : i.val < 2 ∨ j.val < 2) :
    q2SigmaPlane (K := K) i j = (1 : Matrix (Fin 4) (Fin 4) K) i j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [q2SigmaPlane, Matrix.mul_apply, Matrix.transvection, Matrix.one_apply]

theorem q2SigmaE_mem_q2Block : q2SigmaE (K := K) ∈ q2Block 0 K ({0, 1} : Finset (Fin 4)) := by
  refine q2EmbedMat_mem_q2Block rfl fun u v huv => ?_
  have hlt : ∀ {w : Fin 4 ⊕ Fin 4}, w ∈ planeCoords ({0, 1} : Finset (Fin 4)) →
      (planeOf w).val < 2 := fun {w} hw => by
    rw [mem_planeCoords] at hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h | h <;> rw [h] <;> decide
  have huv' : (planeOf u).val < 2 ∨ (planeOf v).val < 2 := huv.imp hlt hlt
  rcases u with i | i <;> rcases v with j | j <;>
    simp only [planeOf_inl, planeOf_inr] at huv' <;>
    simp only [q2SigmaMat, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, ite_false]
  · rw [q2SigmaPlane_apply_of_lt huv', Matrix.one_apply]
  · rw [q2SigmaPlane_apply_of_lt huv', Matrix.one_apply]

theorem q2SigmaPlane_mul_proj :
    q2SigmaPlane (K := K) * (single 2 2 1 + single 3 3 1) =
      (single 2 2 1 + single 3 3 1) * q2SigmaPlane := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [q2SigmaPlane, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transvection,
      Matrix.one_apply]

theorem commute_q2SigmaE_q2Embed (hK : Nat.card K = 2) :
    Commute (q2SigmaE (K := K)) (q2Embed 0 hK (nsElt 2 * nsElt 3)) := by
  have hD := q2SigmaPlane_mul_proj (K := K)
  have hM : q2SigmaMat (K := K) * mat 4 K (nsElt 2 * nsElt 3) =
      mat 4 K (nsElt 2 * nsElt 3) * q2SigmaMat := by
    rw [mat_nsElt_mul_nsElt_eq_fromBlocks (by decide), q2SigmaMat, fromBlocks_multiply,
      fromBlocks_multiply]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hD, neg_zero,
      sub_zero]
  apply Subtype.ext
  change q2EmbedMat 0 q2SigmaMat * q2EmbedMat 0 (mat 4 K (nsElt 2 * nsElt 3)) =
    q2EmbedMat 0 (mat 4 K (nsElt 2 * nsElt 3)) * q2EmbedMat 0 q2SigmaMat
  rw [← q2EmbedMat_mul, ← q2EmbedMat_mul, hM]

theorem q2SigmaPlane_sq_apply_three_two [CharP K 2] :
    (q2SigmaPlane (K := K) * q2SigmaPlane : Matrix (Fin 4) (Fin 4) K) 3 2 = 1 := by
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  simp [q2SigmaPlane, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transvection, Matrix.one_apply,
    h11]

theorem not_commute_q2SigmaE_sq [CharP K 2] (hK : Nat.card K = 2) :
    ¬ Commute (q2SigmaE (K := K) ^ 2) (q2Embed 0 hK (nsElt 2)) := by
  intro h
  have h1 : q2EmbedMat 0 (q2SigmaMat * q2SigmaMat * mat 4 K (nsElt 2)) =
      q2EmbedMat 0 (mat 4 K (nsElt 2) * (q2SigmaMat * q2SigmaMat)) := by
    have := congrArg (fun z : SpecialLinearGroup (Fin (2 * 4 + 0)) K =>
      (z : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) K)) h.eq
    simp only [pow_two, Matrix.SpecialLinearGroup.coe_mul] at this
    rw [q2EmbedMat_mul, q2EmbedMat_mul, q2EmbedMat_mul, q2EmbedMat_mul]
    exact this
  have h2 := congrFun (congrFun (q2EmbedMat_injective h1) (Sum.inl 3)) (Sum.inl 2)
  rw [mul_mat_nsElt_apply _ _ (inl_mem_coords 2),
    mat_nsElt_mul_apply_of_not_mem _ (by simp [mem_coords])] at h2
  rw [mat_nsElt_inl_inl, mat_nsElt_inr_inl] at h2
  simp only [q2SigmaMat, fromBlocks_multiply, add_zero,
    zero_add, fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, mul_zero, zero_mul] at h2
  rw [q2SigmaPlane_sq_apply_three_two] at h2
  exact zero_ne_one h2

end Sigma

section Swap

@[expose] def q2SwapEMat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  fromBlocks (inclMat (Equiv.swap (0 : Fin 4) 1)) 0 0 1

theorem inclMat_swap_transpose :
    (inclMat (K := K) (Equiv.swap (0 : Fin 4) 1))ᵀ = inclMat (Equiv.swap (0 : Fin 4) 1) := by
  ext i j
  simp only [transpose_apply, inclMat, of_apply]
  congr 1
  apply propext
  constructor <;> intro h <;> rw [h, Equiv.swap_apply_self]

theorem inclMat_swap_mul_self :
    inclMat (K := K) (Equiv.swap (0 : Fin 4) 1) * inclMat (Equiv.swap (0 : Fin 4) 1) = 1 :=
  calc _ = (inclMat (K := K) (Equiv.swap (0 : Fin 4) 1))ᵀ * inclMat (Equiv.swap (0 : Fin 4) 1) := by
        rw [inclMat_swap_transpose]
    _ = 1 := inclMat_transpose_mul (Equiv.swap (0 : Fin 4) 1).injective

theorem q2SwapEMat_mul_self : q2SwapEMat (K := K) * q2SwapEMat = 1 := by
  rw [q2SwapEMat, fromBlocks_multiply, inclMat_swap_mul_self]
  simp [fromBlocks_one]

theorem det_q2EmbedMat_q2SwapEMat (hK : Nat.card K = 2) :
    (q2EmbedMat 0 (q2SwapEMat (K := K))).det = 1 := by
  rw [det_q2EmbedMat]
  refine q2_eq_one_of_ne_zero hK fun h0 => ?_
  have h1 := congrArg Matrix.det (q2SwapEMat_mul_self (K := K))
  rw [det_mul, h0, zero_mul, det_one] at h1
  exact zero_ne_one h1

@[expose] noncomputable def q2SwapE (hK : Nat.card K = 2) :
    SpecialLinearGroup (Fin (2 * 4 + 0)) K :=
  ⟨q2EmbedMat 0 q2SwapEMat, det_q2EmbedMat_q2SwapEMat hK⟩

theorem q2SwapE_mem_q2Block (hK : Nat.card K = 2) :
    q2SwapE hK ∈ q2Block 0 K ({2, 3} : Finset (Fin 4)) := by
  refine q2EmbedMat_mem_q2Block rfl fun u v huv => ?_
  have hfix : ∀ {w : Fin 4 ⊕ Fin 4}, w ∈ planeCoords ({2, 3} : Finset (Fin 4)) →
      Equiv.swap (0 : Fin 4) 1 (planeOf w) = planeOf w := fun {w} hw => by
    rw [mem_planeCoords] at hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h | h <;> rw [h] <;> decide
  rcases u with i | i <;> rcases v with j | j <;>
    simp only [q2SwapEMat, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, ite_false]
  simp only [inclMat, of_apply]
  rcases huv with h | h
  · have h' := hfix h
    simp only [planeOf_inl] at h'
    congr 1
    apply propext
    constructor
    · intro hij
      rw [← h', hij, Equiv.swap_apply_self]
    · intro hij
      rw [← hij, h']
  · have h' := hfix h
    simp only [planeOf_inl] at h'
    rw [h']

theorem commute_q2SwapE_q2Embed_nsElt_three (hK : Nat.card K = 2) :
    Commute (q2SwapE hK) (q2Embed 0 hK (nsElt (K := K) (3 : Fin 4))) := by
  have hcb : q2Embed 0 hK (nsElt (K := K) (3 : Fin 4)) ∈
      blockSpecialLinear (planeCoordsQ2 0 ({3} : Finset (Fin 4))) := by
    rw [planeCoordsQ2_singleton,
      show nsElt (K := K) (3 : Fin 4) = longBlock K 4 3 zThreeSL from rfl,
      q2Embed_longBlock hK, ← LinearPilot.range_pairEmbed (q2PlaneNe 3)]
    exact ⟨_, rfl⟩
  have hdisj : Disjoint (planeCoordsQ2 0 ({2, 3} : Finset (Fin 4)))ᶜ
      (planeCoordsQ2 0 ({3} : Finset (Fin 4))) :=
    disjoint_compl_left.mono_right (planeCoordsQ2_mono (by simp))
  exact LinearPilot.commute_blockSpecialLinear_of_disjoint hdisj (q2SwapE_mem_q2Block hK) hcb

theorem q2Graph_inv_mul_q2SwapE [CharP K 2] (hK : Nat.card K = 2) :
    (q2Graph 0 hK (q2SwapE hK))⁻¹ * q2SwapE hK =
      q2Embed 0 hK (permSp K (Equiv.swap (0 : Fin 4) 1)) := by
  have hneg : ∀ A : Matrix (Fin 4) (Fin 4) K, -A = A := fun A => by
    ext i j
    exact CharTwo.neg_eq _
  apply Subtype.ext
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_mul, coe_q2Graph, inv_inv, coe_q2Embed, mat_permSp]
  change q2GramMat 0 * (q2EmbedMat 0 q2SwapEMat)ᵀ * q2GramMat 0 * q2EmbedMat 0 q2SwapEMat =
    q2EmbedMat 0 (spIncl _)
  rw [q2GramMat, q2EmbedMat_transpose, ← q2EmbedMat_mul, ← q2EmbedMat_mul, ← q2EmbedMat_mul]
  congr 1
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, q2SwapEMat, spIncl,
    fromBlocks_transpose, inclMat_swap_transpose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_multiply]
  simp [hneg]

theorem permSp_swap_mem_spBlock :
    permSp K (Equiv.swap (0 : Fin 4) 1) ∈ spBlock K ({0, 1} : Finset (Fin 4)) := by
  rw [mem_spBlock]
  intro a b hab
  rw [mat_permSp, spIncl_apply, Matrix.one_apply]
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp_all [mem_planeCoords, Equiv.swap_apply_def]

end Swap

end CFSG.SeitzReduction.SymplecticPilot
