module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

variable {N ε : ℕ} {K : Type} [Field K]

theorem sum_mul_par_eq_zero [CharP K 2] (f : Fin N ⊕ Fin N → K) :
    ∑ u, f u * f (par u) = 0 := by
  rw [Fintype.sum_sum_type]
  simp only [par_inl, par_inr]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [mul_comm (f (Sum.inr p)), ← two_mul, CharTwo.two_eq_zero, zero_mul]

theorem transpose_mul_q2GramMat_mul_apply [CharP K 2]
    (X : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) (a b : Fin (2 * N + ε)) :
    (Xᵀ * q2GramMat ε * X : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a b =
      ∑ w, X (q2Coord N ε (Sum.map par id w)) a * X (q2Coord N ε w) b := by
  have h1 : ∀ d, (Xᵀ * q2GramMat ε : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a d =
      X (q2Par N ε d) a := by
    intro d
    rw [Matrix.mul_apply, Finset.sum_eq_single (q2Par N ε d)]
    · rw [transpose_apply, q2GramMat_apply, ite_eq_left (q2Par_q2Par d).symm, mul_one]
    · intro c _ hc
      rw [q2GramMat_apply, ite_eq_right (fun h => hc (by rw [h, q2Par_q2Par])), mul_zero]
    · simp
  rw [Matrix.mul_apply, ← (q2Coord N ε).sum_comp]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [h1, q2Par_q2Coord]

theorem sum_fin_le_one {ε : ℕ} (hε : ε ≤ 1) (g : Fin ε → K) (e : Fin ε) :
    ∑ e', g e' = g e :=
  Finset.sum_eq_single e (fun e' _ he' => absurd (Fin.ext (by have := e.2; have := e'.2; omega))
    he') (fun h => absurd (Finset.mem_univ e) h)

theorem exists_eq_q2Embed_of_q2Graph_eq [CharP K 2] (hK : Nat.card K = 2) (hε : ε ≤ 1)
    {x : SpecialLinearGroup (Fin (2 * N + ε)) K} (hx : q2Graph ε hK x = x) :
    ∃ y : StatedSp N K, q2Embed ε hK y = x := by
  have hE := (q2Graph_eq_self_iff hK x).1 hx
  set X : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K :=
    (x : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) with hX
  have hEa : ∀ w w' : (Fin N ⊕ Fin N) ⊕ Fin ε,
      ∑ c, X (q2Coord N ε (Sum.map par id c)) (q2Coord N ε w) * X (q2Coord N ε c)
        (q2Coord N ε w') = q2GramMat ε (q2Coord N ε w) (q2Coord N ε w') := by
    intro w w'
    rw [← transpose_mul_q2GramMat_mul_apply, hE]
  have hP : ∀ w w' : (Fin N ⊕ Fin N) ⊕ Fin ε, q2GramMat (K := K) ε (q2Coord N ε w)
      (q2Coord N ε w') = if w' = Sum.map par id w then 1 else 0 := by
    intro w w'
    rw [q2GramMat_apply, q2Par_q2Coord]
    simp only [(q2Coord N ε).injective.eq_iff]
  have hsplit : ∀ w w' : (Fin N ⊕ Fin N) ⊕ Fin ε,
      ∑ c, X (q2Coord N ε (Sum.map par id c)) (q2Coord N ε w) * X (q2Coord N ε c)
        (q2Coord N ε w') =
      ∑ u, X (q2Coord N ε (Sum.inl (par u))) (q2Coord N ε w) *
          X (q2Coord N ε (Sum.inl u)) (q2Coord N ε w') +
        ∑ e, X (q2Coord N ε (Sum.inr e)) (q2Coord N ε w) *
          X (q2Coord N ε (Sum.inr e)) (q2Coord N ε w') := by
    intro w w'
    rw [Fintype.sum_sum_type]
    rfl
  have hC : ∀ (e : Fin ε) (v : Fin N ⊕ Fin N),
      X (q2Coord N ε (Sum.inr e)) (q2Coord N ε (Sum.inl v)) = 0 := by
    intro e v
    have h1 := hEa (Sum.inl v) (Sum.inl v)
    rw [hsplit, hP, ite_eq_right (by
      simp only [Sum.map_inl, Sum.inl.injEq]
      rcases v with v | v <;> simp [par]), sum_fin_le_one hε _ e] at h1
    have h0 : ∑ u, X (q2Coord N ε (Sum.inl (par u))) (q2Coord N ε (Sum.inl v)) *
        X (q2Coord N ε (Sum.inl u)) (q2Coord N ε (Sum.inl v)) = 0 := by
      have := sum_mul_par_eq_zero (K := K)
        (fun u => X (q2Coord N ε (Sum.inl u)) (q2Coord N ε (Sum.inl v)))
      rw [← this]
      refine Finset.sum_congr rfl fun u _ => ?_
      ring
    rw [h0, zero_add, ← sq] at h1
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
  set A : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K :=
    fun u v => X (q2Coord N ε (Sum.inl u)) (q2Coord N ε (Sum.inl v)) with hA
  have hAsp : Aᵀ * gram K N * A = gram K N := by
    ext u v
    rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply]
    have h1 := hEa (Sum.inl u) (Sum.inl v)
    rw [hsplit, hP] at h1
    simp only [hC, zero_mul, Finset.sum_const_zero, add_zero] at h1
    have hsgn : ∀ c : Fin N ⊕ Fin N, sgn K c = 1 := by
      intro c
      rcases c with c | c
      · rfl
      · simp [sgn, CharTwo.neg_eq]
    simp only [hsgn, one_mul]
    rw [← (Equiv.sumComm (Fin N) (Fin N)).sum_comp]
    have hsw : ∀ c : Fin N ⊕ Fin N, (Equiv.sumComm (Fin N) (Fin N)) c = par c := fun _ => rfl
    simp only [hsw, par_par]
    rw [show (∑ c, A (par c) u * A c v) = ∑ c, X (q2Coord N ε (Sum.inl (par c)))
      (q2Coord N ε (Sum.inl u)) * X (q2Coord N ε (Sum.inl c)) (q2Coord N ε (Sum.inl v)) from rfl,
      h1]
    simp only [Sum.map_inl, Sum.inl.injEq]
  set y : StatedSp N K := ofSymplecticMat A hAsp with hy
  have hmy : mat N K y = A := mat_ofSymplecticMat A hAsp
  have hB : ∀ (u : Fin N ⊕ Fin N) (e : Fin ε),
      X (q2Coord N ε (Sum.inl u)) (q2Coord N ε (Sum.inr e)) = 0 := by
    intro u e
    set b : Fin N ⊕ Fin N → K := fun c => X (q2Coord N ε (Sum.inl (par c)))
      (q2Coord N ε (Sum.inr e)) with hb
    have hbA : b ᵥ* A = 0 := by
      ext v
      have h1 := hEa (Sum.inl v) (Sum.inr e)
      rw [hsplit, hP, ite_eq_right (by simp)] at h1
      simp only [hC, zero_mul, Finset.sum_const_zero, add_zero] at h1
      rw [vecMul, dotProduct, Pi.zero_apply, ← (Equiv.sumComm (Fin N) (Fin N)).sum_comp]
      have hsw : ∀ c : Fin N ⊕ Fin N, (Equiv.sumComm (Fin N) (Fin N)) c = par c := fun _ => rfl
      simp only [hsw, hb, hA, par_par]
      rw [← h1]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    have hAA : A * mat N K y⁻¹ = 1 := by rw [← hmy, ← map_mul, mul_inv_cancel, map_one]
    have hb0 : b = 0 := by
      rw [← vecMul_one b, ← hAA, ← vecMul_vecMul, hbA, zero_vecMul]
    have := congrFun hb0 (par u)
    simpa [hb, par_par] using this
  have hD : ∀ e : Fin ε, X (q2Coord N ε (Sum.inr e)) (q2Coord N ε (Sum.inr e)) = 1 := by
    intro e
    have h1 := hEa (Sum.inr e) (Sum.inr e)
    rw [hsplit, hP, ite_eq_left (by simp)] at h1
    simp only [hB, mul_zero, Finset.sum_const_zero, zero_add] at h1
    rw [sum_fin_le_one hε _ e, ← sq] at h1
    have h2 : (X (q2Coord N ε (Sum.inr e)) (q2Coord N ε (Sum.inr e)) + 1) ^ 2 = 0 := by
      rw [add_sq, h1, mul_one, one_pow, CharTwo.two_eq_zero, zero_mul, add_zero,
        CharTwo.add_self_eq_zero]
    have h3 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
    rw [← CharTwo.neg_eq (X _ _), ← add_eq_zero_iff_neg_eq]
    exact h3
  refine ⟨y, Subtype.ext ?_⟩
  ext a b
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
  rw [q2Embed_apply_q2Coord, hmy]
  rcases w with u | e <;> rcases w' with v | e'
  · rfl
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    exact (hB u e').symm
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    exact (hC e v).symm
  · obtain rfl : e = e' := Fin.ext (by have := e.2; have := e'.2; omega)
    rw [fromBlocks_apply₂₂, Matrix.one_apply_eq]
    exact (hD e).symm

end CFSG.SeitzReduction.SymplecticPilot
