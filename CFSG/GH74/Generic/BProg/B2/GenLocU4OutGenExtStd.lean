module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenStar
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenSu2b
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenDb

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Phan

namespace GenLocU4Out

open GenLocU4Basic GenLocU4ExtBd

variable {K : Type} [Field K] {p f : ℕ}

theorem mD_eq_bd : (mD : Matrix (Fin 4) (Fin 4) K) = bd 1 Y2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mD, bd, Y2, Matrix.diagonal]

theorem bd_map_pow {q : ℕ} (hq : q ≠ 0) (B B' : Matrix (Fin 2) (Fin 2) K) :
    (bd B B').map (· ^ q) = bd (B.map (· ^ q)) (B'.map (· ^ q)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, zero_pow hq]

theorem bd_mul_blockMat2 (M M' Y Y' : Matrix (Fin 2) (Fin 2) K) (h : M' * Y = Y' * M') :
    bd M M' * blockMat 4 2 Y = blockMat 4 2 Y' * bd M M' := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ext a b
  fin_cases a <;> fin_cases b <;> simp [bd, blockMat_apply, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | linear_combination e00 | linear_combination e01 | linear_combination e10 | linear_combination e11

theorem A0_eq : (Y2 * J2 : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Y2, J2, Matrix.mul_apply, Matrix.diagonal]

theorem typeIII_of_comm {X Xb : Matrix (Fin 2) (Fin 2) K} (hb : Xb = J2 * X * J2')
    (hc : (Y2 * J2) * X = X * (Y2 * J2)) : Y2 * Xb * Y2 = X := by
  rw [hb]
  calc Y2 * (J2 * X * J2') * Y2 = (Y2 * J2 * X) * J2' * Y2 := by simp only [Matrix.mul_assoc]
    _ = (X * (Y2 * J2)) * J2' * Y2 := by rw [hc]
    _ = X * Y2 * (J2 * J2') * Y2 := by simp only [Matrix.mul_assoc]
    _ = X := by rw [J2_mul, Matrix.mul_one, Matrix.mul_assoc, Y2_mul, Matrix.mul_one]

theorem typeIV_of_comm {X Xb N Nb : Matrix (Fin 2) (Fin 2) K} (hX : Xb = J2 * X * J2') (hN : Nb = J2 * N * J2')
    (hc : (Y2 * J2 * N) * X = X * (Y2 * J2 * N)) : (Y2 * Nb) * Xb = X * (Y2 * Nb) := by
  rw [hX, hN]
  calc Y2 * (J2 * N * J2') * (J2 * X * J2') = (Y2 * J2 * N) * (J2' * J2) * X * J2' := by
        simp only [Matrix.mul_assoc]
    _ = (Y2 * J2 * N) * X * J2' := by rw [J2_mul', Matrix.mul_one]
    _ = (X * (Y2 * J2 * N)) * J2' := by rw [hc]
    _ = X * (Y2 * (J2 * N * J2')) := by simp only [Matrix.mul_assoc]

theorem anti_of_rel {N Nb : Matrix (Fin 2) (Fin 2) K} (hN : Nb = J2 * N * J2')
    (hrel : N * Y2 = -(Y2 * Nb)) : (Y2 * J2) * N = -(N * (Y2 * J2)) := by
  rw [hN] at hrel
  have e : N * (Y2 * J2) = -((Y2 * J2) * N) := by
    calc N * (Y2 * J2) = (N * Y2) * J2 := by rw [Matrix.mul_assoc]
      _ = -(Y2 * (J2 * N * J2')) * J2 := by rw [hrel]
      _ = -(Y2 * J2 * N * (J2' * J2)) := by simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = -((Y2 * J2) * N) := by rw [J2_mul', Matrix.mul_one]
  rw [e, neg_neg]

theorem ext_class_std
    [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq4 : p ^ f % 4 = 1)
    (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (ξ' : Matrix (Fin 4) (Fin 4) K)
    (hξu : IsUnitaryU (p ^ f) ξ') (hξsq : ξ' * ξ' = -1)
    (hcomm : ξ' * Matrix.diagonal ![-1, -1, 1, 1] = Matrix.diagonal ![-1, -1, 1, 1] * ξ')
    (hrel : ξ' * (mD : Matrix (Fin 4) (Fin 4) K) = -((mD : Matrix (Fin 4) (Fin 4) K) * ξ'.map (· ^ (p ^ f))))
    (h1 : ∀ g, FixOut (p ^ f) (mD : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (h2 : ∀ g, FixIn ξ' g → g ∈ Γ)
    (h3 : ∀ g, FixOut (p ^ f) ((mD : Matrix (Fin 4) (Fin 4) K) * ξ'.map (· ^ (p ^ f))) g → g ∈ Γ) :
    Γ = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  have h2' : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  obtain ⟨N0, N2, hbd⟩ := exists_bd_of_comm h2' ξ' hcomm
  subst hbd
  have hN2u : (N2.map (· ^ (p ^ f)))ᵀ * N2 = 1 := by
    have e : bd ((N0.map (· ^ (p ^ f)))ᵀ * N0) ((N2.map (· ^ (p ^ f)))ᵀ * N2) = bd 1 1 := by
      rw [← bd_unitary hq0, bd_one]
      exact hξu
    exact (bd_inj e).2
  have hN2sq : N2 * N2 = -1 := by
    have e : bd (N0 * N0) (N2 * N2) = bd (-1) (-1) := by
      rw [← bd_mul, hξsq, ← bd_neg, bd_one]
    exact (bd_inj e).2
  have hrel2 : N2 * Y2 = -(Y2 * N2.map (· ^ (p ^ f))) := by
    rw [mD_eq_bd, bd_map_pow hq0, bd_mul, bd_mul, bd_neg] at hrel
    exact (bd_inj hrel).2
  have hN2tr : N2 1 1 = -N2 0 0 := GenLocU4ExtBd.tr_zero hq4 h2' N2 hN2sq hN2u
  have hN2det : N2.det = 1 := by
    have e00 := congrFun (congrFun hN2sq 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.one_apply_eq] at e00
    rw [Matrix.det_fin_two, hN2tr]
    linear_combination (-1 : K) * e00
  have hNs : ∀ lam : K, N2 ≠ lam • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro lam hlam
    have e0 : N2 0 0 = lam := by rw [hlam]; simp
    have e1 : N2 1 1 = lam := by rw [hlam]; simp
    have hl0 : lam = 0 := by
      have : (2 : K) * lam = 0 := by linear_combination (-1 : K) * e1 + (-1 : K) * e0 + hN2tr
      exact (mul_eq_zero.1 this).resolve_left h2'
    have hz : N2 * N2 = 0 := by rw [hlam, hl0]; simp
    rw [hN2sq] at hz
    have := congrFun (congrFun hz 0) 0
    simp at this
  have hbarN : N2.map (· ^ (p ^ f)) = J2 * N2 * J2' :=
    GenLocU4Gen.su2_map_bar (GenLocU4Aux.su2Mk (p := p) (f := f) N2 hN2det hN2u)
  have hanti : (Y2 * J2) * N2 = -(N2 * (Y2 * J2)) := anti_of_rel hbarN hrel2
  have hA0 : (Y2 * J2 : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := A0_eq
  have hA0u : ((Y2 * J2 : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ * (Y2 * J2) = 1 := by
    rw [hA0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, zero_pow hq0]
  have hA0sq : (Y2 * J2 : Matrix (Fin 2) (Fin 2) K) * (Y2 * J2) = 1 := by
    rw [hA0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hA0det : ∀ lam : K, lam ^ (p ^ f) * lam = 1 → lam * lam ≠ (Y2 * J2 : Matrix (Fin 2) (Fin 2) K).det := by
    intro lam hlam hsq
    rw [hA0] at hsq
    simp [Matrix.det_fin_two_of] at hsq
    exact GenLocU4ExtMu.not_isSqM_neg_one hq4 h2' ⟨lam, by rw [pow_succ]; exact hlam, hsq⟩
  have hP : (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    simp [Matrix.map_one, zero_pow hq0]
  have hblock : ∀ x : Su K p f 2, GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 2 x ∈ Γ := by
    refine su2_gen_of_anti hp2 hK hq4 (GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 2) Γ (Y2 * J2) N2
      hA0u hA0sq hA0det hN2det hN2u hN2sq hNs hanti ?_ ?_ ?_
    · intro x hx
      refine h1 _ (fixOut_block (![1, 1, 1, -1]) pmM 2 _ _ (coe_frameBlock_one hK hP 2 x)
        (Or.inr ⟨by simp [GenLocU4Gen.idx4], ?_⟩))
      exact typeIII_of_comm (GenLocU4Gen.su2_map_bar x) hx
    · intro x hx
      refine h2 _ ?_
      unfold FixIn
      rw [coe_frameBlock_one hK hP 2 x]
      exact bd_mul_blockMat2 N0 N2 _ _ hx
    · intro x hx
      refine h3 _ ?_
      unfold FixOut
      rw [coe_frameBlock_one hK hP 2 x, map_blockMat_pow, mD_eq_bd, bd_map_pow hq0, bd_mul]
      exact bd_mul_blockMat2 _ _ _ _ (typeIV_of_comm (GenLocU4Gen.su2_map_bar x) hbarN hx)
  have hB2 : ∀ g, GenLocU4Gen.InBlock (p ^ f) (1 : GL (Fin 4) K) 2 g → g ∈ Γ := by
    intro g hg
    obtain ⟨x, rfl⟩ := GenLocU4Gen.exists_frameBlock_of_inBlock hK (1 : GL (Fin 4) K) hP 2 g hg
    exact hblock x
  exact eq_top_of_SO_star hp hp2 hK hq4 Γ (-1) hq.add_one.neg_one_pow
    (fun μ hμ hsq => GenLocU4ExtMu.not_isSqM_neg_one hq4 h2' ⟨μ, hμ, hsq⟩) (fun g hg => h1 g hg) hB2

end GenLocU4Out

end CFSG.GH74.Generic.BProg.B2
