module

public import CFSG.GH74.Filter.ClassicalOdd.Basic
public import CFSG.GH74.Filter.Statements
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.GH74.Filter.ClassicalOdd

open CFSG.Assembly.LowTwoRank Matrix

section Plane

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def planeDiag (X : ι → Matrix (Fin 2) (Fin 2) F) : Matrix (ι ⊕ ι) (ι ⊕ ι) F :=
  fromBlocks (diagonal fun i => X i 0 0) (diagonal fun i => X i 0 1)
    (diagonal fun i => X i 1 0) (diagonal fun i => X i 1 1)

theorem planeDiag_mul (X Y : ι → Matrix (Fin 2) (Fin 2) F) :
    planeDiag X * planeDiag Y = planeDiag (fun i => X i * Y i) := by
  rw [planeDiag, planeDiag, planeDiag, fromBlocks_multiply]
  simp only [diagonal_mul_diagonal, ← diagonal_add, mul_apply, Fin.sum_univ_two]

omit [Fintype ι] in
theorem planeDiag_one : planeDiag (fun _ : ι => (1 : Matrix (Fin 2) (Fin 2) F)) = 1 := by
  rw [planeDiag, ← fromBlocks_one]
  simp [diagonal_zero]

theorem symplectic_fromBlocks_diagonal (a b c d : ι → F) (h : ∀ i, a i * d i - b i * c i = 1) :
    (fromBlocks (diagonal a) (diagonal b) (diagonal c) (diagonal d))ᵀ * fromBlocks 0 1 (-1) 0 *
      fromBlocks (diagonal a) (diagonal b) (diagonal c) (diagonal d) = fromBlocks 0 1 (-1) 0 := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [diagonal_transpose, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, diagonal_mul_diagonal]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
  all_goals
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.zero_apply, Matrix.one_apply_eq,
        diagonal_apply_eq]
      first | ring1 | linear_combination h i | linear_combination (-1 : F) * h i
    · simp [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem planeDiag_symplectic (X : ι → Matrix (Fin 2) (Fin 2) F) (hX : ∀ i, (X i).det = 1) :
    (planeDiag X)ᵀ * fromBlocks 0 1 (-1) 0 * planeDiag X = fromBlocks 0 1 (-1) 0 :=
  symplectic_fromBlocks_diagonal _ _ _ _ fun i => by
    have := hX i
    rwa [Matrix.det_fin_two] at this

theorem planeDiag_eq_scalar (X : ι → Matrix (Fin 2) (Fin 2) F) (c : F)
    (h : planeDiag X = scalar (ι ⊕ ι) c) (i : ι) : X i = scalar (Fin 2) c := by
  have h00 := congrFun (congrFun h (Sum.inl i)) (Sum.inl i)
  have h01 := congrFun (congrFun h (Sum.inl i)) (Sum.inr i)
  have h10 := congrFun (congrFun h (Sum.inr i)) (Sum.inl i)
  have h11 := congrFun (congrFun h (Sum.inr i)) (Sum.inr i)
  simp [planeDiag, scalar_apply] at h00 h01 h10 h11
  ext a b
  fin_cases a <;> fin_cases b <;> simp [scalar_apply, h00, h01, h10, h11]

@[expose] def alphaSp (ρ : Q8 →* Matrix (Fin 2) (Fin 2) F) (ι : Type*) [Fintype ι]
    [DecidableEq ι] : (ι → Q8) →* Matrix (ι ⊕ ι) (ι ⊕ ι) F where
  toFun g := planeDiag fun i => ρ (g i)
  map_one' := by
    simp only [Pi.one_apply, map_one]
    exact planeDiag_one
  map_mul' g h := by
    rw [planeDiag_mul]
    simp only [Pi.mul_apply, map_mul]

end Plane

theorem not_gen4_Sp {F : Type} [Field F] (Q : QuatRep F) {n : ℕ} (hn : 3 ≤ n) :
    ¬ Gen4 (StatedProj (StatedSp n F)) := by
  have hV : ∀ x : V4, x ^ 2 = 1 := by decide
  refine not_gen4_statedProj (A := Fin n → V4) (alphaSp Q.ρ (Fin n)).toHomUnits (fun k => ?_)
    (MonoidHom.compLeft q8Frattini (Fin n)) ?_ (fun a b => funext fun i => mul_comm (a i) (b i))
    (fun a => funext fun i => hV (a i)) ?_ ?_
  · exact Subgroup.subset_closure (planeDiag_symplectic _ fun i => Q.det_eq _)
  · intro b
    exact ⟨fun i => (q8Frattini_surjective (b i)).choose,
      funext fun i => (q8Frattini_surjective (b i)).choose_spec⟩
  · rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, card_V4]
    calc 2 ^ 4 < 4 ^ 3 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  · intro k c h
    funext i
    exact (Q.scalar_eq _ _ (planeDiag_eq_scalar (fun i => Q.ρ (k i)) c h i)).1

end CFSG.GH74.Filter.ClassicalOdd

namespace CFSG.GH74.Filter

open CFSG.GH74.Filter.ClassicalOdd

theorem t_PSp_odd_ge_three : S_PSp_odd_ge_three := by
  intro G _ _ n p f hp2 hn hm
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨Q⟩ := exists_quatRep hK2
  exact not_gen4_of_mulEquiv e.symm (not_gen4_Sp Q hn)

end CFSG.GH74.Filter
