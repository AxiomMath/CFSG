module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGData

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Matrix CFSG.EvenSporadicStandard.TwoHS

@[expose] def mTau : SoMat5 := !![4, 0, 0, 0, 0; 0, 4, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0;
  0, 0, 0, 0, 1]

@[expose] def mSf : SoMat5 := !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 4, 0, 0; 0, 0, 0, 4, 0;
  0, 0, 0, 0, 4]

@[expose] def mY : SoMat5 := !![2, 0, 0, 0, 0; 0, 3, 0, 0, 0; 0, 0, 0, 2, 0; 0, 0, 3, 0, 0;
  0, 0, 0, 0, 4]

@[expose] def mC5 : SoMat5 := !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 4, 2;
  0, 0, 0, 1, 4]

theorem pgTau1_eq : pgTau1 = mTau := by decide

theorem pgSf0_eq : pgSf0 = mSf := by decide

theorem pgY_eq : pgR0 * pgS1 = mY := by decide

set_option maxRecDepth 100000 in
theorem mC5_so : IsSO5 mC5 := by decide

set_option maxRecDepth 100000 in
theorem mC5_pow : mC5 ^ 5 = 1 := by decide

theorem pgSf0_comm : pgSf0 * pgTau1 = pgTau1 * pgSf0 := by decide

theorem pgY_comm : pgR0 * pgS1 * pgTau1 = pgTau1 * (pgR0 * pgS1) := by decide

theorem mC5_comm : mC5 * pgTau1 = pgTau1 * mC5 := by decide

theorem commutant_diag (A : SoMat5) (h0 : A * mTau = mTau * A) (h1 : A * mSf = mSf * A)
    (h2 : A * mY = mY * A) (h3 : A * mC5 = mC5 * A) :
    (∀ i j : Fin 5, i ≠ j → A i j = 0) ∧ A 0 0 = A 1 1 ∧ A 2 2 = A 3 3 ∧ A 3 3 = A 4 4 := by
  have e0 : ∀ i j : Fin 5, (A * mTau) i j = (mTau * A) i j := fun i j => by rw [h0]
  have e1 : ∀ i j : Fin 5, (A * mSf) i j = (mSf * A) i j := fun i j => by rw [h1]
  have e2 : ∀ i j : Fin 5, (A * mY) i j = (mY * A) i j := fun i j => by rw [h2]
  have e3 : ∀ i j : Fin 5, (A * mC5) i j = (mC5 * A) i j := fun i j => by rw [h3]
  simp [mTau, mSf, mY, mC5, Matrix.mul_apply, Fin.sum_univ_five, Fin.forall_fin_succ] at e0 e1 e2 e3
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> grind
  · grind
  · grind
  · grind

theorem zmod_five_sq_cases : ∀ a b : ZMod 5, a * a = 1 → b * b = 1 → a * a * b * b * b = 1 →
    (a = 1 ∨ a = 4) ∧ b = 1 := by
  decide

theorem eq_one_or_tau1_of_commute (x : PGSp45) (hx : x * x = 1)
    (h0 : x * mkPG pgTau1 pgTau1_so = mkPG pgTau1 pgTau1_so * x)
    (h1 : x * mkPG pgSf0 pgSf0_so = mkPG pgSf0 pgSf0_so * x)
    (h2 : x * (mkPG pgR0 pgR0_so * mkPG pgS1 pgS1_so) =
      (mkPG pgR0 pgR0_so * mkPG pgS1 pgS1_so) * x)
    (h3 : x * mkPG mC5 mC5_so = mkPG mC5 mC5_so * x) :
    x = 1 ∨ x = mkPG pgTau1 pgTau1_so := by
  have m0 : x.1.1 * mTau = mTau * x.1.1 := by
    have := congrArg (fun z : PGSp45 => z.1.1) h0
    simp only [pg_mul_val, mkPG_val] at this
    rwa [pgTau1_eq] at this
  have m1 : x.1.1 * mSf = mSf * x.1.1 := by
    have := congrArg (fun z : PGSp45 => z.1.1) h1
    simp only [pg_mul_val, mkPG_val] at this
    rwa [pgSf0_eq] at this
  have m2 : x.1.1 * mY = mY * x.1.1 := by
    have := congrArg (fun z : PGSp45 => z.1.1) h2
    simp only [pg_mul_val, mkPG_val] at this
    rwa [pgY_eq] at this
  have m3 : x.1.1 * mC5 = mC5 * x.1.1 := by
    have := congrArg (fun z : PGSp45 => z.1.1) h3
    simpa only [pg_mul_val, mkPG_val] using this
  obtain ⟨hoff, h01, h23, h34⟩ := commutant_diag x.1.1 m0 m1 m2 m3
  have hAA : x.1.1 * x.1.1 = 1 := by
    have := congrArg (fun z : PGSp45 => z.1.1) hx
    simpa only [pg_mul_val, pg_one_val] using this
  have hdet : x.1.1.det = 1 := x.2.2
  obtain ⟨a, b, hAeq⟩ : ∃ a b : ZMod 5, x.1.1 = Matrix.diagonal ![a, a, b, b, b] := by
    refine ⟨x.1.1 0 0, x.1.1 2 2, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp [← h01, h23, ← h34]
    · simp [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  rw [hAeq] at hAA hdet
  have ha : a * a = 1 := by
    have := congrFun (congrFun hAA 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_five] using this
  have hb : b * b = 1 := by
    have := congrFun (congrFun hAA 2) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_five] using this
  have hd : a * a * b * b * b = 1 := by
    simpa [Matrix.det_diagonal, Fin.prod_univ_five] using hdet
  obtain ⟨hab, rfl⟩ := zmod_five_sq_cases a b ha hb hd
  rcases hab with rfl | rfl
  · left
    apply pg_ext
    rw [hAeq, pg_one_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  · right
    apply pg_ext
    rw [hAeq, mkPG_val, pgTau1_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, mTau]

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
