module

public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.OrthFrame

public section

namespace CFSG.SectionRank.ClassicalOdd

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K] {n : ℕ}

@[expose] def oddData (hn : 3 ≤ n) : OrthData (Fin n ⊕ Fin n ⊕ Unit) K where
  X i := Sum.inl (Fin.castLE hn i)
  Y i := Sum.inr (Sum.inl (Fin.castLE hn i))
  w := Pi.single (Sum.inr (Sum.inr ())) 1
  β := (2 : K) • LinearMap.proj (Sum.inr (Sum.inr ()))
  injX _ _ h := Fin.castLE_injective hn (Sum.inl_injective h)
  injY _ _ h := Fin.castLE_injective hn (Sum.inl_injective (Sum.inr_injective h))
  X_ne_Y _ _ := Sum.inl_ne_inr
  w_X _ := by simp
  w_Y _ := by simp
  β_X _ := by simp
  β_Y _ := by simp
  β_w := by simp

theorem quadOdd_X (hn : 3 ≤ n) (v : Fin n ⊕ Fin n ⊕ Unit → K) (i : Fin 3) (a : K) :
    StatedQuadOdd n K (v + Pi.single ((oddData (K := K) hn).X i) a) =
      StatedQuadOdd n K v + a * v ((oddData (K := K) hn).Y i) := by
  simp only [StatedQuadOdd, oddData, Pi.add_apply, Pi.single_apply, Sum.inl.injEq,
    reduceCtorEq, ↓reduceIte, add_zero, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ]
  ring

theorem quadOdd_w (hn : 3 ≤ n) (v : Fin n ⊕ Fin n ⊕ Unit → K) (s : K) :
    StatedQuadOdd n K (v + s • (oddData hn).w) =
      StatedQuadOdd n K v + s * (oddData hn).β v + s ^ 2 := by
  simp only [StatedQuadOdd, oddData, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
    Sum.inr.injEq, reduceCtorEq, ↓reduceIte, smul_eq_mul, mul_zero, add_zero, mul_one,
    LinearMap.smul_apply, LinearMap.proj_apply]
  ring

theorem quadOdd_d (hn : 3 ≤ n) (i : Fin 3) (v : Fin n ⊕ Fin n ⊕ Unit → K) :
    StatedQuadOdd n K ((oddData hn).dL i v) = StatedQuadOdd n K v := by
  simp only [StatedQuadOdd, OrthData.dL_apply, OrthData.dsign, oddData, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, or_false, false_or, ↓reduceIte, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem four_mul_le_pRank_omegaOdd (hn : 3 ≤ n) [Finite K] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    4 * f ≤ pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n K)))) :=
  (oddData hn).four_mul_le_pRank hp2 hK _ (quadOdd_X hn) (quadOdd_w hn) (quadOdd_d hn)

theorem castLE_ne_three (hn : 4 ≤ n) (i : Fin 3) :
    Fin.castLE (by omega : 3 ≤ n) i ≠ ⟨3, by omega⟩ := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castLE] at this
  omega

abbrev three (hn : 4 ≤ n) : Fin n := ⟨3, by omega⟩

@[expose] def plusData (hn : 4 ≤ n) : OrthData (Fin n ⊕ Fin n) K where
  X i := Sum.inl (Fin.castLE (by omega) i)
  Y i := Sum.inr (Fin.castLE (by omega) i)
  w := Pi.single (Sum.inl (three hn)) 1 + Pi.single (Sum.inr (three hn)) 1
  β := LinearMap.proj (R := K) (φ := fun _ => K) (Sum.inl (three hn)) +
    LinearMap.proj (R := K) (φ := fun _ => K) (Sum.inr (three hn))
  injX _ _ h := Fin.castLE_injective _ (Sum.inl_injective h)
  injY _ _ h := Fin.castLE_injective _ (Sum.inr_injective h)
  X_ne_Y _ _ := Sum.inl_ne_inr
  w_X i := by simp [castLE_ne_three hn i]
  w_Y i := by simp [castLE_ne_three hn i]
  β_X i := by simp [castLE_ne_three hn i]
  β_Y i := by simp [castLE_ne_three hn i]
  β_w := by
    simp
    norm_num

theorem quadPlus_X (hn : 4 ≤ n) (v : Fin n ⊕ Fin n → K) (i : Fin 3) (a : K) :
    StatedQuadPlus n K (v + Pi.single ((plusData (K := K) hn).X i) a) =
      StatedQuadPlus n K v + a * v ((plusData (K := K) hn).Y i) := by
  simp only [StatedQuadPlus, plusData, Pi.add_apply, Pi.single_apply, Sum.inl.injEq,
    reduceCtorEq, ↓reduceIte, add_zero, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ]

theorem quadPlus_w (hn : 4 ≤ n) (v : Fin n ⊕ Fin n → K) (s : K) :
    StatedQuadPlus n K (v + s • (plusData hn).w) =
      StatedQuadPlus n K v + s * (plusData hn).β v + s ^ 2 := by
  set u : Fin n ⊕ Fin n → K := v + s • (plusData hn).w with hu
  have key : ∑ j, (u (Sum.inl j) * u (Sum.inr j) - v (Sum.inl j) * v (Sum.inr j)) =
      s * (plusData hn).β v + s ^ 2 := by
    rw [Finset.sum_eq_single (three hn)]
    · simp [hu, plusData]
      ring
    · intro j _ hj
      simp [hu, plusData, hj]
    · simp
  rw [Finset.sum_sub_distrib] at key
  rw [StatedQuadPlus, StatedQuadPlus]
  linear_combination key

theorem quadPlus_d (hn : 4 ≤ n) (i : Fin 3) (v : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n K ((plusData hn).dL i v) = StatedQuadPlus n K v := by
  simp only [StatedQuadPlus, OrthData.dL_apply, OrthData.dsign, plusData, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, or_false, false_or]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem four_mul_le_pRank_omegaPlus (hn : 4 ≤ n) [Finite K] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    4 * f ≤ pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) :=
  (plusData hn).four_mul_le_pRank hp2 hK _ (quadPlus_X hn) (quadPlus_w hn) (quadPlus_d hn)

@[expose] def minusData (hn : 4 ≤ n) (b : K) :
    OrthData (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K where
  X i := Sum.inl (Fin.castLE (by omega) i)
  Y i := Sum.inr (Sum.inl (Fin.castLE (by omega) i))
  w := Pi.single (Sum.inr (Sum.inr 0)) 1
  β := (2 : K) • LinearMap.proj (Sum.inr (Sum.inr 0)) + b • LinearMap.proj (Sum.inr (Sum.inr 1))
  injX _ _ h := Fin.castLE_injective _ (Sum.inl_injective h)
  injY _ _ h := Fin.castLE_injective _ (Sum.inl_injective (Sum.inr_injective h))
  X_ne_Y _ _ := Sum.inl_ne_inr
  w_X _ := by simp
  w_Y _ := by simp
  β_X _ := by simp
  β_Y _ := by simp
  β_w := by simp

theorem quadMinus_X (hn : 4 ≤ n) (b c : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
    (i : Fin 3) (a : K) :
    StatedQuadMinus n K b c (v + Pi.single ((minusData hn b).X i) a) =
      StatedQuadMinus n K b c v + a * v ((minusData hn b).Y i) := by
  simp only [StatedQuadMinus, minusData, Pi.add_apply, Pi.single_apply, Sum.inl.injEq,
    reduceCtorEq, ↓reduceIte, add_zero, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ]
  ring

theorem quadMinus_w (hn : 4 ≤ n) (b c : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
    (s : K) :
    StatedQuadMinus n K b c (v + s • (minusData hn b).w) =
      StatedQuadMinus n K b c v + s * (minusData hn b).β v + s ^ 2 := by
  simp only [StatedQuadMinus, minusData, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
    Sum.inr.injEq, reduceCtorEq, ↓reduceIte, smul_eq_mul, mul_zero, add_zero, mul_one,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    show ((1 : Fin 2) = 0) = False by decide]
  ring

theorem quadMinus_d (hn : 4 ≤ n) (b c : K) (i : Fin 3)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c ((minusData hn b).dL i v) = StatedQuadMinus n K b c v := by
  simp only [StatedQuadMinus, OrthData.dL_apply, OrthData.dsign, minusData, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, or_false, false_or, ↓reduceIte, one_mul]
  congr 3
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem four_mul_le_pRank_omegaMinus (hn : 4 ≤ n) (b c : K) [Finite K] {p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    4 * f ≤ pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) :=
  (minusData hn b).four_mul_le_pRank hp2 hK _ (quadMinus_X hn b c) (quadMinus_w hn b c)
    (quadMinus_d hn b c)

end CFSG.SectionRank.ClassicalOdd
