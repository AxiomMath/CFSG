module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.OrthRot

public section

namespace CFSG.SectionRank.ClassicalEven

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix

namespace OrthRot

section Forms

variable {K : Type} [Field K] {n : ℕ}

theorem isPolar_plus_inl (j : Fin n) :
    IsPolar (StatedQuadPlus n K) (Pi.single (Sum.inl j) 1) (LinearMap.proj (Sum.inr j)) 0 :=
  fun v t => by
    simp only [StatedQuadPlus, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Sum.inl.injEq,
      reduceCtorEq, ↓reduceIte, smul_eq_mul, mul_ite, mul_one, mul_zero, add_zero, add_mul,
      Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      LinearMap.proj_apply]

theorem isPolar_plus_inr (j : Fin n) :
    IsPolar (StatedQuadPlus n K) (Pi.single (Sum.inr j) 1) (LinearMap.proj (Sum.inl j)) 0 :=
  fun v t => by
    simp only [StatedQuadPlus, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Sum.inr.injEq,
      reduceCtorEq, ↓reduceIte, smul_eq_mul, mul_ite, mul_one, mul_zero, add_zero, mul_add,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, LinearMap.proj_apply]
    ring

theorem castLE_ne_three (hn : 4 ≤ n) (i : Fin 3) :
    Fin.castLE (by omega : 3 ≤ n) i ≠ ⟨3, by omega⟩ := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castLE] at this
  omega

def plusFrame (hn : 4 ≤ n) : Frame (StatedQuadPlus n K) where
  X i := Sum.inl (Fin.castLE (by omega) i)
  Y i := Sum.inr (Fin.castLE (by omega) i)
  w := Pi.single (Sum.inl ⟨3, by omega⟩) 1 + Pi.single (Sum.inr ⟨3, by omega⟩) 1
  β := (LinearMap.proj (Sum.inr ⟨3, by omega⟩) : (Fin n ⊕ Fin n → K) →ₗ[K] K) +
    LinearMap.proj (Sum.inl ⟨3, by omega⟩)
  injX _ _ h := Fin.castLE_injective _ (Sum.inl_injective h)
  injY _ _ h := Fin.castLE_injective _ (Sum.inr_injective h)
  X_ne_Y _ _ := Sum.inl_ne_inr
  w_X i := by simp [castLE_ne_three hn i]
  w_Y i := by simp [castLE_ne_three hn i]
  isPolar_X _ := isPolar_plus_inl _
  isPolar_Y _ := isPolar_plus_inr _
  isPolar_w := (isPolar_plus_inl _).add (isPolar_plus_inr _) (by simp)

theorem isPolar_minus_inl (b c : K) (j : Fin (n - 1)) :
    IsPolar (StatedQuadMinus n K b c) (Pi.single (Sum.inl j) 1)
      (LinearMap.proj (Sum.inr (Sum.inl j))) 0 :=
  fun v t => by
    simp only [StatedQuadMinus, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Sum.inl.injEq,
      reduceCtorEq, ↓reduceIte, smul_eq_mul, mul_ite, mul_one, mul_zero, add_zero, add_mul,
      Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      LinearMap.proj_apply]
    ring

theorem isPolar_minus_inr (b c : K) (j : Fin (n - 1)) :
    IsPolar (StatedQuadMinus n K b c) (Pi.single (Sum.inr (Sum.inl j)) 1)
      (LinearMap.proj (Sum.inl j)) 0 :=
  fun v t => by
    simp only [StatedQuadMinus, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Sum.inr.injEq,
      Sum.inl.injEq, reduceCtorEq, ↓reduceIte, smul_eq_mul, mul_ite, mul_one, mul_zero,
      add_zero, mul_add, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      LinearMap.proj_apply]
    ring

theorem isPolar_minus_u (b c : K) :
    IsPolar (StatedQuadMinus n K b c) (Pi.single (Sum.inr (Sum.inr 0)) 1)
      ((2 : K) • LinearMap.proj (Sum.inr (Sum.inr 0)) +
        b • LinearMap.proj (Sum.inr (Sum.inr 1))) 1 :=
  fun v t => by
    simp only [StatedQuadMinus, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Sum.inr.injEq,
      reduceCtorEq, ↓reduceIte, smul_eq_mul, mul_one, mul_zero, add_zero,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      show ((1 : Fin 2) = 0) = False by decide]
    ring

def minusFrame (hn : 4 ≤ n) (b c : K) : Frame (StatedQuadMinus n K b c) where
  X i := Sum.inl (Fin.castLE (by omega) i)
  Y i := Sum.inr (Sum.inl (Fin.castLE (by omega) i))
  w := Pi.single (Sum.inr (Sum.inr 0)) 1
  β := (2 : K) • LinearMap.proj (Sum.inr (Sum.inr 0)) + b • LinearMap.proj (Sum.inr (Sum.inr 1))
  injX _ _ h := Fin.castLE_injective _ (Sum.inl_injective h)
  injY _ _ h := Fin.castLE_injective _ (Sum.inl_injective (Sum.inr_injective h))
  X_ne_Y _ _ := Sum.inl_ne_inr
  w_X _ := by simp
  w_Y _ := by simp
  isPolar_X _ := isPolar_minus_inl b c _
  isPolar_Y _ := isPolar_minus_inr b c _
  isPolar_w := isPolar_minus_u b c

end Forms

end OrthRot

theorem omegaPlus_three_le_pRank_three {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 4 ≤ n) :
    3 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) :=
  (OrthRot.plusFrame hn).three_le_pRank_three

theorem omegaMinus_three_le_pRank_three {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 4 ≤ n) (b c : K) :
    3 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c)))) :=
  (OrthRot.minusFrame hn b c).three_le_pRank_three

end CFSG.SectionRank.ClassicalEven
