module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowSummand
public import CFSG.ClassicalGroups.Orthogonal.Models

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem a2l_polar_sum_left {ι : Type} (s : Finset ι) (w : ι → V) (y : V) :
    polar Q (∑ i ∈ s, w i) y = ∑ i ∈ s, polar Q (w i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polar_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, polar_add_left, ih]

theorem a2l_polar_sum_right {ι : Type} (s : Finset ι) (x : V) (w : ι → V) :
    polar Q x (∑ i ∈ s, w i) = ∑ i ∈ s, polar Q x (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polar_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, polar_add_right, ih]

section Pairs

variable {m : ℕ} (P : Fin m → HypPair Q) (hP : ∀ i j, i ≠ j → (P i).Orth (P j))

include hP in
theorem a2l_polar_e_f (i j : Fin m) : polar Q (P i).e (P j).f = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [(P i).polar_ef]
  · simp [h, (hP i j h).ef]

include hP in
theorem a2l_polar_f_e (i j : Fin m) : polar Q (P i).f (P j).e = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [(P i).polar_fe]
  · simp [h, (hP i j h).fe]

include hP in
theorem a2l_polar_e_e (i j : Fin m) : polar Q (P i).e (P j).e = 0 := by
  by_cases h : i = j
  · subst h
    exact (P i).polar_ee
  · exact (hP i j h).ee

include hP in
theorem a2l_polar_f_f (i j : Fin m) : polar Q (P i).f (P j).f = 0 := by
  by_cases h : i = j
  · subst h
    exact (P i).polar_ff
  · exact (hP i j h).ff

variable (Q) in
@[expose] def a2lPairIncl : (Fin m ⊕ Fin m → K) →ₗ[K] V where
  toFun d := ∑ j, (d (Sum.inl j) • (P j).e + d (Sum.inr j) • (P j).f)
  map_add' d d' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c d := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, smul_add, mul_smul]

@[expose] def a2lPairCoords : V →ₗ[K] (Fin m ⊕ Fin m → K) where
  toFun x := Sum.elim (fun j => polar Q x (P j).f) (fun j => polar Q x (P j).e)
  map_add' x y := by
    ext (j | j) <;> simp [polar_add_left]
  map_smul' c x := by
    ext (j | j) <;> simp [polar_smul_left]

include hP in
theorem a2lPairCoords_incl (d : Fin m ⊕ Fin m → K) :
    a2lPairCoords P (a2lPairIncl Q P d) = d := by
  ext (j | j)
  · simp only [a2lPairCoords, a2lPairIncl, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl]
    rw [a2l_polar_sum_left, Finset.sum_eq_single j]
    · rw [polar_add_left, polar_smul_left, polar_smul_left, a2l_polar_e_f P hP,
        a2l_polar_f_f P hP]
      simp
    · intro i _ hij
      rw [polar_add_left, polar_smul_left, polar_smul_left, a2l_polar_e_f P hP,
        a2l_polar_f_f P hP]
      simp [hij]
    · simp
  · simp only [a2lPairCoords, a2lPairIncl, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr]
    rw [a2l_polar_sum_left, Finset.sum_eq_single j]
    · rw [polar_add_left, polar_smul_left, polar_smul_left, a2l_polar_e_e P hP,
        a2l_polar_f_e P hP]
      simp
    · intro i _ hij
      rw [polar_add_left, polar_smul_left, polar_smul_left, a2l_polar_e_e P hP,
        a2l_polar_f_e P hP]
      simp [hij]
    · simp

theorem a2lPair_polar_incl (x : V) (d : Fin m ⊕ Fin m → K) :
    polar Q x (a2lPairIncl Q P d) = polar (quadPlus m K) (a2lPairCoords P x) d := by
  rw [polar_quadPlus]
  simp only [a2lPairIncl, LinearMap.coe_mk, AddHom.coe_mk, a2lPairCoords, Sum.elim_inl,
    Sum.elim_inr]
  rw [a2l_polar_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [polar_add_right, polar_smul_right, polar_smul_right]
  simp only [smul_eq_mul]
  ring

@[expose] def a2lSummandOfPairs : A2lSummand (quadPlus m K) Q where
  incl := a2lPairIncl Q P
  coords := a2lPairCoords P
  coords_incl := a2lPairCoords_incl P hP
  polar_incl := a2lPair_polar_incl P

theorem a2lPairCoords_eq_zero {x : V} (h1 : ∀ j, polar Q x (P j).f = 0)
    (h2 : ∀ j, polar Q x (P j).e = 0) : a2lPairCoords P x = 0 := by
  ext (j | j)
  · simp [a2lPairCoords, h1 j]
  · simp [a2lPairCoords, h2 j]

end Pairs

section Forms

variable {n : ℕ}

theorem a2l_summand_plus (hn : 5 ≤ n) :
    ∃ (S : A2lSummand (quadPlus 4 K) (quadPlus n K)) (v : Fin n ⊕ Fin n → K),
      v ≠ 0 ∧ S.coords v = 0 := by
  let P : Fin 4 → HypPair (quadPlus n K) := fun j => plusPair K ⟨j, by omega⟩
  have hP : ∀ i j, i ≠ j → (P i).Orth (P j) := fun i j hij =>
    plusPair_orth (fun h => hij (Fin.ext (Fin.mk.inj h)))
  have hne : ∀ j : Fin 4, (⟨4, by omega⟩ : Fin n) ≠ ⟨j, by omega⟩ := fun j h => by
    have := congrArg Fin.val h
    have hj := j.2
    simp only at this
    omega
  exact ⟨a2lSummandOfPairs P hP, (plusPair K (⟨4, by omega⟩ : Fin n)).e,
    (plusPair K _).e_ne_zero,
    a2lPairCoords_eq_zero P (fun j => (plusPair_orth (hne j)).ef)
      (fun j => (plusPair_orth (hne j)).ee)⟩

theorem a2l_summand_odd (hn : 4 ≤ n) :
    ∃ (S : A2lSummand (quadPlus 4 K) (quadOdd n K)) (v : Fin n ⊕ Fin n ⊕ Unit → K),
      v ≠ 0 ∧ S.coords v = 0 := by
  let P : Fin 4 → HypPair (quadOdd n K) := fun j => oddPair K ⟨j, by omega⟩
  have hP : ∀ i j, i ≠ j → (P i).Orth (P j) := fun i j hij =>
    oddPair_orth (fun h => hij (Fin.ext (Fin.mk.inj h)))
  refine ⟨a2lSummandOfPairs P hP, Pi.single (Sum.inr (Sum.inr ())) 1, ?_,
    a2lPairCoords_eq_zero P (fun j => ?_) (fun j => ?_)⟩
  · intro h
    have := congrFun h (Sum.inr (Sum.inr ()))
    simp at this
  · exact (polar_quadOdd_single_inr_inl n K _ _).trans (by simp [Pi.single_apply])
  · exact (polar_quadOdd_single_inl n K _ _).trans (by simp [Pi.single_apply])

theorem a2l_summand_minus (hn : 5 ≤ n) (b c : K) :
    ∃ (S : A2lSummand (quadPlus 4 K) (quadMinus n K b c))
      (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K), v ≠ 0 ∧ S.coords v = 0 := by
  let P : Fin 4 → HypPair (quadMinus n K b c) := fun j => minusPair K b c ⟨j, by omega⟩
  have hP : ∀ i j, i ≠ j → (P i).Orth (P j) := fun i j hij =>
    minusPair_orth (fun h => hij (Fin.ext (Fin.mk.inj h)))
  refine ⟨a2lSummandOfPairs P hP, Pi.single (Sum.inr (Sum.inr 0)) 1, ?_,
    a2lPairCoords_eq_zero P (fun j => ?_) (fun j => ?_)⟩
  · intro h
    have := congrFun h (Sum.inr (Sum.inr 0))
    simp at this
  · exact (polar_quadMinus_single_inr_inl n K b c _ _).trans (by simp [Pi.single_apply])
  · exact (polar_quadMinus_single_inl n K b c _ _).trans (by simp [Pi.single_apply])

end Forms

end CFSG.OddStandard.SmallF3.HypA2Leaves
