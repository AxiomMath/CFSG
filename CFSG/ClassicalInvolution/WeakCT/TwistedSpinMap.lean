module

public import CFSG.ClassicalInvolution.WeakCT.SpModel
public import CFSG.LieType.Universal.Spin.Chevalley.Odd
public import CFSG.LieType.Universal.Spin.Twisted.Frame

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem sum_pushforward_mul {m m' : ℕ} (σ : Fin m → Fin m') (hσ : Function.Injective σ)
    (a b : Fin m → F) :
    ∑ j : Fin m', (∑ i, if σ i = j then a i else 0) * (∑ i, if σ i = j then b i else 0) =
      ∑ i, a i * b i := by
  classical
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h1 : σ i = j
    · have h2 : σ k ≠ j := fun h2 => hk (hσ (h2.trans h1.symm))
      simp [h2]
    · simp [h1]
  · simp

@[expose] noncomputable def oddToMinus (n : ℕ) (b c : F) :
    (quadOdd (n - 1) F).Isometry (quadMinus n F b c) where
  toFun v := fun x => match x with
    | .inl i => v (.inl i)
    | .inr (.inl i) => v (.inr (.inl i))
    | .inr (.inr t) => if t = 0 then v (.inr (.inr ())) else 0
  map_add' v w := by
    funext x
    rcases x with i | i | t
    · rfl
    · rfl
    · by_cases ht : t = 0 <;> simp [ht]
  map_smul' a v := by
    funext x
    rcases x with i | i | t
    · rfl
    · rfl
    · by_cases ht : t = 0 <;> simp [ht]
  map_app' v := by
    simp [quadMinus_apply, quadOdd_apply]

@[simp] theorem oddToMinus_apply_inl (n : ℕ) (b c : F) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Unit → F)
    (i : Fin (n - 1)) : oddToMinus n b c v (.inl i) = v (.inl i) := rfl

@[simp] theorem oddToMinus_apply_inr_inl (n : ℕ) (b c : F)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Unit → F) (i : Fin (n - 1)) :
    oddToMinus n b c v (.inr (.inl i)) = v (.inr (.inl i)) := rfl

@[simp] theorem oddToMinus_apply_inr_inr (n : ℕ) (b c : F)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Unit → F) (t : Fin 2) :
    oddToMinus n b c v (.inr (.inr t)) = if t = 0 then v (.inr (.inr ())) else 0 := rfl

theorem oddToMinus_oddVec (n : ℕ) (b c : F) (i : Fin (n - 1)) (s : Bool) :
    oddToMinus n b c (oddVec (n - 1) F i s) = minusVec n i s := by
  funext x
  rcases x with j | j | t <;> cases s <;>
    simp [oddVec, minusVec, eVec, fVec, Pi.single_apply]

theorem oddToMinus_oddZ (n : ℕ) (b c : F) :
    oddToMinus n b c (oddZ (n - 1) F) = planeVec n planeOne := by
  funext x
  rcases x with j | j | t
  · simp [oddZ, planeVec]
  · simp [oddZ, planeVec]
  · fin_cases t <;> simp [oddZ, planeVec, planeOne]

@[expose] def pairShift (n : ℕ) (hn : 3 ≤ n) (i : Fin (3 - 1)) : Fin (n - 1) :=
  ⟨n - 3 + i.val, by have := i.2; omega⟩

theorem pairShift_injective (n : ℕ) (hn : 3 ≤ n) : Function.Injective (pairShift n hn) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [pairShift] at this
  exact Fin.ext (by omega)

@[expose] noncomputable def minusShift (n : ℕ) (hn : 3 ≤ n) (b c : F) :
    (quadMinus 3 F b c).Isometry (quadMinus n F b c) where
  toFun v := fun x => match x with
    | .inl j => ∑ i, if pairShift n hn i = j then v (.inl i) else 0
    | .inr (.inl j) => ∑ i, if pairShift n hn i = j then v (.inr (.inl i)) else 0
    | .inr (.inr t) => v (.inr (.inr t))
  map_add' v w := by
    funext x
    rcases x with j | j | t
    · simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    · simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    · rfl
  map_smul' a v := by
    funext x
    rcases x with j | j | t
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    · rfl
  map_app' v := by
    rw [quadMinus_apply, quadMinus_apply]
    simp only
    rw [sum_pushforward_mul (pairShift n hn) (pairShift_injective n hn)
      (fun i => v (.inl i)) (fun i => v (.inr (.inl i)))]

@[simp] theorem minusShift_apply_inl (n : ℕ) (hn : 3 ≤ n) (b c : F)
    (v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) (j : Fin (n - 1)) :
    minusShift n hn b c v (.inl j) = ∑ i, if pairShift n hn i = j then v (.inl i) else 0 := rfl

@[simp] theorem minusShift_apply_inr_inl (n : ℕ) (hn : 3 ≤ n) (b c : F)
    (v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) (j : Fin (n - 1)) :
    minusShift n hn b c v (.inr (.inl j)) =
      ∑ i, if pairShift n hn i = j then v (.inr (.inl i)) else 0 := rfl

@[simp] theorem minusShift_apply_inr_inr (n : ℕ) (hn : 3 ≤ n) (b c : F)
    (v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) (t : Fin 2) :
    minusShift n hn b c v (.inr (.inr t)) = v (.inr (.inr t)) := rfl

theorem minusShift_single_inl (n : ℕ) (hn : 3 ≤ n) (b c : F) (i : Fin (3 - 1)) :
    minusShift n hn b c (Pi.single (.inl i) 1) = Pi.single (.inl (pairShift n hn i)) 1 := by
  funext x
  rcases x with j | j | t
  · rw [minusShift_apply_inl, Finset.sum_eq_single i]
    · by_cases h : pairShift n hn i = j
      · subst h
        simp
      · simp [h, Ne.symm h]
    · intro k _ hk
      simp [hk]
    · simp
  · rw [minusShift_apply_inr_inl]
    simp
  · rw [minusShift_apply_inr_inr]
    simp

theorem minusShift_single_inr (n : ℕ) (hn : 3 ≤ n) (b c : F) (i : Fin (3 - 1)) :
    minusShift n hn b c (Pi.single (.inr (.inl i)) 1) =
      Pi.single (.inr (.inl (pairShift n hn i))) 1 := by
  funext x
  rcases x with j | j | t
  · rw [minusShift_apply_inl]
    simp
  · rw [minusShift_apply_inr_inl, Finset.sum_eq_single i]
    · by_cases h : pairShift n hn i = j
      · subst h
        simp
      · simp [h, Ne.symm h]
    · intro k _ hk
      simp [hk]
    · simp
  · rw [minusShift_apply_inr_inr]
    simp

theorem minusShift_minusVec (n : ℕ) (hn : 3 ≤ n) (b c : F) (i : Fin (3 - 1)) (s : Bool) :
    minusShift n hn b c (minusVec 3 i s) = minusVec n (pairShift n hn i) s := by
  cases s
  · exact minusShift_single_inr n hn b c i
  · exact minusShift_single_inl n hn b c i

theorem minusShift_planeVec (n : ℕ) (hn : 3 ≤ n) (b c : F) (p : Fin 2 → F) :
    minusShift n hn b c (planeVec 3 p) = planeVec n p := by
  funext x
  rcases x with j | j | t
  · rw [minusShift_apply_inl]
    simp [planeVec]
  · rw [minusShift_apply_inr_inl]
    simp [planeVec]
  · rw [minusShift_apply_inr_inr]
    simp [planeVec]

section Injective

variable {V₁ V₂ : Type} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

theorem spinGroupMap_injective_of_injective [FiniteDimensional F V₁] [Nontrivial V₁]
    (h2 : (2 : F) ≠ 0) (hQ : Q₁.Nondegenerate) (f : Q₁ →qᵢ Q₂) (hf : Function.Injective f) :
    Function.Injective f.spinGroupMap := by
  let _ : Invertible (2 : F) := invertibleOfNonzero h2
  rw [injective_iff_map_eq_one]
  intro x hx
  have hker : x ∈ (spinAction Q₁).ker := by
    rw [MonoidHom.mem_ker]
    ext v
    apply hf
    have h := QuadraticMap.Isometry.spinGroupMap_spinVectorAction f x v
    rw [hx] at h
    simp only [spinVectorAction_eq, map_one] at h
    simpa using h.symm
  rcases (mem_ker_spinAction_iff Q₁ hQ x).1 hker with h | h
  · exact h
  · exfalso
    have hQ₂ : Q₂ ≠ 0 := by
      intro h0
      apply hQ.ne_zero
      ext m
      simpa [h0] using (f.map_app m).symm
    have h1 := QuadraticMap.Isometry.spinGroupMap_negOne f hQ.ne_zero
    rw [h] at hx
    rw [h1] at hx
    exact CliffordAlgebra.spinGroup.negOne_ne_one Q₂ _ hx

end Injective

section Compat

theorem tv01_eq_upperSL2 (c : F) : (tv 0 1 c : SL(2, F)) = upperSL2 c :=
  (tv01_eq_sl2Upper c).trans rfl

theorem tv10_eq_lowerSL2 (c : F) : (tv 1 0 c : SL(2, F)) = lowerSL2 c :=
  (tv10_eq_sl2Lower c).trans rfl

theorem spinGroupMap_oddToMinus_longRoot (n : ℕ) (b c : F) {i j : Fin (n - 1)} (hij : i ≠ j)
    (s t : Bool) (x : F) :
    (oddToMinus n b c).spinGroupMap ((oddFrame (n - 1) F).longRoot hij s t (.ofAdd x)) =
      (minusFrame n b c).longRoot hij s t (.ofAdd x) := by
  apply Subtype.ext
  rw [QuadraticMap.Isometry.coe_spinGroupMap_apply, HypFrame.coe_longRoot, HypFrame.coe_longRoot]
  simp only [map_add, map_one, map_smul, map_mul, CliffordAlgebra.map_apply_ι, oddFrame_vec,
    minusFrame_vec, oddToMinus_oddVec]

theorem spinGroupMap_oddToMinus_longSL2 (n : ℕ) (b c : F) {i j : Fin (n - 1)} (hij : i ≠ j)
    (s t : Bool) :
    (oddToMinus n b c).spinGroupMap.comp ((oddFrame (n - 1) F).longSL2 hij s t) =
      (minusFrame n b c).longSL2 hij s t := by
  refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
  · rw [MonoidHom.comp_apply, tv01_eq_upperSL2, HypFrame.longSL2_upperSL2,
      HypFrame.longSL2_upperSL2, spinGroupMap_oddToMinus_longRoot]
  · rw [MonoidHom.comp_apply, tv10_eq_lowerSL2, HypFrame.longSL2_lowerSL2,
      HypFrame.longSL2_lowerSL2, spinGroupMap_oddToMinus_longRoot]

theorem spinGroupMap_minusShift_longRoot (n : ℕ) (hn : 3 ≤ n) (b c : F) {i j : Fin (3 - 1)}
    (hij : i ≠ j) (s t : Bool) (x : F) :
    (minusShift n hn b c).spinGroupMap ((minusFrame 3 b c).longRoot hij s t (.ofAdd x)) =
      (minusFrame n b c).longRoot ((pairShift_injective n hn).ne hij) s t (.ofAdd x) := by
  apply Subtype.ext
  rw [QuadraticMap.Isometry.coe_spinGroupMap_apply, HypFrame.coe_longRoot, HypFrame.coe_longRoot]
  simp only [map_add, map_one, map_smul, map_mul, CliffordAlgebra.map_apply_ι, minusFrame_vec,
    minusShift_minusVec]

theorem spinGroupMap_minusShift_longSL2 (n : ℕ) (hn : 3 ≤ n) (b c : F) {i j : Fin (3 - 1)}
    (hij : i ≠ j) (s t : Bool) :
    (minusShift n hn b c).spinGroupMap.comp ((minusFrame 3 b c).longSL2 hij s t) =
      (minusFrame n b c).longSL2 ((pairShift_injective n hn).ne hij) s t := by
  refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
  · rw [MonoidHom.comp_apply, tv01_eq_upperSL2, HypFrame.longSL2_upperSL2,
      HypFrame.longSL2_upperSL2, spinGroupMap_minusShift_longRoot]
  · rw [MonoidHom.comp_apply, tv10_eq_lowerSL2, HypFrame.longSL2_lowerSL2,
      HypFrame.longSL2_lowerSL2, spinGroupMap_minusShift_longRoot]

theorem spinGroupMap_minusShift_twShortRoot (n : ℕ) (hn : 3 ≤ n) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (i : Fin (3 - 1)) (s : Bool) (p : Fin 2 → F) :
    (minusShift n hn b c).spinGroupMap (twShortRoot 3 hirr i s (.ofAdd p)) =
      twShortRoot n hirr (pairShift n hn i) s (.ofAdd p) := by
  apply Subtype.ext
  rw [QuadraticMap.Isometry.coe_spinGroupMap_apply, coe_twShortRoot, coe_twShortRoot]
  simp only [map_add, map_one, map_mul, CliffordAlgebra.map_apply_ι, minusShift_planeVec,
    minusShift_minusVec]

end Compat

section SpinInjective

theorem oddToMinus_injective (n : ℕ) (b c : F) : Function.Injective (oddToMinus n b c) := by
  intro v w h
  funext x
  rcases x with i | i | ⟨⟩
  · exact congrFun h (.inl i)
  · exact congrFun h (.inr (.inl i))
  · simpa using congrFun h (.inr (.inr 0))

theorem minusShift_injective (n : ℕ) (hn : 3 ≤ n) (b c : F) :
    Function.Injective (minusShift n hn b c) := by
  intro v w h
  have hs : ∀ (u : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) (i : Fin (3 - 1)),
      minusShift n hn b c u (.inl (pairShift n hn i)) = u (.inl i) ∧
        minusShift n hn b c u (.inr (.inl (pairShift n hn i))) = u (.inr (.inl i)) := by
    intro u i
    refine ⟨?_, ?_⟩
    · rw [minusShift_apply_inl, Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [(pairShift_injective n hn).ne hk]
      · simp
    · rw [minusShift_apply_inr_inl, Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [(pairShift_injective n hn).ne hk]
      · simp
  funext x
  rcases x with i | i | t
  · have := congrFun h (.inl (pairShift n hn i))
    rwa [(hs v i).1, (hs w i).1] at this
  · have := congrFun h (.inr (.inl (pairShift n hn i)))
    rwa [(hs v i).2, (hs w i).2] at this
  · exact congrFun h (.inr (.inr t))

theorem spinGroupMap_oddToMinus_injective (h2 : (2 : F) ≠ 0) (n : ℕ) (b c : F) :
    Function.Injective (oddToMinus n b c).spinGroupMap :=
  spinGroupMap_injective_of_injective h2 (nondegenerate_quadOdd (n - 1) F) _
    (oddToMinus_injective n b c)

theorem spinGroupMap_minusShift_injective [Finite F] (h2 : (2 : F) ≠ 0) (n : ℕ) (hn : 3 ≤ n)
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (minusShift n hn b c).spinGroupMap :=
  spinGroupMap_injective_of_injective h2 (nondegenerate_quadMinus_of_finite 3 F hirr) _
    (minusShift_injective n hn b c)

end SpinInjective

end CFSG.ClassicalInvolution.WeakCT
