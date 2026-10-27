module

public import CFSG.LieType.Universal.Spin.RootElements
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CliffordAlgebra QuadraticMap

variable (n : ℕ) {K : Type*} [Field K] (b c : K)

abbrev Vm (n : ℕ) (K : Type*) : Type _ := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K

@[expose] def planeVec (w : Fin 2 → K) : Vm n K
  | .inr (.inr t) => w t
  | _ => 0

@[expose] def eVec (i : Fin (n - 1)) : Vm n K := Pi.single (.inl i) 1

@[expose] def fVec (i : Fin (n - 1)) : Vm n K := Pi.single (.inr (.inl i)) 1

theorem planeVec_add (w w' : Fin 2 → K) : planeVec n (w + w') = planeVec n w + planeVec n w' := by
  funext v
  rcases v with i | i | t <;> simp [planeVec]

theorem planeVec_zero : planeVec n (0 : Fin 2 → K) = 0 := by
  funext v
  rcases v with i | i | t <;> simp [planeVec]

theorem planeVec_injective : Function.Injective (planeVec n (K := K)) := by
  intro w w' h
  funext t
  exact congrFun h (.inr (.inr t))

theorem quadMinus_planeVec (w : Fin 2 → K) :
    quadMinus n K b c (planeVec n w) = w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2 := by
  simp [quadMinus_apply, planeVec]

theorem quadMinus_eVec (i : Fin (n - 1)) : quadMinus n K b c (eVec n i) = 0 := by
  simp [quadMinus_apply, eVec, Pi.single_apply]

theorem quadMinus_fVec (i : Fin (n - 1)) : quadMinus n K b c (fVec n i) = 0 := by
  simp [quadMinus_apply, fVec, Pi.single_apply]

theorem polar_eVec_planeVec (i : Fin (n - 1)) (w : Fin 2 → K) :
    polar (quadMinus n K b c) (eVec n i) (planeVec n w) = 0 := by
  simp [polar_quadMinus, eVec, planeVec, Pi.single_apply]

theorem polar_fVec_planeVec (i : Fin (n - 1)) (w : Fin 2 → K) :
    polar (quadMinus n K b c) (fVec n i) (planeVec n w) = 0 := by
  simp [polar_quadMinus, fVec, planeVec, Pi.single_apply]

variable {b c} in
theorem binary_ne_zero (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {w : Fin 2 → K} (hw : w ≠ 0) :
    w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2 ≠ 0 := by
  by_cases h1 : w 1 = 0
  · have h0 : w 0 ≠ 0 := by
      intro h0
      apply hw
      funext t
      fin_cases t
      · exact h0
      · exact h1
    rw [h1]
    simpa using h0
  · intro hzero
    apply h (w 0 / w 1)
    have hw1 : w 1 ^ 2 ≠ 0 := pow_ne_zero 2 h1
    have : (w 0 / w 1) ^ 2 + b * (w 0 / w 1) + c =
        (w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2) / w 1 ^ 2 := by
      field_simp
    rw [this, hzero, zero_div]

@[expose] noncomputable def shortPos (i : Fin (n - 1)) (w : Fin 2 → K) :
    CliffordAlgebra (quadMinus n K b c) :=
  1 + ι (quadMinus n K b c) (planeVec n w) * ι (quadMinus n K b c) (eVec n i)

@[expose] noncomputable def shortNeg (i : Fin (n - 1)) (w : Fin 2 → K) :
    CliffordAlgebra (quadMinus n K b c) :=
  1 + ι (quadMinus n K b c) (planeVec n w) * ι (quadMinus n K b c) (fVec n i)

theorem shortPos_add (i : Fin (n - 1)) (w w' : Fin 2 → K) :
    shortPos n b c i (w + w') = shortPos n b c i w * shortPos n b c i w' := by
  rw [shortPos, shortPos, shortPos,
    one_add_ι_mul_ι_mul_one_add_ι_mul_ι _ (quadMinus_eVec n b c i)
      (polar_eVec_planeVec n b c i w'), planeVec_add]

theorem shortNeg_add (i : Fin (n - 1)) (w w' : Fin 2 → K) :
    shortNeg n b c i (w + w') = shortNeg n b c i w * shortNeg n b c i w' := by
  rw [shortNeg, shortNeg, shortNeg,
    one_add_ι_mul_ι_mul_one_add_ι_mul_ι _ (quadMinus_fVec n b c i)
      (polar_fVec_planeVec n b c i w'), planeVec_add]

theorem shortPos_zero (i : Fin (n - 1)) : shortPos n b c i 0 = 1 := by
  rw [shortPos, planeVec_zero, map_zero, zero_mul, add_zero]

theorem shortNeg_zero (i : Fin (n - 1)) : shortNeg n b c i 0 = 1 := by
  rw [shortNeg, planeVec_zero, map_zero, zero_mul, add_zero]

variable {b c}

theorem shortPos_mem (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) (w : Fin 2 → K) :
    shortPos n b c i w ∈ spinGroup (quadMinus n K b c) := by
  by_cases hw : w = 0
  · rw [hw, shortPos_zero]
    exact one_mem _
  · refine one_add_ι_mul_ι_mem_spinGroup _ (quadMinus_eVec n b c i)
      (polar_eVec_planeVec n b c i w) (isUnit_iff_ne_zero.2 ?_)
    rw [quadMinus_planeVec]
    exact binary_ne_zero h hw

theorem shortNeg_mem (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) (w : Fin 2 → K) :
    shortNeg n b c i w ∈ spinGroup (quadMinus n K b c) := by
  by_cases hw : w = 0
  · rw [hw, shortNeg_zero]
    exact one_mem _
  · refine one_add_ι_mul_ι_mem_spinGroup _ (quadMinus_fVec n b c i)
      (polar_fVec_planeVec n b c i w) (isUnit_iff_ne_zero.2 ?_)
    rw [quadMinus_planeVec]
    exact binary_ne_zero h hw

@[expose] noncomputable def shortPosHom (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) :
    Multiplicative (Fin 2 → K) →* spinGroup (quadMinus n K b c) where
  toFun w := ⟨shortPos n b c i w.toAdd, shortPos_mem n h i _⟩
  map_one' := Subtype.ext (shortPos_zero n b c i)
  map_mul' _ _ := Subtype.ext (shortPos_add n b c i _ _)

@[expose] noncomputable def shortNegHom (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) :
    Multiplicative (Fin 2 → K) →* spinGroup (quadMinus n K b c) where
  toFun w := ⟨shortNeg n b c i w.toAdd, shortNeg_mem n h i _⟩
  map_one' := Subtype.ext (shortNeg_zero n b c i)
  map_mul' _ _ := Subtype.ext (shortNeg_add n b c i _ _)

private theorem linearIndependent_planeVec {w : Fin 2 → K} (hw : w ≠ 0) {u : Vm n K}
    (hu : u ≠ 0) (hdisj : ∀ v, u v ≠ 0 → planeVec n w v = 0)
    (hdisj' : ∀ v, planeVec n w v ≠ 0 → u v = 0) :
    LinearIndependent K ![planeVec n w, u] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hpw : planeVec n w ≠ 0 := fun h0 =>
    hw (planeVec_injective n (h0.trans (planeVec_zero n).symm))
  obtain ⟨v₁, hv₁⟩ : ∃ v, planeVec n w v ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hpw (funext h')
  obtain ⟨v₂, hv₂⟩ : ∃ v, u v ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hu (funext h')
  have e1 := congrFun hst v₁
  have e2 := congrFun hst v₂
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hdisj' v₁ hv₁,
    hdisj v₂ hv₂, mul_zero, add_zero, zero_add] at e1 e2
  exact ⟨(mul_eq_zero.1 e1).resolve_right hv₁, (mul_eq_zero.1 e2).resolve_right hv₂⟩

theorem shortPosHom_injective (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) :
    Function.Injective (shortPosHom n h i) := by
  intro w w' hww
  have h1 := congrArg (fun x : spinGroup (quadMinus n K b c) =>
    (x : CliffordAlgebra (quadMinus n K b c))) hww
  change shortPos n b c i w.toAdd = shortPos n b c i w'.toAdd at h1
  have h2 : ι (quadMinus n K b c) (planeVec n (w.toAdd - w'.toAdd)) *
      ι (quadMinus n K b c) (eVec n i) = 0 := by
    have hsub : planeVec n (w.toAdd - w'.toAdd) = planeVec n w.toAdd - planeVec n w'.toAdd := by
      funext v
      rcases v with j | j | t <;> simp [planeVec]
    rw [hsub, map_sub, sub_mul]
    rw [shortPos, shortPos] at h1
    rw [add_left_cancel h1, sub_self]
  by_contra hne
  have hne' : w.toAdd - w'.toAdd ≠ 0 := fun h0 =>
    hne (Multiplicative.toAdd.injective (sub_eq_zero.1 h0))
  refine ι_mul_ι_ne_zero _ (linearIndependent_planeVec n hne' ?_ ?_ ?_) h2
  · intro h0
    have := congrFun h0 (.inl i)
    simp [eVec] at this
  · intro v hv
    simp only [eVec, Pi.single_apply] at hv
    split_ifs at hv with hv'
    · subst hv'
      rfl
    · exact absurd rfl hv
  · intro v hv
    rcases v with j | j | t
    · exact absurd rfl hv
    · exact absurd rfl hv
    · simp [eVec]

theorem shortNegHom_injective (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) :
    Function.Injective (shortNegHom n h i) := by
  intro w w' hww
  have h1 := congrArg (fun x : spinGroup (quadMinus n K b c) =>
    (x : CliffordAlgebra (quadMinus n K b c))) hww
  change shortNeg n b c i w.toAdd = shortNeg n b c i w'.toAdd at h1
  have h2 : ι (quadMinus n K b c) (planeVec n (w.toAdd - w'.toAdd)) *
      ι (quadMinus n K b c) (fVec n i) = 0 := by
    have hsub : planeVec n (w.toAdd - w'.toAdd) = planeVec n w.toAdd - planeVec n w'.toAdd := by
      funext v
      rcases v with j | j | t <;> simp [planeVec]
    rw [hsub, map_sub, sub_mul]
    rw [shortNeg, shortNeg] at h1
    rw [add_left_cancel h1, sub_self]
  by_contra hne
  have hne' : w.toAdd - w'.toAdd ≠ 0 := fun h0 =>
    hne (Multiplicative.toAdd.injective (sub_eq_zero.1 h0))
  refine ι_mul_ι_ne_zero _ (linearIndependent_planeVec n hne' ?_ ?_ ?_) h2
  · intro h0
    have := congrFun h0 (.inr (.inl i))
    simp [fVec] at this
  · intro v hv
    simp only [fVec, Pi.single_apply] at hv
    split_ifs at hv with hv'
    · subst hv'
      rfl
    · exact absurd rfl hv
  · intro v hv
    rcases v with j | j | t
    · exact absurd rfl hv
    · exact absurd rfl hv
    · simp [fVec]

end CFSG.LieType.Universal.Spin.Twisted
