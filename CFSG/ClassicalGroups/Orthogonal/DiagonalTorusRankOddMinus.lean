module

public import CFSG.ClassicalGroups.Orthogonal.DiagonalTorusRank

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.Open CFSG.LieType.Universal.Spin QuadraticMap
open Matrix
open scoped commutatorElement

variable {m : ℕ} {F : Type} [Field F]

@[expose] def threeToFinMinus (hm : 4 ≤ m) : Fin 3 → Fin (m - 1) := fun i => Fin.castLE (by omega) i

theorem threeToFinMinus_injective (hm : 4 ≤ m) :
    Function.Injective (threeToFinMinus (m := m) hm) :=
  Fin.castLE_injective (by omega)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem diagGL_toLinEquiv_single (c : ι → Fˣ) (k : ι) :
    toLinEquiv ι F (TauCeti.diagGL c) (Pi.single k 1) = (c k : F) • Pi.single k 1 := by
  rw [toLinEquiv_apply, TauCeti.diagGL_coe]
  funext j
  rw [Matrix.mulVec_diagonal, Pi.smul_apply]
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [Pi.single_eq_of_ne hjk]

theorem reflect_mul_reflect_eq_diagGL {Q : QuadraticForm F (ι → F)} {e f : ι} (hne : e ≠ f)
    (t : Fˣ) (c : ι → Fˣ) (hce : c e = t) (hcf : c f = t⁻¹)
    (hc : ∀ k, k ≠ e → k ≠ f → c k = 1)
    (he : Q (Pi.single e 1) = 0) (hf : Q (Pi.single f 1) = 0)
    (hB : polar Q (Pi.single e 1) (Pi.single f 1) = 1)
    (horth : ∀ k, k ≠ e → k ≠ f →
      polar Q (Pi.single e 1) (Pi.single k 1) = 0 ∧
        polar Q (Pi.single f 1) (Pi.single k 1) = 0) :
    reflect Q (Pi.single e 1 + Pi.single f 1) *
        reflect Q (Pi.single e 1 + (t : F) • Pi.single f 1) =
      toLinEquiv ι F (TauCeti.diagGL c) := by
  have ht : (t : F) ≠ 0 := t.ne_zero
  have hBe : polar Q (Pi.single e 1) (Pi.single e 1) = 0 := polar_self_eq_zero he
  have hBf : polar Q (Pi.single f 1) (Pi.single f 1) = 0 := polar_self_eq_zero hf
  have hBfe : polar Q (Pi.single f 1) (Pi.single e 1) = 1 := by
    rw [polar_comm, hB]
  have hp1 : ∀ k, polar Q (Pi.single e 1 + Pi.single f 1) (Pi.single k 1) =
      if k = e then (1 : F) else if k = f then 1 else 0 := by
    intro k
    rw [polar_add_left]
    by_cases hke : k = e
    · subst hke
      rw [hBe, hBfe]
      simp
    · by_cases hkf : k = f
      · subst hkf
        rw [hB, hBf]
        simp [hke]
      · rw [(horth k hke hkf).1, (horth k hke hkf).2]
        simp [hke, hkf]
  have hp2 : ∀ k, polar Q (Pi.single e 1 + (t : F) • Pi.single f 1) (Pi.single k 1) =
      if k = e then (t : F) else if k = f then 1 else 0 := by
    intro k
    rw [polar_add_left, polar_smul_left]
    by_cases hke : k = e
    · subst hke
      rw [hBe, hBfe]
      simp
    · by_cases hkf : k = f
      · subst hkf
        rw [hB, hBf]
        simp [hke]
      · rw [(horth k hke hkf).1, (horth k hke hkf).2]
        simp [hke, hkf]
  have hQ1 : Q (Pi.single e 1 + Pi.single f 1) = 1 := by
    rw [QuadraticMap.map_add Q, he, hf, hB]
    ring
  have hQ2 : Q (Pi.single e 1 + (t : F) • Pi.single f 1) = (t : F) := by
    rw [QuadraticMap.map_add Q, he, QuadraticMap.map_smul, hf, polar_smul_right, hB]
    simp
  have hv1 : Q (Pi.single e 1 + Pi.single f 1) ≠ 0 := by
    rw [hQ1]
    exact one_ne_zero
  have hv2 : Q (Pi.single e 1 + (t : F) • Pi.single f 1) ≠ 0 := by
    rw [hQ2]
    exact ht
  have hae : reflect Q (Pi.single e 1 + Pi.single f 1) (Pi.single e 1) =
      -Pi.single f 1 := by
    rw [reflect_apply hv1, hp1 e, if_pos rfl, hQ1, div_one, one_smul]
    abel
  have haf : reflect Q (Pi.single e 1 + Pi.single f 1) (Pi.single f 1) =
      -Pi.single e 1 := by
    rw [reflect_apply hv1, hp1 f, if_neg (Ne.symm hne), if_pos rfl, hQ1, div_one, one_smul]
    abel
  have hbe : reflect Q (Pi.single e 1 + (t : F) • Pi.single f 1) (Pi.single e 1) =
      -((t : F) • Pi.single f 1) := by
    rw [reflect_apply hv2, hp2 e, if_pos rfl, hQ2, div_self ht, one_smul]
    abel
  have hbf : reflect Q (Pi.single e 1 + (t : F) • Pi.single f 1) (Pi.single f 1) =
      -(((1 : F) / (t : F)) • Pi.single e 1) := by
    rw [reflect_apply hv2, hp2 f, if_neg (Ne.symm hne), if_pos rfl, hQ2]
    rw [smul_add, smul_smul, div_mul_cancel₀ (1 : F) ht, one_smul]
    abel
  have hcomp_e : (reflect Q (Pi.single e 1 + Pi.single f 1) *
        reflect Q (Pi.single e 1 + (t : F) • Pi.single f 1)) (Pi.single e 1) =
      (t : F) • Pi.single e 1 := by
    rw [LinearEquiv.mul_apply, hbe, map_neg, map_smul, haf, smul_neg, neg_neg]
  have hcomp_f : (reflect Q (Pi.single e 1 + Pi.single f 1) *
        reflect Q (Pi.single e 1 + (t : F) • Pi.single f 1)) (Pi.single f 1) =
      ((t⁻¹ : Fˣ) : F) • Pi.single f 1 := by
    rw [LinearEquiv.mul_apply, hbf, map_neg, map_smul, hae, smul_neg, neg_neg, one_div,
      Units.val_inv_eq_inv_val]
  have hcomp_other : ∀ k, k ≠ e → k ≠ f →
      (reflect Q (Pi.single e 1 + Pi.single f 1) *
        reflect Q (Pi.single e 1 + (t : F) • Pi.single f 1)) (Pi.single k 1) =
      Pi.single k 1 := by
    intro k hke hkf
    have hp1k : polar Q (Pi.single e 1 + Pi.single f 1) (Pi.single k 1) = 0 := by
      rw [hp1 k, if_neg hke, if_neg hkf]
    have hp2k : polar Q (Pi.single e 1 + (t : F) • Pi.single f 1) (Pi.single k 1) = 0 := by
      rw [hp2 k, if_neg hke, if_neg hkf]
    rw [LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero hp2k,
      reflect_apply_of_polar_eq_zero hp1k]
  have hrhs_e : toLinEquiv ι F (TauCeti.diagGL c) (Pi.single e 1) =
      (t : F) • Pi.single e 1 := by
    rw [diagGL_toLinEquiv_single, hce]
  have hrhs_f : toLinEquiv ι F (TauCeti.diagGL c) (Pi.single f 1) =
      ((t⁻¹ : Fˣ) : F) • Pi.single f 1 := by
    rw [diagGL_toLinEquiv_single, hcf]
  have hrhs_other : ∀ k, k ≠ e → k ≠ f →
      toLinEquiv ι F (TauCeti.diagGL c) (Pi.single k 1) = Pi.single k 1 := by
    intro k hke hkf
    rw [diagGL_toLinEquiv_single, hc k hke hkf]
    simp
  have h : (reflect Q (Pi.single e 1 + Pi.single f 1) *
      reflect Q (Pi.single e 1 + (t : F) • Pi.single f 1)).toLinearMap =
      (toLinEquiv ι F (TauCeti.diagGL c)).toLinearMap := by
    refine (Pi.basisFun F ι).ext fun k => ?_
    rw [Pi.basisFun_apply]
    by_cases hke : k = e
    · subst hke
      exact hcomp_e.trans hrhs_e.symm
    · by_cases hkf : k = f
      · subst hkf
        exact hcomp_f.trans hrhs_f.symm
      · exact (hcomp_other k hke hkf).trans (hrhs_other k hke hkf).symm
  exact LinearEquiv.ext fun v => LinearMap.congr_fun h v

@[expose] def oddDiagHom (m : ℕ) (F : Type) [Field F] :
    (Fin m → Fˣ) →* (Fin m ⊕ Fin m ⊕ Unit → Fˣ) where
  toFun d := fun k =>
    match k with
    | Sum.inl i => d i
    | Sum.inr (Sum.inl i) => (d i)⁻¹
    | Sum.inr (Sum.inr _) => 1
  map_one' := by
    funext k
    rcases k with i | i | u <;> simp
  map_mul' d e := by
    funext k
    rcases k with i | i | u <;> simp [mul_comm]

@[simp]
theorem oddDiagHom_inl (d : Fin m → Fˣ) (i : Fin m) :
    oddDiagHom m F d (Sum.inl i) = d i :=
  rfl

@[simp]
theorem oddDiagHom_inr_inl (d : Fin m → Fˣ) (i : Fin m) :
    oddDiagHom m F d (Sum.inr (Sum.inl i)) = (d i)⁻¹ :=
  rfl

@[simp]
theorem oddDiagHom_inr_inr (d : Fin m → Fˣ) (u : Unit) :
    oddDiagHom m F d (Sum.inr (Sum.inr u)) = 1 :=
  rfl

@[expose] noncomputable def diagGLOddHom (m : ℕ) (F : Type) [Field F] :
    (Fin m → Fˣ) →* GL (Fin m ⊕ Fin m ⊕ Unit) F :=
  (TauCeti.diagGL (k := F) (ι := Fin m ⊕ Fin m ⊕ Unit)).comp (oddDiagHom m F)

@[simp]
theorem coe_diagGLOddHom (d : Fin m → Fˣ) :
    ((diagGLOddHom m F d : GL (Fin m ⊕ Fin m ⊕ Unit) F) :
        Matrix (Fin m ⊕ Fin m ⊕ Unit) (Fin m ⊕ Fin m ⊕ Unit) F) =
      Matrix.diagonal (fun k => (oddDiagHom m F d k : F)) :=
  TauCeti.diagGL_coe _

theorem oddDiagGen_mem_statedOmega (hm : 4 ≤ m) (t : Fˣ) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    diagGLOddHom m F (Pi.mulSingle (threeToFinOrth hm i) t) ∈
      StatedOmega (StatedQuadOdd m F) := by
  rw [statedOmega_eq_comap (coe_quadOdd m F), Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  set j : Fin m := threeToFinOrth hm i with hj
  set c : Fin m ⊕ Fin m ⊕ Unit → Fˣ := oddDiagHom m F (Pi.mulSingle j t) with hcdef
  have hdiag : diagGLOddHom m F (Pi.mulSingle j t) = TauCeti.diagGL c := rfl
  rw [hdiag]
  have horth : ∀ k, k ≠ Sum.inl j → k ≠ Sum.inr (Sum.inl j) →
      polar (quadOdd m F) (Pi.single (Sum.inl j) 1) (Pi.single k 1) = 0 ∧
        polar (quadOdd m F) (Pi.single (Sum.inr (Sum.inl j)) 1) (Pi.single k 1) = 0 := by
    intro k h1 h2
    rcases k with j' | j' | u
    · constructor
      · rw [polar_quadOdd_single_inl]; simp
      · rw [polar_quadOdd_single_inl]
        simp [show j ≠ j' from fun h => h1 (by rw [h])]
    · constructor
      · rw [polar_quadOdd_single_inr_inl]
        simp [show j ≠ j' from fun h => h2 (by rw [h])]
      · rw [polar_quadOdd_single_inr_inl]; simp
    · constructor
      · rw [polar_quadOdd_single_inr_inr]; simp
      · rw [polar_quadOdd_single_inr_inr]; simp
  have hstep := reflect_mul_reflect_eq_diagGL (Q := quadOdd m F) (e := Sum.inl j)
    (f := Sum.inr (Sum.inl j)) (by simp) t c (by simp [hcdef]) (by simp [hcdef]) (by
      intro k h1 h2
      rcases k with j' | j' | u
      · rw [hcdef, oddDiagHom_inl,
          Pi.mulSingle_eq_of_ne (show j' ≠ j from fun h => h1 (by rw [h]))]
      · rw [hcdef, oddDiagHom_inr_inl,
          Pi.mulSingle_eq_of_ne (show j' ≠ j from fun h => h2 (by rw [h]))]
        simp
      · rw [hcdef]
        simp) (quadOdd_single_inl j) (quadOdd_single_inr j)
    (by rw [polar_quadOdd_single_inr_inl]; simp) horth
  rw [← hstep]
  refine mem_of_odd_pow_of_sq_mem (N := ⁅TauCeti.QuadraticMap.orthogonalGroup (quadOdd m F),
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd m F)⁆) ?_ hodd ?_
  · intro x hx
    subst hx
    have hsq : (reflect (quadOdd m F) (Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr (Sum.inl j)) 1) *
          reflect (quadOdd m F) (Pi.single (Sum.inl j) 1 +
            (t : F) • Pi.single (Sum.inr (Sum.inl j)) 1)) ^ 2 =
        ⁅reflect (quadOdd m F) (Pi.single (Sum.inl j) 1 +
            Pi.single (Sum.inr (Sum.inl j)) 1),
          reflect (quadOdd m F) (Pi.single (Sum.inl j) 1 +
            (t : F) • Pi.single (Sum.inr (Sum.inl j)) 1)⁆ := by
      rw [pow_two, commutatorElement_def, reflect_inv, reflect_inv]
      group
    rw [hsq]
    exact Subgroup.commutator_mem_commutator
      (reflect_mem_orthogonalGroup (quadOdd m F) _)
      (reflect_mem_orthogonalGroup (quadOdd m F) _)
  · rw [hstep, ← hdiag, ← map_pow (toLinEquiv (Fin m ⊕ Fin m ⊕ Unit) F),
      ← map_pow (diagGLOddHom m F), ← Pi.mulSingle_pow, ← ht, pow_orderOf_eq_one,
      Pi.mulSingle_one]
    simp

@[expose] noncomputable def diagGenOdd (t : Fˣ) (hm : 4 ≤ m) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    StatedOmega (StatedQuadOdd m F) :=
  ⟨diagGLOddHom m F (Pi.mulSingle (threeToFinOrth hm i) t),
    oddDiagGen_mem_statedOmega hm t i hodd ht⟩

@[simp]
theorem coe_diagGenOdd (t : Fˣ) (hm : 4 ≤ m) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    ((diagGenOdd t hm i hodd ht : StatedOmega (StatedQuadOdd m F)) :
        GL (Fin m ⊕ Fin m ⊕ Unit) F) =
      diagGLOddHom m F (Pi.mulSingle (threeToFinOrth hm i) t) :=
  rfl

@[expose] noncomputable def omegaActOdd (m : ℕ) (F : Type) [Field F] :
    StatedOmega (StatedQuadOdd m F) →*
      ((Fin m ⊕ Fin m ⊕ Unit → F) ≃ₗ[F] (Fin m ⊕ Fin m ⊕ Unit → F)) :=
  (toLinEquiv (Fin m ⊕ Fin m ⊕ Unit) F).toMonoidHom.comp
    (Subgroup.subtype (StatedOmega (StatedQuadOdd m F)))

@[expose] def minusDiagHom (m : ℕ) (F : Type) [Field F] :
    (Fin (m - 1) → Fˣ) →* (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → Fˣ) where
  toFun d := fun k =>
    match k with
    | Sum.inl i => d i
    | Sum.inr (Sum.inl i) => (d i)⁻¹
    | Sum.inr (Sum.inr _) => 1
  map_one' := by
    funext k
    rcases k with i | i | u <;> simp
  map_mul' d e := by
    funext k
    rcases k with i | i | u <;> simp [mul_comm]

@[simp]
theorem minusDiagHom_inl (d : Fin (m - 1) → Fˣ) (i : Fin (m - 1)) :
    minusDiagHom m F d (Sum.inl i) = d i :=
  rfl

@[simp]
theorem minusDiagHom_inr_inl (d : Fin (m - 1) → Fˣ) (i : Fin (m - 1)) :
    minusDiagHom m F d (Sum.inr (Sum.inl i)) = (d i)⁻¹ :=
  rfl

@[simp]
theorem minusDiagHom_inr_inr (d : Fin (m - 1) → Fˣ) (u : Fin 2) :
    minusDiagHom m F d (Sum.inr (Sum.inr u)) = 1 :=
  rfl

theorem minusDiagHom_injective (m : ℕ) (F : Type) [Field F] :
    Function.Injective (minusDiagHom m F) := by
  intro d e h
  funext i
  have := congrFun h (Sum.inl i)
  simpa using this

@[expose] noncomputable def diagGLMinusHom (m : ℕ) (F : Type) [Field F] :
    (Fin (m - 1) → Fˣ) →* GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F :=
  (TauCeti.diagGL (k := F) (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)).comp (minusDiagHom m F)

theorem diagGLMinusHom_injective (m : ℕ) (F : Type) [Field F] :
    Function.Injective (diagGLMinusHom m F) :=
  TauCeti.diagGL_injective.comp (minusDiagHom_injective m F)

@[simp]
theorem coe_diagGLMinusHom (d : Fin (m - 1) → Fˣ) :
    ((diagGLMinusHom m F d : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F) :
        Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
          (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F) =
      Matrix.diagonal (fun k => (minusDiagHom m F d k : F)) :=
  TauCeti.diagGL_coe _

@[expose] noncomputable def diagTorusMinus (m : ℕ) (F : Type) [Field F] :
    Subgroup (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F) :=
  (diagGLMinusHom m F).range

theorem minusDiagGen_mem_statedOmega {b c : F} (hm : 4 ≤ m) (t : Fˣ) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    diagGLMinusHom m F (Pi.mulSingle (threeToFinMinus hm i) t) ∈
      StatedOmega (StatedQuadMinus m F b c) := by
  rw [statedOmega_eq_comap (coe_quadMinus m F b c), Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom]
  set j : Fin (m - 1) := threeToFinMinus hm i with hj
  set d : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → Fˣ := minusDiagHom m F (Pi.mulSingle j t)
    with hddef
  have hdiag : diagGLMinusHom m F (Pi.mulSingle j t) = TauCeti.diagGL d := rfl
  rw [hdiag]
  have horth : ∀ k, k ≠ Sum.inl j → k ≠ Sum.inr (Sum.inl j) →
      polar (quadMinus m F b c) (Pi.single (Sum.inl j) 1) (Pi.single k 1) = 0 ∧
        polar (quadMinus m F b c) (Pi.single (Sum.inr (Sum.inl j)) 1) (Pi.single k 1) = 0 := by
    intro k h1 h2
    rcases k with j' | j' | u
    · constructor
      · rw [polar_quadMinus_single_inl]; simp
      · rw [polar_quadMinus_single_inl]
        simp [show j ≠ j' from fun h => h1 (by rw [h])]
    · constructor
      · rw [polar_quadMinus_single_inr_inl]
        simp [show j ≠ j' from fun h => h2 (by rw [h])]
      · rw [polar_quadMinus_single_inr_inl]; simp
    · fin_cases u
      · constructor <;>
          simp [polar_quadMinus_single_inr_inr_zero, polar_quadMinus_single_inr_inr_one]
      · constructor <;>
          simp [polar_quadMinus_single_inr_inr_zero, polar_quadMinus_single_inr_inr_one]
  have hstep := reflect_mul_reflect_eq_diagGL (Q := quadMinus m F b c) (e := Sum.inl j)
    (f := Sum.inr (Sum.inl j)) (by simp) t d (by simp [hddef]) (by simp [hddef]) (by
      intro k h1 h2
      rcases k with j' | j' | u
      · rw [hddef, minusDiagHom_inl,
          Pi.mulSingle_eq_of_ne (show j' ≠ j from fun h => h1 (by rw [h]))]
      · rw [hddef, minusDiagHom_inr_inl,
          Pi.mulSingle_eq_of_ne (show j' ≠ j from fun h => h2 (by rw [h]))]
        simp
      · rw [hddef]
        simp) (quadMinus_single_inl j) (quadMinus_single_inr j)
    (by rw [polar_quadMinus_single_inr_inl]; simp) horth
  rw [← hstep]
  refine mem_of_odd_pow_of_sq_mem (N :=
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus m F b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus m F b c)⁆) ?_ hodd ?_
  · intro x hx
    subst hx
    have hsq : (reflect (quadMinus m F b c) (Pi.single (Sum.inl j) 1 +
          Pi.single (Sum.inr (Sum.inl j)) 1) *
          reflect (quadMinus m F b c) (Pi.single (Sum.inl j) 1 +
            (t : F) • Pi.single (Sum.inr (Sum.inl j)) 1)) ^ 2 =
        ⁅reflect (quadMinus m F b c) (Pi.single (Sum.inl j) 1 +
            Pi.single (Sum.inr (Sum.inl j)) 1),
          reflect (quadMinus m F b c) (Pi.single (Sum.inl j) 1 +
            (t : F) • Pi.single (Sum.inr (Sum.inl j)) 1)⁆ := by
      rw [pow_two, commutatorElement_def, reflect_inv, reflect_inv]
      group
    rw [hsq]
    exact Subgroup.commutator_mem_commutator
      (reflect_mem_orthogonalGroup (quadMinus m F b c) _)
      (reflect_mem_orthogonalGroup (quadMinus m F b c) _)
  · rw [hstep, ← hdiag, ← map_pow (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F),
      ← map_pow (diagGLMinusHom m F), ← Pi.mulSingle_pow, ← ht, pow_orderOf_eq_one,
      Pi.mulSingle_one]
    simp

@[expose] noncomputable def diagGenMinus (b c : F) (t : Fˣ) (hm : 4 ≤ m) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    StatedOmega (StatedQuadMinus m F b c) :=
  ⟨diagGLMinusHom m F (Pi.mulSingle (threeToFinMinus hm i) t),
    minusDiagGen_mem_statedOmega (b := b) (c := c) hm t i hodd ht⟩

@[simp]
theorem coe_diagGenMinus (b c : F) (t : Fˣ) (hm : 4 ≤ m) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    ((diagGenMinus b c t hm i hodd ht : StatedOmega (StatedQuadMinus m F b c)) :
        GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F) =
      diagGLMinusHom m F (Pi.mulSingle (threeToFinMinus hm i) t) :=
  rfl

theorem orderOf_diagGenMinus (b c : F) (t : Fˣ) (hm : 4 ≤ m) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    orderOf (diagGenMinus b c t hm i hodd ht) = q := by
  rw [← orderOf_injective (Subgroup.subtype (StatedOmega (StatedQuadMinus m F b c)))
    Subtype.coe_injective]
  change orderOf (diagGLMinusHom m F (Pi.mulSingle (threeToFinMinus hm i) t)) = q
  rw [orderOf_injective (diagGLMinusHom m F) (diagGLMinusHom_injective m F),
    orderOf_piMulSingle, ht]

theorem commute_diagGenMinus (b c : F) (t : Fˣ) (hm : 4 ≤ m) (i j : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    Commute (diagGenMinus b c t hm i hodd ht) (diagGenMinus b c t hm j hodd ht) := by
  rw [commute_iff_eq]
  apply Subtype.ext
  change diagGLMinusHom m F (Pi.mulSingle (threeToFinMinus hm i) t) *
      diagGLMinusHom m F (Pi.mulSingle (threeToFinMinus hm j) t) =
    diagGLMinusHom m F (Pi.mulSingle (threeToFinMinus hm j) t) *
      diagGLMinusHom m F (Pi.mulSingle (threeToFinMinus hm i) t)
  rw [← map_mul, ← map_mul, mul_comm]

@[expose] noncomputable def omegaActMinus (m : ℕ) (F : Type) [Field F] (b c : F) :
    StatedOmega (StatedQuadMinus m F b c) →*
      ((Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → F) ≃ₗ[F]
        (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → F)) :=
  (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F).toMonoidHom.comp
    (Subgroup.subtype (StatedOmega (StatedQuadMinus m F b c)))

theorem omegaActMinus_apply (b c : F) (A : StatedOmega (StatedQuadMinus m F b c))
    (v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → F) :
    omegaActMinus m F b c A v =
      ((A : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F) :
        Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
          (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F) *ᵥ v :=
  rfl

theorem omegaAct_diagGenMinus_zpow_single (b c : F) (t : Fˣ) (hm : 4 ≤ m) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) (a : ℤ)
    (k : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) :
    omegaActMinus m F b c ((diagGenMinus b c t hm i hodd ht) ^ a) (Pi.single k 1) =
      Pi.single k
        (((minusDiagHom m F (Pi.mulSingle (threeToFinMinus hm i) (t ^ a))) k : Fˣ) : F) := by
  rw [omegaActMinus_apply, Subgroup.coe_zpow, coe_diagGenMinus,
    ← map_zpow (diagGLMinusHom m F), ← Pi.mulSingle_zpow, coe_diagGLMinusHom]
  ext j
  rw [Matrix.mulVec_diagonal]
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [Pi.single_eq_of_ne hjk]

theorem omegaAct_diagGenMinus_zpow_single_self (b c : F) (t : Fˣ) (hm : 4 ≤ m) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) (a : ℤ) :
    omegaActMinus m F b c ((diagGenMinus b c t hm i hodd ht) ^ a)
        (Pi.single (Sum.inl (threeToFinMinus hm i)) 1) =
      Pi.single (Sum.inl (threeToFinMinus hm i)) (((t ^ a : Fˣ) : F)) := by
  rw [omegaAct_diagGenMinus_zpow_single, minusDiagHom_inl, Pi.mulSingle_eq_same]

theorem omegaAct_diagGenMinus_single_of_ne (b c : F) (t : Fˣ) (hm : 4 ≤ m)
    {i j : Fin 3} (hij : i ≠ j) {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    omegaActMinus m F b c (diagGenMinus b c t hm i hodd ht)
        (Pi.single (Sum.inl (threeToFinMinus hm j)) 1) =
      Pi.single (Sum.inl (threeToFinMinus hm j)) 1 := by
  have hne : threeToFinMinus hm i ≠ threeToFinMinus hm j := fun h =>
    hij (threeToFinMinus_injective hm h)
  have h := omegaAct_diagGenMinus_zpow_single (b := b) (c := c) (t := t) (hm := hm) (i := i)
    (hodd := hodd) (ht := ht) (a := 1) (k := Sum.inl (threeToFinMinus hm j))
  simpa [hne, Ne.symm hne] using h

theorem dvd_of_diagGenMinus_zpow_fixes (b c : F) (t : Fˣ) (hm : 4 ≤ m) (i : Fin 3)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) {a : ℤ}
    (h : omegaActMinus m F b c ((diagGenMinus b c t hm i hodd ht) ^ a)
        (Pi.single (Sum.inl (threeToFinMinus hm i)) 1) =
      Pi.single (Sum.inl (threeToFinMinus hm i)) 1) :
    (q : ℤ) ∣ a := by
  rw [omegaAct_diagGenMinus_zpow_single_self] at h
  have hval : ((t ^ a : Fˣ) : F) = 1 := by
    have := congrFun h (Sum.inl (threeToFinMinus hm i))
    simpa using this
  have hta : t ^ a = 1 := Units.ext hval
  rw [← ht, orderOf_dvd_iff_zpow_eq_one]
  exact hta

end CFSG.ClassicalGroups.Orthogonal

end
