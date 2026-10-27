module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open scoped Matrix commutatorElement

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U43

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem zetaBData_iota_inv (ι : OGroup Q →* Matrix (Fin 6) (Fin 6) (ZMod 3))
    (horth : ∀ g, ι g * (ι g)ᵀ = 1) (x : OGroup Q) : ι x⁻¹ = (ι x)ᵀ := by
  have h1 : ι x * ι x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc ι x⁻¹ = (ι x)⁻¹ := (Matrix.inv_eq_right_inv h1).symm
    _ = (ι x)ᵀ := Matrix.inv_eq_right_inv (horth x)

private theorem zetaBData_squareClassHom_two_ne_one (h : (2 : ZMod 3) ≠ 0) :
    TauCeti.squareClassHom (Units.mk0 (2 : ZMod 3) h) ≠ 1 := by
  intro h1
  have hsq : IsSquare (Units.mk0 (2 : ZMod 3) h) := by
    rw [← MonoidHom.mem_ker, TauCeti.ker_squareClassHom, Subgroup.mem_square] at h1
    exact h1
  obtain ⟨b, hb⟩ := hsq
  have hbval : (b : ZMod 3) * (b : ZMod 3) = 2 := by
    have := congrArg (Units.val) hb
    simpa using this.symm
  exact (by decide : ∀ x : ZMod 3, x * x ≠ 2) (b : ZMod 3) hbval

private theorem zetaBData_zMatA_mul_zMatB_ne :
    zMatA * zMatB ≠ zMatB * zMatA := by
  decide +kernel

theorem zetaOmegaData_of_frameHom (hF : ZetaFrameHom) (hM : ZetaMatrixFacts) :
    ZetaOmegaData := by
  unfold ZetaOmegaData
  intro V instAC instMod instFD Q hQ hdim hsgn
  unfold ZetaFrameHom at hF
  unfold ZetaMatrixFacts at hM
  obtain ⟨hne, hAq, hBq, hGq, hrel, hcover, _hA_ne_one, _hA_ne_neg_one, hUV⟩ := hM
  obtain ⟨ι, hinj, horth, hπ, hπΩ, hrefl⟩ := hF hQ hdim hsgn
  classical
  let r : (Fin 6 → ZMod 3) → OGroup Q := fun v =>
    if h : v ⬝ᵥ v ≠ 0 then (hrefl v h).choose else 1
  let qu : (Fin 6 → ZMod 3) → (ZMod 3)ˣ := fun v =>
    if h : v ⬝ᵥ v ≠ 0 then Units.mk0 (v ⬝ᵥ v) h else 1
  have hr_iota : ∀ (v : Fin 6 → ZMod 3) (h : v ⬝ᵥ v ≠ 0), ι (r v) = zRefl v := by
    intro v h
    show ι (if h' : v ⬝ᵥ v ≠ 0 then (hrefl v h').choose else 1) = zRefl v
    rw [dif_pos h]
    exact (hrefl v h).choose_spec.1
  have hr_dsn' : ∀ (v : Fin 6 → ZMod 3), v ⬝ᵥ v ≠ 0 →
      detSpinorNorm hQ (r v) = ((-1 : (ZMod 3)ˣ), TauCeti.squareClassHom (qu v)) := by
    intro v h
    have h1 : detSpinorNorm hQ (r v) =
        ((-1 : (ZMod 3)ˣ), TauCeti.squareClassHom (Units.mk0 (v ⬝ᵥ v) h)) := by
      show detSpinorNorm hQ
        (if h' : v ⬝ᵥ v ≠ 0 then (hrefl v h').choose else 1) = _
      rw [dif_pos h]
      exact (hrefl v h).choose_spec.2
    rw [h1]
    congr 1
    show TauCeti.squareClassHom (Units.mk0 (v ⬝ᵥ v) h) =
      TauCeti.squareClassHom (if h' : v ⬝ᵥ v ≠ 0 then Units.mk0 (v ⬝ᵥ v) h' else 1)
    rw [dif_pos h]
  have hlA : ∀ v ∈ zVecsA, v ⬝ᵥ v ≠ 0 := by
    intro v hv
    exact hne v (by simp [hv])
  have hlB : ∀ v ∈ zVecsB, v ⬝ᵥ v ≠ 0 := by
    intro v hv
    exact hne v (by simp [hv])
  have hlG : ∀ v ∈ zVecsG, v ⬝ᵥ v ≠ 0 := by
    intro v hv
    exact hne v (by simp [hv])
  have hqu_val : ∀ (l : List (Fin 6 → ZMod 3)), (∀ v ∈ l, v ⬝ᵥ v ≠ 0) →
      ((l.map qu).prod : ZMod 3) = (l.map fun v => v ⬝ᵥ v).prod := by
    intro l hl
    change Units.coeHom (ZMod 3) ((l.map qu).prod) = (l.map fun v => v ⬝ᵥ v).prod
    rw [map_list_prod, List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro v hv
    show ((qu v : (ZMod 3)ˣ) : ZMod 3) = v ⬝ᵥ v
    show ((if h : v ⬝ᵥ v ≠ 0 then Units.mk0 (v ⬝ᵥ v) h else 1 : (ZMod 3)ˣ) : ZMod 3) =
      v ⬝ᵥ v
    rw [dif_pos (hl v hv)]
    rfl
  have hqu_prod_one : ∀ (l : List (Fin 6 → ZMod 3)), (∀ v ∈ l, v ⬝ᵥ v ≠ 0) →
      (l.map fun v => v ⬝ᵥ v).prod = 1 → (l.map qu).prod = 1 := by
    intro l hl hp
    apply Units.ext
    rw [hqu_val l hl, hp]
    rfl
  have hpair_prod : ∀ (l : List (Fin 6 → ZMod 3)), (∀ v ∈ l, v ⬝ᵥ v ≠ 0) →
      (l.map fun v => detSpinorNorm hQ (r v)).prod =
        (((-1 : (ZMod 3)ˣ) ^ l.length, TauCeti.squareClassHom ((l.map qu).prod))) := by
    intro l
    induction l with
    | nil =>
        intro _
        refine Prod.ext rfl ?_
        have h : TauCeti.squareClass (1 : (ZMod 3)ˣ) = 0 := by
          rw [TauCeti.squareClass_eq_zero_iff]
          exact ⟨1, by simp⟩
        simp [h]
    | cons a tl ih =>
        intro hl
        have ha : a ⬝ᵥ a ≠ 0 := hl a (by simp)
        have htl : ∀ v ∈ tl, v ⬝ᵥ v ≠ 0 := fun v hv => hl v (by simp [hv])
        simp only [List.map_cons, List.prod_cons, List.length_cons]
        rw [ih htl, hr_dsn' a ha]
        simp only [List.map_cons, List.prod_cons, pow_succ, map_mul]
        exact Prod.ext (mul_comm _ _) rfl
  set A₀ : OGroup Q := (zVecsA.map r).prod with hA₀
  set B₀ : OGroup Q := (zVecsB.map r).prod with hB₀
  set g : OGroup Q := (zVecsG.map r).prod with hg
  have hA_dsn : detSpinorNorm hQ A₀ = 1 := by
    rw [hA₀, map_list_prod, List.map_map]
    simp only [Function.comp_def]
    rw [hpair_prod zVecsA hlA, hqu_prod_one zVecsA hlA hAq, map_one,
      show zVecsA.length = 2 from by decide]
    refine Prod.ext ?_ rfl
    decide
  have hB_dsn : detSpinorNorm hQ B₀ = 1 := by
    rw [hB₀, map_list_prod, List.map_map]
    simp only [Function.comp_def]
    rw [hpair_prod zVecsB hlB, hqu_prod_one zVecsB hlB hBq, map_one,
      show zVecsB.length = 4 from by decide]
    refine Prod.ext ?_ rfl
    decide
  have hg_dsn : detSpinorNorm hQ g =
      (((-1 : (ZMod 3)ˣ) ^ zVecsG.length,
        TauCeti.squareClassHom ((zVecsG.map qu).prod))) := by
    rw [hg, map_list_prod, List.map_map]
    simp only [Function.comp_def]
    exact hpair_prod zVecsG hlG
  have hGunit : (zVecsG.map qu).prod = Units.mk0 (2 : ZMod 3) (by decide) := by
    apply Units.ext
    rw [hqu_val zVecsG hlG, hGq]
    rfl
  have hg_fst : (detSpinorNorm hQ g).1 = 1 := by
    rw [hg_dsn, show zVecsG.length = 2 from by decide]
    decide
  have hg_snd : (detSpinorNorm hQ g).2 ≠ 1 := by
    rw [hg_dsn, hGunit]
    exact zetaBData_squareClassHom_two_ne_one (by decide)
  have hπ_dsn : detSpinorNorm hQ (piOrth Q) = 1 := (mem_omegaGroup_iff hQ).mp hπΩ
  have hA_mem : A₀ ∈ omegaGroup hQ := by
    rw [mem_omegaGroup_iff hQ]
    exact hA_dsn
  have hB_mem : piOrth Q * B₀ ∈ omegaGroup hQ := by
    rw [mem_omegaGroup_iff hQ, map_mul, hπ_dsn, hB_dsn, one_mul]
  let A : omegaGroup hQ := ⟨A₀, hA_mem⟩
  let B : omegaGroup hQ := ⟨piOrth Q * B₀, hB_mem⟩
  have hA_iota : ι ((A : omegaGroup hQ) : OGroup Q) = zMatA := by
    change ι A₀ = zMatA
    rw [hA₀, map_list_prod, List.map_map]
    simp only [Function.comp_def, zMatA]
    apply congrArg List.prod
    apply List.map_congr_left
    intro v hv
    exact hr_iota v (hlA v hv)
  have hB₀_iota : ι B₀ = (zVecsB.map zRefl).prod := by
    rw [hB₀, map_list_prod, List.map_map]
    simp only [Function.comp_def]
    apply congrArg List.prod
    apply List.map_congr_left
    intro v hv
    exact hr_iota v (hlB v hv)
  have hB_iota : ι ((B : omegaGroup hQ) : OGroup Q) = zMatB := by
    change ι (piOrth Q * B₀) = zMatB
    rw [map_mul, hπ, hB₀_iota, zMatB]
    simp
  have hg_iota : ι g = zMatG := by
    rw [hg, map_list_prod, List.map_map]
    simp only [Function.comp_def, zMatG]
    apply congrArg List.prod
    apply List.map_congr_left
    intro v hv
    exact hr_iota v (hlG v hv)
  have hGG : zMatG * zMatGᵀ = 1 := by
    simpa [hg_iota] using horth g
  have hAB_iota : ∀ i : Fin 2,
      ι ((![A, B] i : omegaGroup hQ) : OGroup Q) = ![zMatA, zMatB] i := by
    intro i
    fin_cases i
    · simpa using hA_iota
    · simpa using hB_iota
  have hword : ∀ (f : Fin 2 → OGroup Q) (w : List (Fin 2 × Bool)),
      ι (FreeGroup.lift f (FreeGroup.mk w)) =
        zWordEval (fun i => ι (f i)) (fun i => (ι (f i))ᵀ) w := by
    intro f w
    rw [FreeGroup.lift_mk, map_list_prod, List.map_map]
    induction w with
    | nil => simp [zWordEval]
    | cons p tl ih =>
        obtain ⟨i, b⟩ := p
        cases b
        · simp only [List.map_cons, List.prod_cons, zWordEval, Bool.false_eq_true,
            if_false, List.map_map, Function.comp_apply, Bool.cond_false]
          rw [ih, zetaBData_iota_inv ι horth (f i)]
          simp only [zWordEval]
        · simp only [List.map_cons, List.prod_cons, zWordEval, if_true, List.map_map,
            Function.comp_apply, Bool.cond_true]
          rw [ih]
          simp only [zWordEval]
  have hcoe : ∀ w : List (Fin 2 × Bool),
      ((FreeGroup.lift ![A, B] (FreeGroup.mk w) : omegaGroup hQ) : OGroup Q) =
        FreeGroup.lift (fun i => ((![A, B] i : omegaGroup hQ) : OGroup Q))
          (FreeGroup.mk w) := by
    intro w
    let Φ : FreeGroup (Fin 2) →* OGroup Q :=
      (omegaGroup hQ).subtype.comp (FreeGroup.lift ![A, B])
    have hΦ : ∀ i, Φ (FreeGroup.of i) = ((![A, B] i : omegaGroup hQ) : OGroup Q) := by
      intro i
      simp [Φ]
    have h := FreeGroup.lift_unique Φ hΦ (x := FreeGroup.mk w)
    simpa [Φ] using h
  have hword_eval : ∀ w : List (Fin 2 × Bool),
      ι (((FreeGroup.lift ![A, B] (FreeGroup.mk w) : omegaGroup hQ) : OGroup Q)) =
        zEvalM w := by
    intro w
    rw [hcoe w, hword (fun i => ((![A, B] i : omegaGroup hQ) : OGroup Q)) w]
    have hY : (fun i => (ι ((![A, B] i : omegaGroup hQ) : OGroup Q))ᵀ) =
        ![zMatAᵀ, zMatBᵀ] := by
      funext i
      rw [hAB_iota i]
      fin_cases i <;> simp
    rw [show (fun i => ι ((![A, B] i : omegaGroup hQ) : OGroup Q)) = ![zMatA, zMatB]
      from funext hAB_iota, hY]
    rfl
  have hrel_center : ∀ r ∈ wordSet rels,
      FreeGroup.lift ![A, B] r ∈ Subgroup.center (omegaGroup hQ) := by
    intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    have hι : ι (((FreeGroup.lift ![A, B] (FreeGroup.mk r') : omegaGroup hQ) : OGroup Q)) =
        1 ∨ ι (((FreeGroup.lift ![A, B] (FreeGroup.mk r') : omegaGroup hQ) :
          OGroup Q)) = -1 := by
      rw [hword_eval r']
      exact hrel r' hr'
    rcases hι with h | h
    · have h1 : FreeGroup.lift ![A, B] (FreeGroup.mk r') = 1 := by
        apply Subtype.ext
        apply hinj
        simpa using h
      rw [h1]
      exact (Subgroup.center (omegaGroup hQ)).one_mem
    · have h2 : FreeGroup.lift ![A, B] (FreeGroup.mk r') = ⟨piOrth Q, hπΩ⟩ := by
        apply Subtype.ext
        apply hinj
        rw [h, hπ]
      rw [h2]
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext ((Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q))
        (x : OGroup Q)))
  have hcover_eq : ∀ i : Fin 2, FreeGroup.lift ![A, B] (zW i) = ![A, B] i := by
    intro i
    apply Subtype.ext
    apply hinj
    rw [zW, hword_eval (commWords (coverPairs i)), hcover i, hAB_iota i]
  have hA_not_center : A ∉ Subgroup.center (omegaGroup hQ) := by
    intro hc
    have hcomm : B * A = A * B := (Subgroup.mem_center_iff.mp hc) B
    have hmat : zMatB * zMatA = zMatA * zMatB := by
      have := congrArg (fun x : omegaGroup hQ => ι (x : OGroup Q)) hcomm
      simpa [hA_iota, hB_iota] using this
    exact zetaBData_zMatA_mul_zMatB_ne hmat.symm
  let U : Fin 2 → OGroup Q := fun k =>
    ((FreeGroup.lift ![A, B] (FreeGroup.mk (zU k)) : omegaGroup hQ) : OGroup Q)
  let W : Fin 2 → OGroup Q := fun k =>
    ((FreeGroup.lift ![A, B] (FreeGroup.mk (zV k)) : omegaGroup hQ) : OGroup Q)
  have hUeval : ∀ k, ι (U k) = zEvalM (zU k) := by
    intro k
    exact hword_eval (zU k)
  have hWeval : ∀ k, ι (W k) = zEvalM (zV k) := by
    intro k
    exact hword_eval (zV k)
  refine ⟨A, B, g, hg_fst, hg_snd, hrel_center, hcover_eq, hA_not_center, ?_⟩
  intro k
  refine ⟨?_, ?_, ?_⟩
  · change ⁅U k, W k⁆ = 1
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    apply hinj
    rw [map_mul, map_mul, hUeval k, hWeval k]
    exact (hUV k).1
  · change g * U k * g⁻¹ = U k
    apply hinj
    rw [map_mul, map_mul, zetaBData_iota_inv ι horth g, hg_iota, hUeval k, (hUV k).2.1,
      mul_assoc, hGG, mul_one]
  · change g * W k * g⁻¹ = (W k)⁻¹
    apply hinj
    rw [map_mul, map_mul, zetaBData_iota_inv ι horth g, hg_iota, hWeval k,
      zetaBData_iota_inv ι horth (W k), hWeval k]
    exact (hUV k).2.2

end CFSG.OddStandard.SmallF3.Omega
