module

public import Mathlib
public import CFSG.Open.StatedDefs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34C3

open CFSG.Open Matrix

variable {F : Type} [Field F]

@[expose] def dM (ω : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]

@[expose] def cM : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem det_dM {ω : F} (h3 : ω ^ 3 = 1) : (dM ω).det = 1 := by
  rw [dM, det_fin_three]
  simp
  linear_combination h3

theorem det_cM : (cM : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  rw [cM, det_fin_three]
  simp

theorem cM_mul_dM {ω : F} (h3 : ω ^ 3 = 1) : (cM : Matrix (Fin 3) (Fin 3) F) * dM ω =
    ω • (dM ω * cM) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cM, dM, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination (-1 : F) * h3


section Group

@[expose] noncomputable def dG {ω : F} (h3 : ω ^ 3 = 1) : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (dM ω) (by rw [det_dM h3]; exact one_ne_zero)

@[expose] noncomputable def cG : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero cM (by rw [det_cM]; exact one_ne_zero)

theorem coe_dG {ω : F} (h3 : ω ^ 3 = 1) : ((dG h3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    dM ω := rfl

theorem coe_cG : ((cG : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = cM := rfl

theorem dG_mem {ω : F} (h3 : ω ^ 3 = 1) : dG h3 ∈ StatedSL 3 F :=
  Subgroup.subset_closure (by simp [coe_dG, det_dM h3])

theorem cG_mem : (cG : GL (Fin 3) F) ∈ StatedSL 3 F :=
  Subgroup.subset_closure (by simp [coe_cG, det_cM])

theorem cG_mul_dG {ω : F} (h0 : ω ≠ 0) (h3 : ω ^ 3 = 1) :
    (cG : GL (Fin 3) F) * dG h3 =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω h0) * (dG h3 * cG) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
    coe_dG, coe_cG, cM_mul_dM h3]
  simp [Matrix.smul_eq_diagonal_mul]

end Group


section Proj

theorem scalar_comm (u : Fˣ) (g : GL (Fin 3) F) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  exact (Subgroup.mem_center_iff.1 hz g).symm

theorem mk_eq_of_scalar {a b : ↥(StatedSL 3 F)} {u : Fˣ}
    (h : (b : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) u * a) :
    (QuotientGroup.mk a : StatedProj (StatedSL 3 F)) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  show ((a⁻¹ * b : ↥(StatedSL 3 F)) : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F
  rw [Subgroup.coe_mul, Subgroup.coe_inv, h, scalar_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  exact ⟨u, rfl⟩

theorem scalar_of_mk_eq {a b : ↥(StatedSL 3 F)}
    (h : (QuotientGroup.mk a : StatedProj (StatedSL 3 F)) = QuotientGroup.mk b) :
    ∃ u : Fˣ, (b : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) u * a := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  have h1 : (b : GL (Fin 3) F) = a * ((a⁻¹ * b : ↥(StatedSL 3 F)) : GL (Fin 3) F) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [h1, ← hu, scalar_comm]

end Proj


section Main

variable [Finite F]

theorem exists_noncyclic_three_subgroup {ω : F} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    ∃ E : Subgroup (StatedProj (StatedSL 3 F)), IsPGroup 3 E ∧ ¬ IsCyclic E := by
  classical
  have h0 : ω ≠ 0 := by
    rintro rfl
    norm_num at h3
  let dH : ↥(StatedSL 3 F) := ⟨dG h3, dG_mem h3⟩
  let cH : ↥(StatedSL 3 F) := ⟨cG, cG_mem⟩
  let d : StatedProj (StatedSL 3 F) := QuotientGroup.mk dH
  let c : StatedProj (StatedSL 3 F) := QuotientGroup.mk cH
  have hdc : d * c = c * d := by
    show (QuotientGroup.mk dH : StatedProj (StatedSL 3 F)) * QuotientGroup.mk cH =
      QuotientGroup.mk cH * QuotientGroup.mk dH
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact mk_eq_of_scalar (u := Units.mk0 ω h0) (cG_mul_dG h0 h3)
  have hdM : dM ω = Matrix.diagonal ![1, ω, ω ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dM]
  have hdH3 : dH ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_dG, hdM, Matrix.diagonal_pow]
    show Matrix.diagonal (![1, ω, ω ^ 2] ^ 3) = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp
    · simpa using h3
    · simp only [Fin.reduceFinMk, Matrix.cons_val, Pi.pow_apply, Pi.one_apply]
      rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
  have hcH3 : cH ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_cG]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cM, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  have hd3 : d ^ 3 = 1 := by
    show (QuotientGroup.mk dH : StatedProj (StatedSL 3 F)) ^ 3 = 1
    rw [← QuotientGroup.mk_pow, hdH3, QuotientGroup.mk_one]
  have hc3 : c ^ 3 = 1 := by
    show (QuotientGroup.mk cH : StatedProj (StatedSL 3 F)) ^ 3 = 1
    rw [← QuotientGroup.mk_pow, hcH3, QuotientGroup.mk_one]
  have hc : ∀ g : ↥(StatedSL 3 F), ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 →
      (QuotientGroup.mk g : StatedProj (StatedSL 3 F)) ≠ c := by
    intro g hg hgc
    obtain ⟨u, hu⟩ := scalar_of_mk_eq hgc
    have := congrArg (fun A : GL (Fin 3) F => ((A : Matrix (Fin 3) (Fin 3) F)) 0 1) hu
    simp [coe_cG, cM, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_three,
      hg] at this
    have h01 : ((cH : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 = 1 := by
      show (cM : Matrix (Fin 3) (Fin 3) F) 0 1 = 1
      simp [cM]
    rw [h01] at this
    exact one_ne_zero this
  have hd01 : ∀ n : ℕ,
      (((dH ^ n : ↥(StatedSL 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
    intro n
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    show ((dM ω) ^ n) 0 1 = 0
    rw [hdM, Matrix.diagonal_pow]
    exact Matrix.diagonal_apply_ne _ (by decide)
  have hd1 : d ≠ 1 := by
    intro h
    have h' : (QuotientGroup.mk dH : StatedProj (StatedSL 3 F)) = QuotientGroup.mk 1 := by
      rw [QuotientGroup.mk_one]
      exact h
    obtain ⟨u, hu⟩ := scalar_of_mk_eq h'
    have e00 := congrArg (fun A : GL (Fin 3) F => ((A : Matrix (Fin 3) (Fin 3) F)) 0 0) hu
    have e11 := congrArg (fun A : GL (Fin 3) F => ((A : Matrix (Fin 3) (Fin 3) F)) 1 1) hu
    have hdd : ((dH : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dM ω := rfl
    simp only [Subgroup.coe_one, Units.val_one, Units.val_mul, hdd,
      Matrix.GeneralLinearGroup.coe_scalar] at e00 e11
    simp [dM, Matrix.smul_eq_diagonal_mul] at e00 e11
    apply h1
    rw [← e00] at e11
    simpa using e11.symm
  have hcomm : ∀ x ∈ Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))),
      ∀ y ∈ Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))), x * y = y * x := by
    have h1' : Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))) ≤
        Subgroup.centralizer ({d, c} : Set (StatedProj (StatedSL 3 F))) := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rcases hx with rfl | rfl
      · intro h hh
        rcases hh with rfl | rfl
        · rfl
        · exact hdc.symm
      · intro h hh
        rcases hh with rfl | rfl
        · exact hdc
        · rfl
    intro x hx y hy
    have h2 : Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))) ≤
        Subgroup.centralizer ({x} : Set (StatedProj (StatedSL 3 F))) := by
      rw [Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((Subgroup.mem_centralizer_iff.1 (h1' hx)) z hz).symm
    exact (Subgroup.mem_centralizer_iff.1 (h2 hy)) x rfl
  have hcube : ∀ x ∈ Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))), x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hd3
      · exact hc3
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      rw [Commute.mul_pow (show Commute x y from hcomm x hx y hy) 3, ihx, ihy, mul_one]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  refine ⟨Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))), ?_, ?_⟩
  · intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hcube g.1 g.2
  · intro hcyc
    classical
    haveI : Fintype (Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F)))) :=
      Fintype.ofFinite _
    have hmem_d : d ∈ Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))) :=
      Subgroup.subset_closure (by simp)
    have hmem_c : c ∈ Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))) :=
      Subgroup.subset_closure (by simp)
    have hd2 : d ^ 2 ≠ 1 := by
      intro h
      apply hd1
      calc d = d ^ 3 * (d ^ 2)⁻¹ := by group
        _ = 1 := by rw [hd3, h, inv_one, one_mul]
    have hdd2 : d ≠ d ^ 2 := by
      intro h
      apply hd1
      calc d = d ^ 2 * d⁻¹ := by group
        _ = 1 := by rw [← h, mul_inv_cancel]
    have hc1 : c ≠ 1 := by
      intro h
      apply hc 1 (by simp)
      rw [QuotientGroup.mk_one]
      exact h.symm
    have hdc' : d ≠ c := fun h => hc dH (by simpa using hd01 1) h
    have hd2c : d ^ 2 ≠ c := fun h => hc (dH ^ 2) (hd01 2) (by
      rw [QuotientGroup.mk_pow]
      exact h)
    let e0 : Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))) := 1
    let e1 : Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))) := ⟨d, hmem_d⟩
    let e2 : Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))) :=
      ⟨d ^ 2, Subgroup.pow_mem _ hmem_d 2⟩
    let e3 : Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))) := ⟨c, hmem_c⟩
    have hne01 : e0 ≠ e1 := fun h => hd1 (congrArg Subtype.val h).symm
    have hne02 : e0 ≠ e2 := fun h => hd2 (congrArg Subtype.val h).symm
    have hne03 : e0 ≠ e3 := fun h => hc1 (congrArg Subtype.val h).symm
    have hne12 : e1 ≠ e2 := fun h => hdd2 (congrArg Subtype.val h)
    have hne13 : e1 ≠ e3 := fun h => hdc' (congrArg Subtype.val h)
    have hne23 : e2 ≠ e3 := fun h => hd2c (congrArg Subtype.val h)
    have hcard : ({e0, e1, e2, e3} : Finset _).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hne23]
      · simp [hne12, hne13]
      · simp [hne01, hne02, hne03]
    have hsub : ({e0, e1, e2, e3} : Finset _) ⊆
        Finset.univ.filter (fun a : Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F))) =>
          a ^ 3 = 1) := by
      intro a ha
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      simpa using hcube a.1 a.2
    have h4 := Finset.card_le_card hsub
    have h3' := IsCyclic.card_pow_eq_one_le
      (α := Subgroup.closure ({d, c} : Set (StatedProj (StatedSL 3 F)))) (n := 3) (by norm_num)
    rw [hcard] at h4
    omega

end Main

end CFSG.HardMathSupport.Dickson.Sec6.Up34C3
