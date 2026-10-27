module

public import CFSG.LieType.Chevalley.C2E6FirstResidueFlags
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap Matrix Module
  CFSG.LocalAnalysis.ComponentInitial

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem transvection_mulVec (i j : Fin 6) (c : K) (w : Fin 6 → K) :
    transvection i j c *ᵥ w = w + (c * w j) • uVec i := by
  rw [transvection, add_mulVec, one_mulVec, single_mulVec_eq]

theorem matrix_eq_of_mulVec {A B : Matrix (Fin 6) (Fin 6) K} (h : ∀ w, A *ᵥ w = B *ᵥ w) :
    A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun w => by
    simp only [Matrix.toLin'_apply]
    exact h w)

theorem transvection_comm {i j k l : Fin 6} (hjk : j ≠ k) (hli : l ≠ i) (c d : K) :
    transvection i j c * transvection k l d = transvection k l d * transvection i j c := by
  refine matrix_eq_of_mulVec fun w => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, transvection_mulVec, transvection_mulVec,
    transvection_mulVec, transvection_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, uVec, Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hli,
    smul_eq_mul, mul_zero, add_zero]
  abel

theorem tauSL_upAdj (t : Fin 5) (c : K) : tauSL (upAdj t c) = upAdj (Fin.rev t) (bar c) := by
  rw [MonoidHom.comp_apply, barSL_upAdj, thetaSL_upAdj]

theorem tauSL_downAdj (t : Fin 5) (c : K) :
    tauSL (downAdj t c) = downAdj (Fin.rev t) (bar c) := by
  rw [MonoidHom.comp_apply, barSL_downAdj, thetaSL_downAdj]

theorem mem_SU6_of_tauSL {g : SpecialLinearGroup (Fin 6) K} (hg : tauSL g = g) : g ∈ SU6 :=
  hg

abbrev wAdj (t : Fin 5) : SpecialLinearGroup (Fin 6) K := upAdj t 1 * downAdj t (-1) * upAdj t 1

theorem wAdj_mulVec_uVec : ∀ (t : Fin 5) (j : Fin 6),
    ((wAdj t : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ uVec j =
      uVec (Equiv.swap t.castSucc t.succ j) := by
  decide

@[expose] def weylMat : Fin 3 → SpecialLinearGroup (Fin 6) K :=
  ![wAdj 0 * wAdj 4, wAdj 1 * wAdj 3, wAdj 2]

@[expose] def weylPerm : Fin 3 → Equiv.Perm (Fin 6) :=
  ![Equiv.swap 0 1 * Equiv.swap 4 5, Equiv.swap 1 2 * Equiv.swap 3 4, Equiv.swap 2 3]

theorem weylMat_mulVec_uVec (d : Fin 3) (j : Fin 6) :
    ((weylMat d : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ uVec j =
      uVec (weylPerm d j) := by
  fin_cases d
  · change ((wAdj 0 : Matrix (Fin 6) (Fin 6) K) * (wAdj 4 : Matrix (Fin 6) (Fin 6) K)) *ᵥ
      uVec j = _
    rw [← mulVec_mulVec, wAdj_mulVec_uVec, wAdj_mulVec_uVec]
    rfl
  · change ((wAdj 1 : Matrix (Fin 6) (Fin 6) K) * (wAdj 3 : Matrix (Fin 6) (Fin 6) K)) *ᵥ
      uVec j = _
    rw [← mulVec_mulVec, wAdj_mulVec_uVec, wAdj_mulVec_uVec]
    rfl
  · exact wAdj_mulVec_uVec 2 j

theorem weylMat_mem_SU6 : ∀ d : Fin 3, weylMat d ∈ SU6 := by
  intro d
  refine (mem_SU6_iff _).mpr ?_
  revert d
  decide

@[expose] def weylSU (d : Fin 3) : SU6 := ⟨weylMat d, weylMat_mem_SU6 d⟩

@[expose] def bUp (d : Fin 3) (a : K) : SpecialLinearGroup (Fin 6) K :=
  ![upAdj 0 a * upAdj 4 (bar a), upAdj 1 a * upAdj 3 (bar a), upAdj 2 a] d

theorem bUp_mem_SU6 (d : Fin 3) {a : K} (ha : d ≠ 2 ∨ bar a = a) : bUp d a ∈ SU6 := by
  apply mem_SU6_of_tauSL
  fin_cases d
  · change tauSL (upAdj 0 a * upAdj 4 (bar a)) = upAdj 0 a * upAdj 4 (bar a)
    rw [map_mul, tauSL_upAdj, tauSL_upAdj, bar_bar]
    exact Subtype.ext (transvection_comm (by decide) (by decide) _ _)
  · change tauSL (upAdj 1 a * upAdj 3 (bar a)) = upAdj 1 a * upAdj 3 (bar a)
    rw [map_mul, tauSL_upAdj, tauSL_upAdj, bar_bar]
    exact Subtype.ext (transvection_comm (by decide) (by decide) _ _)
  · change tauSL (upAdj 2 a) = upAdj 2 a
    rw [tauSL_upAdj, ha.resolve_left (by decide)]

theorem bUp_mulVec (d : Fin 3) (a : K) (w : Fin 6 → K) :
    ((bUp d a : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w =
      ![w + (a * w 1) • uVec 0 + (bar a * w 5) • uVec 4,
        w + (a * w 2) • uVec 1 + (bar a * w 4) • uVec 3, w + (a * w 3) • uVec 2] d := by
  fin_cases d
  · change ((upAdj 0 a : Matrix (Fin 6) (Fin 6) K) * (upAdj 4 (bar a) : Matrix (Fin 6) (Fin 6) K))
      *ᵥ w = _
    rw [← mulVec_mulVec]
    change transvection 0 1 a *ᵥ (transvection 4 5 (bar a) *ᵥ w) = _
    rw [transvection_mulVec, transvection_mulVec]
    simp
    abel
  · change ((upAdj 1 a : Matrix (Fin 6) (Fin 6) K) * (upAdj 3 (bar a) : Matrix (Fin 6) (Fin 6) K))
      *ᵥ w = _
    rw [← mulVec_mulVec]
    change transvection 1 2 a *ᵥ (transvection 3 4 (bar a) *ᵥ w) = _
    rw [transvection_mulVec, transvection_mulVec]
    simp
    abel
  · change transvection 2 3 a *ᵥ w = _
    rw [transvection_mulVec]
    rfl

theorem bUp_mem_upperTriangular (d : Fin 3) (a : K) : bUp d a ∈ LinearFlag.upperTriangular 6 K := by
  have hT : ∀ (t : Fin 5) (c : K), upAdj t c ∈ LinearFlag.upperTriangular 6 K := by
    intro t c i j hij
    change transvection t.castSucc t.succ c i j = 0
    rw [transvection, Matrix.add_apply, one_apply_ne (ne_of_gt hij), zero_add, single_apply]
    rw [ite_eq_right]
    rintro ⟨rfl, rfl⟩
    exact absurd hij (not_lt.mpr (Fin.castSucc_lt_succ (i := t)).le)
  fin_cases d
  · exact mul_mem (hT 0 a) (hT 4 _)
  · exact mul_mem (hT 1 a) (hT 3 _)
  · exact hT 2 a

@[expose] def bUpSU (d : Fin 3) {a : K} (ha : d ≠ 2 ∨ bar a = a) : SU6 :=
  ⟨bUp d a, bUp_mem_SU6 d ha⟩

theorem bUpSU_smul_baseFlag (d : Fin 3) {a : K} (ha : d ≠ 2 ∨ bar a = a) :
    bUpSU d ha • baseFlag = baseFlag :=
  (smul_baseFlag_eq_iff _).mpr (bUp_mem_upperTriangular d a)

theorem suLin_mul_apply (g h : SU6) (v : Fin 6 → K) : suLin (g * h) v = suLin g (suLin h v) := by
  rw [suLin_mul]
  rfl

theorem suLin_inv_apply (g : SU6) (v : Fin 6 → K) : suLin g⁻¹ (suLin g v) = v := by
  rw [← suLin_mul_apply, inv_mul_cancel, suLin_one]
  rfl

theorem map_preSpan_eq_iff_mulVec (h : SpecialLinearGroup (Fin 6) K) (k : ℕ) :
    (preSpan k).map (SpecialLinearGroup.toLin' h : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
        preSpan k ↔
      ∀ j : Fin 6, (j : ℕ) < k → (h : Matrix (Fin 6) (Fin 6) K) *ᵥ uVec j ∈ preSpan k := by
  rw [map_preSpan_eq_iff]
  constructor
  · intro H j hj i hi
    rw [mulVec_uVec]
    exact H i j hj hi
  · intro H i j hj hi
    have := H j hj i hi
    rwa [mulVec_uVec] at this

theorem smul_baseFlag_sub_eq_iff (h : SU6) (k : Fin 3) :
    (h • baseFlag).sub k = baseFlag.sub k ↔
      ∀ j : Fin 6, (j : ℕ) ≤ k → suLin h (uVec j) ∈ preSpan (k + 1) := by
  rw [smul_sub, baseFlag_sub]
  exact (map_preSpan_eq_iff_mulVec (h : SpecialLinearGroup (Fin 6) K) (k + 1)).trans
    ⟨fun H j hj => H j (by omega), fun H j hj => H j (by omega)⟩

theorem suLin_mem_preSpan {h : SU6} {k : Fin 3} (hk : (h • baseFlag).sub k = baseFlag.sub k)
    {v : Fin 6 → K} (hv : v ∈ preSpan (k + 1)) : suLin h v ∈ preSpan (k + 1) := by
  have : suLin h v ∈ (h • baseFlag).sub k := Submodule.mem_map_of_mem hv
  rwa [hk] at this

theorem inv_smul_baseFlag_sub {h : SU6} {k : Fin 3} (hk : (h • baseFlag).sub k = baseFlag.sub k) :
    (h⁻¹ • baseFlag).sub k = baseFlag.sub k := by
  have e : ((h⁻¹ * h) • baseFlag).sub k = (h⁻¹ • baseFlag).sub k := by
    rw [mul_smul, smul_sub h⁻¹ (h • baseFlag), hk, ← smul_sub]
  rw [inv_mul_cancel, one_smul] at e
  exact e.symm

theorem smul_baseFlag_eq_of_cols (s : SU6)
    (hs : ∀ j : Fin 6, (j : ℕ) < 3 → suLin s (uVec j) ∈ preSpan (j + 1)) :
    s • baseFlag = baseFlag := by
  refine (smul_baseFlag_eq_iff_pattern s).mpr fun i j hj hji => ?_
  have := hs j hj i (by omega)
  rwa [suLin_apply, mulVec_uVec] at this

theorem smul_baseFlag_eq_iff_sub (h : SU6) :
    h • baseFlag = baseFlag ↔ ∀ k, (h • baseFlag).sub k = baseFlag.sub k :=
  ⟨fun e k => by rw [e], fun H => IsoFlag6.ext (funext H)⟩

theorem weylPerm_lt : ∀ d k : Fin 3, k ≠ d → ∀ j : Fin 6, (j : ℕ) ≤ k →
    ((weylPerm d j : Fin 6) : ℕ) < k + 1 := by
  decide

theorem weylSU_smul_baseFlag_sub {d k : Fin 3} (hk : k ≠ d) :
    (weylSU d • baseFlag).sub k = baseFlag.sub k := by
  refine (smul_baseFlag_sub_eq_iff _ k).mpr fun j hj => ?_
  rw [suLin_apply]
  change ((weylMat d : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ uVec j ∈ _
  rw [weylMat_mulVec_uVec]
  exact uVec_mem_preSpan (weylPerm_lt d k hk j hj)

theorem suLin_bUpSU_weylSU (d : Fin 3) {a : K} (ha : d ≠ 2 ∨ bar a = a) (j : Fin 6) :
    suLin (bUpSU d ha * weylSU d) (uVec j) =
      ((bUp d a : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ
        uVec (weylPerm d j) := by
  rw [suLin_mul_apply, suLin_apply]
  change _ *ᵥ (((weylMat d : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ
    uVec j) = _
  rw [weylMat_mulVec_uVec]
  rfl

theorem bUpSU_weylSU_smul_baseFlag_sub {d k : Fin 3} {a : K} (ha : d ≠ 2 ∨ bar a = a)
    (hk : k ≠ d) : ((bUpSU d ha * weylSU d) • baseFlag).sub k = baseFlag.sub k := by
  rw [mul_smul, smul_sub _ (weylSU d • baseFlag), weylSU_smul_baseFlag_sub hk, ← smul_sub,
    bUpSU_smul_baseFlag]

theorem smul_baseFlag_eq_of_cols' (s : SU6) (h0 : suLin s (uVec 0) ∈ preSpan 1)
    (h1 : suLin s (uVec 1) ∈ preSpan 2) (h2 : suLin s (uVec 2) ∈ preSpan 3) :
    s • baseFlag = baseFlag := by
  refine smul_baseFlag_eq_of_cols s fun j hj => ?_
  fin_cases j
  exacts [h0, h1, h2, absurd hj (by decide), absurd hj (by decide), absurd hj (by decide)]

theorem eq_of_mem_preSpan_two {v : Fin 6 → K} (hv : v ∈ preSpan 2) :
    v = v 0 • uVec 0 + v 1 • uVec 1 := by
  funext i
  fin_cases i
  · simp
  · simp
  all_goals (simp; exact hv _ (by decide))

theorem eq_of_mem_preSpan_three {v : Fin 6 → K} (hv : v ∈ preSpan 3) :
    v = v 0 • uVec 0 + v 1 • uVec 1 + v 2 • uVec 2 := by
  funext i
  fin_cases i
  · simp
  · simp
  · simp
  all_goals (simp; exact hv _ (by decide))

theorem eq_of_mem_preSpan_four {v : Fin 6 → K} (hv : v ∈ preSpan 4) :
    v = v 0 • uVec 0 + v 1 • uVec 1 + v 2 • uVec 2 + v 3 • uVec 3 := by
  funext i
  fin_cases i
  · simp
  · simp
  · simp
  · simp
  all_goals (simp; exact hv _ (by decide))

theorem smul_uVec_mem_preSpan {c : K} {i : Fin 6} {k : ℕ} (hi : (i : ℕ) < k) :
    c • uVec i ∈ preSpan k :=
  Submodule.smul_mem _ c (uVec_mem_preSpan hi)

theorem panel_factor_zero (h : SU6) (hh1 : (h • baseFlag).sub 1 = baseFlag.sub 1)
    (hh2 : (h • baseFlag).sub 2 = baseFlag.sub 2) :
    h • baseFlag = baseFlag ∨ ∃ (a : K) (ha : (0 : Fin 3) ≠ 2 ∨ bar a = a),
      ((bUpSU 0 ha * weylSU 0)⁻¹ * h) • baseFlag = baseFlag := by
  have c1 := (smul_baseFlag_sub_eq_iff h 1).mp hh1
  have c2 := (smul_baseFlag_sub_eq_iff h 2).mp hh2
  have hv2 : suLin h (uVec 0) ∈ preSpan 2 := c1 0 (by decide)
  by_cases hv1 : suLin h (uVec 0) 1 = 0
  · left
    refine smul_baseFlag_eq_of_cols' h (fun j hj => ?_) (c1 1 (by decide)) (c2 2 (by decide))
    rcases Nat.lt_or_ge (j : ℕ) 2 with hj2 | hj2
    · rw [show j = 1 from Fin.ext (by omega)]
      exact hv1
    · exact hv2 j hj2
  · right
    set v := suLin h (uVec 0) with hvdef
    set a := v 0 / v 1 with hadef
    have ha : (0 : Fin 3) ≠ 2 ∨ bar a = a := Or.inl (by decide)
    refine ⟨a, ha, ?_⟩
    set g := bUpSU 0 ha * weylSU 0 with hg
    have hgu : suLin g (uVec 0) = a • uVec 0 + uVec 1 := by
      rw [hg, suLin_bUpSU_weylSU, show weylPerm 0 0 = 1 by decide, bUp_mulVec]
      funext i
      fin_cases i <;> simp
    have hvg : v = v 1 • suLin g (uVec 0) := by
      rw [hgu, smul_add, smul_smul, hadef, mul_div_cancel₀ _ hv1]
      exact eq_of_mem_preSpan_two hv2
    have hk1 : (g • baseFlag).sub 1 = baseFlag.sub 1 :=
      bUpSU_weylSU_smul_baseFlag_sub ha (by decide)
    have hk2 : (g • baseFlag).sub 2 = baseFlag.sub 2 :=
      bUpSU_weylSU_smul_baseFlag_sub ha (by decide)
    refine smul_baseFlag_eq_of_cols' _ ?_ ?_ ?_
    · rw [suLin_mul_apply, ← hvdef, hvg, map_smul, suLin_inv_apply]
      exact smul_uVec_mem_preSpan (by decide)
    · rw [suLin_mul_apply]
      exact suLin_mem_preSpan (k := 1) (inv_smul_baseFlag_sub hk1) (c1 1 (by decide))
    · rw [suLin_mul_apply]
      exact suLin_mem_preSpan (k := 2) (inv_smul_baseFlag_sub hk2) (c2 2 (by decide))

theorem panel_factor_one (h : SU6) (hh0 : (h • baseFlag).sub 0 = baseFlag.sub 0)
    (hh2 : (h • baseFlag).sub 2 = baseFlag.sub 2) :
    h • baseFlag = baseFlag ∨ ∃ (a : K) (ha : (1 : Fin 3) ≠ 2 ∨ bar a = a),
      ((bUpSU 1 ha * weylSU 1)⁻¹ * h) • baseFlag = baseFlag := by
  have c0 := (smul_baseFlag_sub_eq_iff h 0).mp hh0
  have c2 := (smul_baseFlag_sub_eq_iff h 2).mp hh2
  have hv3 : suLin h (uVec 1) ∈ preSpan 3 := c2 1 (by decide)
  by_cases hv2 : suLin h (uVec 1) 2 = 0
  · left
    refine smul_baseFlag_eq_of_cols' h (c0 0 (by decide)) (fun j hj => ?_) (c2 2 (by decide))
    rcases Nat.lt_or_ge (j : ℕ) 3 with hj3 | hj3
    · rw [show j = 2 from Fin.ext (by omega)]
      exact hv2
    · exact hv3 j hj3
  · right
    set v := suLin h (uVec 1) with hvdef
    set a := v 1 / v 2 with hadef
    have ha : (1 : Fin 3) ≠ 2 ∨ bar a = a := Or.inl (by decide)
    refine ⟨a, ha, ?_⟩
    set g := bUpSU 1 ha * weylSU 1 with hg
    have hgu1 : suLin g (uVec 1) = a • uVec 1 + uVec 2 := by
      rw [hg, suLin_bUpSU_weylSU, show weylPerm 1 1 = 2 by decide, bUp_mulVec]
      funext i
      fin_cases i <;> simp
    have hgu0 : suLin g (uVec 0) = uVec 0 := by
      rw [hg, suLin_bUpSU_weylSU, show weylPerm 1 0 = 0 by decide, bUp_mulVec]
      funext i
      fin_cases i <;> simp
    have hvg : v = v 0 • suLin g (uVec 0) + v 2 • suLin g (uVec 1) := by
      rw [hgu0, hgu1, smul_add, smul_smul, hadef, mul_div_cancel₀ _ hv2, ← add_assoc]
      exact eq_of_mem_preSpan_three hv3
    have hk0 : (g • baseFlag).sub 0 = baseFlag.sub 0 :=
      bUpSU_weylSU_smul_baseFlag_sub ha (by decide)
    have hk2 : (g • baseFlag).sub 2 = baseFlag.sub 2 :=
      bUpSU_weylSU_smul_baseFlag_sub ha (by decide)
    refine smul_baseFlag_eq_of_cols' _ ?_ ?_ ?_
    · rw [suLin_mul_apply]
      exact suLin_mem_preSpan (k := 0) (inv_smul_baseFlag_sub hk0) (c0 0 (by decide))
    · rw [suLin_mul_apply, ← hvdef, hvg, map_add, map_smul, map_smul, suLin_inv_apply,
        suLin_inv_apply]
      exact add_mem (smul_uVec_mem_preSpan (by decide)) (smul_uVec_mem_preSpan (by decide))
    · rw [suLin_mul_apply]
      exact suLin_mem_preSpan (k := 2) (inv_smul_baseFlag_sub hk2) (c2 2 (by decide))

theorem apply_eq_bar_inv (h : SU6) (i j : Fin 6) :
    ((h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j =
      bar (suLin h⁻¹ (uVec (Fin.rev i)) (Fin.rev j)) := by
  rw [suLin_apply, mulVec_uVec]
  obtain ⟨g, hg⟩ := h
  have hinv := inv_apply_of_mem_SU6 (inv_mem hg) i j
  rw [inv_inv] at hinv
  exact hinv

theorem form6_uVec_two : form6 (uVec 2) (uVec 2) = 0 := by
  rw [form6_apply, Fin.sum_univ_six]
  simp [bar_zero]

theorem bar_div_eq_of_trace {x y : K} (hy : y ≠ 0) (h : bar x * y + bar y * x = 0) :
    bar (x / y) = x / y := by
  have hy' : bar y ≠ 0 := fun h' => hy (by rw [← bar_bar y, h', bar_zero])
  rw [← barHom_apply, map_div₀, barHom_apply, barHom_apply, div_eq_div_iff hy' hy]
  have e := eq_neg_of_add_eq_zero_left h
  rw [CharTwo.neg_eq] at e
  rw [e, mul_comm]

theorem panel_factor_two (h : SU6) (hh0 : (h • baseFlag).sub 0 = baseFlag.sub 0)
    (hh1 : (h • baseFlag).sub 1 = baseFlag.sub 1) :
    h • baseFlag = baseFlag ∨ ∃ (a : K) (ha : (2 : Fin 3) ≠ 2 ∨ bar a = a),
      ((bUpSU 2 ha * weylSU 2)⁻¹ * h) • baseFlag = baseFlag := by
  have c0 := (smul_baseFlag_sub_eq_iff h 0).mp hh0
  have c1 := (smul_baseFlag_sub_eq_iff h 1).mp hh1
  have d0 := (smul_baseFlag_sub_eq_iff h⁻¹ 0).mp (inv_smul_baseFlag_sub hh0)
  have d1 := (smul_baseFlag_sub_eq_iff h⁻¹ 1).mp (inv_smul_baseFlag_sub hh1)
  set v := suLin h (uVec 2) with hvdef
  have hvi : ∀ i, v i = ((h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i 2 :=
    fun i => by rw [hvdef, suLin_apply, mulVec_uVec]
  have hv4 : v 4 = 0 := by
    rw [hvi, apply_eq_bar_inv, show Fin.rev (4 : Fin 6) = 1 by decide,
      show Fin.rev (2 : Fin 6) = 3 by decide, d1 1 (by decide) 3 (by decide), bar_zero]
  have hv5 : v 5 = 0 := by
    rw [hvi, apply_eq_bar_inv, show Fin.rev (5 : Fin 6) = 0 by decide,
      show Fin.rev (2 : Fin 6) = 3 by decide, d0 0 (by decide) 3 (by decide), bar_zero]
  have hv4' : v ∈ preSpan 4 := fun j hj => by
    rcases Nat.lt_or_ge (j : ℕ) 5 with hj5 | hj5
    · rw [show j = 4 from Fin.ext (by omega)]
      exact hv4
    · rw [show j = 5 from Fin.ext (by omega)]
      exact hv5
  have hiso : bar (v 2) * v 3 + bar (v 3) * v 2 = 0 := by
    have e := form6_mulVec_of_mem_SU6 h.2 (uVec 2) (uVec 2)
    rw [form6_uVec_two, ← suLin_apply, ← hvdef, form6_apply, Fin.sum_univ_six] at e
    simp only [show Fin.rev (0 : Fin 6) = 5 by decide, show Fin.rev (1 : Fin 6) = 4 by decide,
      show Fin.rev (2 : Fin 6) = 3 by decide, show Fin.rev (3 : Fin 6) = 2 by decide,
      show Fin.rev (4 : Fin 6) = 1 by decide, show Fin.rev (5 : Fin 6) = 0 by decide, hv4, hv5,
      bar_zero, mul_zero, zero_mul, zero_add, add_zero] at e
    exact e
  by_cases hv3 : v 3 = 0
  · left
    refine smul_baseFlag_eq_of_cols' h (c0 0 (by decide)) (c1 1 (by decide)) (fun j hj => ?_)
    rcases Nat.lt_or_ge (j : ℕ) 4 with hj4 | hj4
    · rw [show j = 3 from Fin.ext (by omega)]
      exact hv3
    · exact hv4' j hj4
  · right
    set a := v 2 / v 3 with hadef
    have ha : (2 : Fin 3) ≠ 2 ∨ bar a = a := Or.inr (bar_div_eq_of_trace hv3 hiso)
    refine ⟨a, ha, ?_⟩
    set g := bUpSU 2 ha * weylSU 2 with hg
    have hgu2 : suLin g (uVec 2) = a • uVec 2 + uVec 3 := by
      rw [hg, suLin_bUpSU_weylSU, show weylPerm 2 2 = 3 by decide, bUp_mulVec]
      funext i
      fin_cases i <;> simp
    have hgu0 : suLin g (uVec 0) = uVec 0 := by
      rw [hg, suLin_bUpSU_weylSU, show weylPerm 2 0 = 0 by decide, bUp_mulVec]
      funext i
      fin_cases i <;> simp
    have hgu1 : suLin g (uVec 1) = uVec 1 := by
      rw [hg, suLin_bUpSU_weylSU, show weylPerm 2 1 = 1 by decide, bUp_mulVec]
      funext i
      fin_cases i <;> simp
    have hvg : v = v 0 • suLin g (uVec 0) + v 1 • suLin g (uVec 1) + v 3 • suLin g (uVec 2) := by
      rw [hgu0, hgu1, hgu2, smul_add, smul_smul, hadef, mul_div_cancel₀ _ hv3, ← add_assoc]
      exact eq_of_mem_preSpan_four hv4'
    have hk0 : (g • baseFlag).sub 0 = baseFlag.sub 0 :=
      bUpSU_weylSU_smul_baseFlag_sub ha (by decide)
    have hk1 : (g • baseFlag).sub 1 = baseFlag.sub 1 :=
      bUpSU_weylSU_smul_baseFlag_sub ha (by decide)
    refine smul_baseFlag_eq_of_cols' _ ?_ ?_ ?_
    · rw [suLin_mul_apply]
      exact suLin_mem_preSpan (k := 0) (inv_smul_baseFlag_sub hk0) (c0 0 (by decide))
    · rw [suLin_mul_apply]
      exact suLin_mem_preSpan (k := 1) (inv_smul_baseFlag_sub hk1) (c1 1 (by decide))
    · rw [suLin_mul_apply, ← hvdef, hvg, map_add, map_add, map_smul, map_smul, map_smul,
        suLin_inv_apply, suLin_inv_apply, suLin_inv_apply]
      exact add_mem (add_mem (smul_uVec_mem_preSpan (by decide))
        (smul_uVec_mem_preSpan (by decide))) (smul_uVec_mem_preSpan (by decide))

theorem panel_factor (d : Fin 3) (h : SU6)
    (hh : ∀ k, k ≠ d → (h • baseFlag).sub k = baseFlag.sub k) :
    h • baseFlag = baseFlag ∨ ∃ (a : K) (ha : d ≠ 2 ∨ bar a = a),
      ((bUpSU d ha * weylSU d)⁻¹ * h) • baseFlag = baseFlag := by
  fin_cases d
  · exact panel_factor_zero h (hh 1 (by decide)) (hh 2 (by decide))
  · exact panel_factor_one h (hh 0 (by decide)) (hh 2 (by decide))
  · exact panel_factor_two h (hh 0 (by decide)) (hh 1 (by decide))

@[expose] def bLow (d : Fin 3) : SpecialLinearGroup (Fin 6) K :=
  ![downAdj 0 1 * downAdj 4 1, downAdj 1 1 * downAdj 3 1, downAdj 2 1] d

theorem bLow_mem_SU6 (d : Fin 3) : bLow d ∈ SU6 := by
  apply mem_SU6_of_tauSL
  fin_cases d
  · change tauSL (downAdj 0 1 * downAdj 4 1) = downAdj 0 1 * downAdj 4 1
    rw [map_mul, tauSL_downAdj, tauSL_downAdj, bar_one]
    exact Subtype.ext (transvection_comm (by decide) (by decide) _ _)
  · change tauSL (downAdj 1 1 * downAdj 3 1) = downAdj 1 1 * downAdj 3 1
    rw [map_mul, tauSL_downAdj, tauSL_downAdj, bar_one]
    exact Subtype.ext (transvection_comm (by decide) (by decide) _ _)
  · change tauSL (downAdj 2 1) = downAdj 2 1
    rw [tauSL_downAdj, bar_one]

@[expose] def bLowSU (d : Fin 3) : SU6 := ⟨bLow d, bLow_mem_SU6 d⟩

theorem bLow_mulVec (d : Fin 3) (w : Fin 6 → K) :
    ((bLow d : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w =
      ![w + w 4 • uVec 5 + w 0 • uVec 1, w + w 3 • uVec 4 + w 1 • uVec 2,
        w + w 2 • uVec 3] d := by
  fin_cases d
  · change ((downAdj 0 1 : Matrix (Fin 6) (Fin 6) K) * (downAdj 4 1 : Matrix (Fin 6) (Fin 6) K))
      *ᵥ w = _
    rw [← mulVec_mulVec]
    change transvection 1 0 1 *ᵥ (transvection 5 4 1 *ᵥ w) = _
    rw [transvection_mulVec, transvection_mulVec]
    simp
  · change ((downAdj 1 1 : Matrix (Fin 6) (Fin 6) K) * (downAdj 3 1 : Matrix (Fin 6) (Fin 6) K))
      *ᵥ w = _
    rw [← mulVec_mulVec]
    change transvection 2 1 1 *ᵥ (transvection 4 3 1 *ᵥ w) = _
    rw [transvection_mulVec, transvection_mulVec]
    simp
  · change transvection 3 2 1 *ᵥ w = _
    rw [transvection_mulVec, one_mul]
    rfl

theorem bLow_mulVec_uVec_zero :
    ((bLow 0 : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ uVec 0 =
      uVec 0 + uVec 1 := by
  rw [bLow_mulVec]
  funext i
  fin_cases i <;> simp

theorem bLow_mulVec_uVec_one :
    ((bLow 1 : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ uVec 1 =
      uVec 1 + uVec 2 := by
  rw [bLow_mulVec]
  funext i
  fin_cases i <;> simp

theorem bLow_mulVec_uVec_two :
    ((bLow 2 : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ uVec 2 =
      uVec 2 + uVec 3 := by
  rw [bLow_mulVec]
  funext i
  fin_cases i <;> simp

theorem suLin_bLowSU_zero : suLin (bLowSU 0) (uVec 0) = uVec 0 + uVec 1 :=
  bLow_mulVec_uVec_zero

theorem suLin_bLowSU_one : suLin (bLowSU 1) (uVec 1) = uVec 1 + uVec 2 :=
  bLow_mulVec_uVec_one

theorem suLin_bLowSU_two : suLin (bLowSU 2) (uVec 2) = uVec 2 + uVec 3 :=
  bLow_mulVec_uVec_two

theorem apply_eq_of_mem_bLow_zero {v : Fin 6 → K} (hv : v ∈ ((bLowSU 0) • baseFlag).sub 0) :
    v 1 = v 0 := by
  obtain ⟨w, hw, rfl⟩ := hv
  rw [baseFlag_sub] at hw
  change (((bLow 0 : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w) 1 =
    (((bLow 0 : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w) 0
  rw [bLow_mulVec]
  have h1 : w 1 = 0 := hw 1 (by decide)
  have h4 : w 4 = 0 := hw 4 (by decide)
  simp [h1, h4]

theorem apply_eq_of_mem_bLow_one {v : Fin 6 → K} (hv : v ∈ ((bLowSU 1) • baseFlag).sub 1) :
    v 2 = v 1 := by
  obtain ⟨w, hw, rfl⟩ := hv
  rw [baseFlag_sub] at hw
  change (((bLow 1 : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w) 2 =
    (((bLow 1 : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w) 1
  rw [bLow_mulVec]
  have h2 : w 2 = 0 := hw 2 (by decide)
  have h3 : w 3 = 0 := hw 3 (by decide)
  simp [h2, h3]

theorem apply_eq_of_mem_bLow_two {v : Fin 6 → K} (hv : v ∈ ((bLowSU 2) • baseFlag).sub 2) :
    v 3 = v 2 := by
  obtain ⟨w, hw, rfl⟩ := hv
  rw [baseFlag_sub] at hw
  change (((bLow 2 : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w) 3 =
    (((bLow 2 : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w) 2
  rw [bLow_mulVec]
  have h3 : w 3 = 0 := hw 3 (by decide)
  simp [h3]

theorem suLin_revSU_apply (v : Fin 6 → K) (i : Fin 6) : suLin revSU v i = v (Fin.rev i) := by
  rw [suLin_apply]
  exact J6_mulVec v i

theorem revSU_inv : revSU⁻¹ = revSU :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (Subtype.ext J6_mul_J6))

theorem eq_of_bar_mul {c x : K} (hc : bar c * c = 1) (hx : bar c * x = 1) : x = c := by
  have hb : bar c ≠ 0 := fun h => by rw [h, zero_mul] at hc; exact zero_ne_one hc
  exact mul_left_cancel₀ hb (hx.trans hc.symm)

theorem mem_smul_sub_of_forall {h g : SU6} (hh : h • (g • baseFlag) = g • baseFlag) (k : Fin 3)
    {w : Fin 6 → K} (hw : w ∈ preSpan (k + 1)) : suLin h (suLin g w) ∈ (g • baseFlag).sub k := by
  have h1 : suLin g w ∈ (g • baseFlag).sub k := Submodule.mem_map_of_mem hw
  have h2 := Submodule.mem_map_of_mem (f := (suLin h : (Fin 6 → K) →ₗ[K] (Fin 6 → K))) h1
  rwa [← smul_sub, hh] at h2

theorem mem_scalars_of_forall_smul_eq (h : SU6) (hh : ∀ F : IsoFlag6, h • F = F) :
    (h : SpecialLinearGroup (Fin 6) K) ∈ LinearFlag.scalars 6 K := by
  have hup := (smul_baseFlag_eq_iff h).mp (hh baseFlag)
  have hlow : ∀ i j : Fin 6, i < j →
      ((h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0 := by
    have e : (revSU⁻¹ * h * revSU) • baseFlag = baseFlag := by
      rw [mul_smul, mul_smul, hh, ← mul_smul, inv_mul_cancel, one_smul]
    have H := (smul_baseFlag_eq_iff _).mp e
    intro i j hij
    have := H (Fin.rev i) (Fin.rev j) (Fin.rev_lt_rev.mpr hij)
    have e2 : (((revSU⁻¹ * h * revSU : SU6) : SpecialLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) (Fin.rev i) (Fin.rev j) =
          suLin revSU⁻¹ (suLin h (suLin revSU (uVec (Fin.rev j)))) (Fin.rev i) := by
      rw [← suLin_mul_apply, ← suLin_mul_apply, suLin_apply, mulVec_uVec]
    rw [e2, revSU_inv, suLin_revSU_apply, Fin.rev_rev, suLin_revSU_uVec, Fin.rev_rev,
      suLin_apply, mulVec_uVec] at this
    exact this
  have hv : ∀ v : Fin 6 → K, suLin h v =
      fun i => ((h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i * v i := by
    intro v
    funext i
    rw [suLin_apply, mulVec, dotProduct, Finset.sum_eq_single i (fun j _ hj => by
      rw [(lt_or_gt_of_ne hj).elim (fun hlt => hup i j hlt) (fun hgt => hlow i j hgt),
        zero_mul]) (fun h => absurd (Finset.mem_univ _) h)]
  obtain ⟨g, hg⟩ := h
  set M := (g : Matrix (Fin 6) (Fin 6) K) with hM
  have hdiag : ∀ i j, i ≠ j → M i j = 0 := fun i j hij =>
    (lt_or_gt_of_ne hij).elim (hlow i j) (hup i j)
  have e1 : M 1 1 = M 0 0 := by
    have hm := mem_smul_sub_of_forall (g := bLowSU 0) (hh _) 0
      (uVec_mem_preSpan (i := 0) (by decide))
    have e := apply_eq_of_mem_bLow_zero hm
    rw [suLin_bLowSU_zero, hv] at e
    simpa using e
  have e2 : M 2 2 = M 1 1 := by
    have hm := mem_smul_sub_of_forall (g := bLowSU 1) (hh _) 1
      (uVec_mem_preSpan (i := 1) (by decide))
    have e := apply_eq_of_mem_bLow_one hm
    rw [suLin_bLowSU_one, hv] at e
    simpa using e
  have e3 : M 3 3 = M 2 2 := by
    have hm := mem_smul_sub_of_forall (g := bLowSU 2) (hh _) 2
      (uVec_mem_preSpan (i := 2) (by decide))
    have e := apply_eq_of_mem_bLow_two hm
    rw [suLin_bLowSU_two, hv] at e
    simpa using e
  have hunit : ∀ i : Fin 6, bar (M i i) * M (Fin.rev i) (Fin.rev i) = 1 := by
    intro i
    have e := congrFun (congrFun ((mem_SU6_iff g).mp hg) i) (Fin.rev i)
    change ((M.map bar)ᵀ * J6 * M) i (Fin.rev i) = J6 i (Fin.rev i) at e
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i), mul_J6_apply, transpose_apply,
      map_apply, Fin.rev_rev, J6_apply, ite_eq_left rfl] at e
    · exact e
    · intro j _ hj
      rw [hdiag j (Fin.rev i) hj, mul_zero]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  have hc : bar (M 0 0) * M 0 0 = 1 := by
    have := hunit 2
    rwa [show Fin.rev (2 : Fin 6) = 3 by decide, e3, e2, e1] at this
  have e4 : M 4 4 = M 0 0 := eq_of_bar_mul hc (by
    have := hunit 1
    rwa [show Fin.rev (1 : Fin 6) = 4 by decide, e1] at this)
  have e5 : M 5 5 = M 0 0 := eq_of_bar_mul hc (by
    have := hunit 0
    rwa [show Fin.rev (0 : Fin 6) = 5 by decide] at this)
  have hc0 : M 0 0 ≠ 0 := fun h' => by rw [h', mul_zero] at hc; exact zero_ne_one hc
  refine LinearFlag.mem_scalars.mpr ⟨Units.mk0 _ hc0, ?_, ?_⟩
  · calc Units.mk0 (M 0 0) hc0 ^ 6 = (Units.mk0 (M 0 0) hc0 ^ 3) ^ 2 := pow_mul _ 3 2
      _ = 1 := by rw [units_pow_three, one_pow]
  · ext i j
    rw [Units.val_mk0, scalar_apply, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      fin_cases i
      exacts [rfl, e1, e2.trans e1, e3.trans (e2.trans e1), e4, e5]
    · rw [ite_eq_right hij]
      exact hdiag i j hij

end CFSG.LieType.Chevalley.C2E6Std
