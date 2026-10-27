module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix

variable {F : Type*} [Field F]

theorem single_one_mul_apply_five (a b i j : Fin 5) (M : Matrix (Fin 5) (Fin 5) F) :
    (single a b (1 : F) * M) i j = if i = a then M b j else 0 := by
  split_ifs with h
  · subst h
    rw [single_mul_apply_same, one_mul]
  · exact single_mul_apply_of_ne _ _ _ _ _ h M

theorem mul_single_one_apply_five (a b i j : Fin 5) (M : Matrix (Fin 5) (Fin 5) F) :
    (M * single a b (1 : F)) i j = if j = b then M i a else 0 := by
  split_ifs with h
  · subst h
    rw [mul_single_apply_same, mul_one]
  · exact mul_single_apply_of_ne _ _ _ _ _ h M

abbrev brkFive (a b : Fin 5) (M : Matrix (Fin 5) (Fin 5) F) : Matrix (Fin 5) (Fin 5) F :=
  single a b (1 : F) * M - M * single a b 1

theorem linearIndependent_of_triangular {n : ℕ} (v : Fin n → Matrix (Fin 5) (Fin 5) F)
    (p q : Fin n → Fin 5) (hdiag : ∀ k, v k (p k) (q k) ≠ 0)
    (htri : ∀ k l, l < k → v k (p l) (q l) = 0) : LinearIndependent F v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hev : ∀ l, ∑ k, g k * v k (p l) (q l) = 0 := fun l => by
    have h := congrFun (congrFun hg (p l)) (q l)
    simpa [Matrix.sum_apply] using h
  suffices h : ∀ m : ℕ, ∀ i : Fin n, (i : ℕ) = m → g i = 0 from fun i => h i i rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i hi
    have h1 := hev i
    rw [Finset.sum_eq_single i] at h1
    · exact (mul_eq_zero.1 h1).resolve_right (hdiag i)
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hk | hk
      · rw [ih k (hi ▸ hk) k rfl, zero_mul]
      · rw [htri k i hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem le_finrank_of_triangular {n : ℕ} {J : Submodule F (Matrix (Fin 5) (Fin 5) F)}
    (v : Fin n → Matrix (Fin 5) (Fin 5) F) (hv : ∀ k, v k ∈ J)
    (p q : Fin n → Fin 5) (hdiag : ∀ k, v k (p k) (q k) ≠ 0)
    (htri : ∀ k l, l < k → v k (p l) (q l) = 0) : n ≤ Module.finrank F J := by
  have h := finrank_span_eq_card (linearIndependent_of_triangular v p q hdiag htri)
  rw [Fintype.card_fin] at h
  rw [← h]
  exact Submodule.finrank_mono (Submodule.span_le.2 (Set.range_subset_iff.2 hv))

theorem single_one_mul_comm_of {a b : Fin 5} {M : Matrix (Fin 5) (Fin 5) F}
    (hrow : ∀ j, M b j = 0) (hcol : ∀ i, M i a = 0) :
    single a b (1 : F) * M = M * single a b 1 := by
  ext i j
  rw [single_one_mul_apply_five, mul_single_one_apply_five, hrow, hcol]
  simp

@[expose] def uFiveTwistedSpace (e : F) : Submodule F (Matrix (Fin 5) (Fin 5) F) where
  carrier := {N | IsStrictUpperFive N ∧ N 1 2 = 0 ∧ N 1 3 = 0 ∧ N 2 3 = 0 ∧ N 3 4 = 0 ∧
    N 1 4 = -e * N 0 2 ∧ N 2 4 = e * N 0 1}
  add_mem' := by
    rintro N N' ⟨h0, h1, h2, h3, h4, h5, h6⟩ ⟨h0', h1', h2', h3', h4', h5', h6'⟩
    refine ⟨h0.add h0', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Matrix.add_apply, h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6'] <;> ring
  zero_mem' := ⟨fun _ _ _ => rfl, by simp⟩
  smul_mem' := by
    rintro a N ⟨h0, h1, h2, h3, h4, h5, h6⟩
    refine ⟨h0.smul a, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Matrix.smul_apply, smul_eq_mul, h1, h2, h3, h4, h5, h6] <;> ring

theorem mem_uFiveTwistedSpace {e : F} {N : Matrix (Fin 5) (Fin 5) F} :
    N ∈ uFiveTwistedSpace e ↔ IsStrictUpperFive N ∧ N 1 2 = 0 ∧ N 1 3 = 0 ∧ N 2 3 = 0 ∧
      N 3 4 = 0 ∧ N 1 4 = -e * N 0 2 ∧ N 2 4 = e * N 0 1 := Iff.rfl

theorem finrank_uFiveTwistedSpace_le (e : F) : Module.finrank F (uFiveTwistedSpace e) ≤ 4 := by
  let f : uFiveTwistedSpace e →ₗ[F] (Fin 4 → F) :=
    { toFun := fun N => ![(N : Matrix (Fin 5) (Fin 5) F) 0 1, (N : Matrix (Fin 5) (Fin 5) F) 0 2,
        (N : Matrix (Fin 5) (Fin 5) F) 0 3, (N : Matrix (Fin 5) (Fin 5) F) 0 4]
      map_add' := fun N N' => by ext k; fin_cases k <;> rfl
      map_smul' := fun a N => by ext k; fin_cases k <;> rfl }
  have hf : Function.Injective f := by
    rintro ⟨N, h0, h1, h2, h3, h4, h5, h6⟩ ⟨N', h0', h1', h2', h3', h4', h5', h6'⟩ h
    have e1 := congrFun h 0
    have e2 := congrFun h 1
    have e3 := congrFun h 2
    have e4 := congrFun h 3
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] at e1 e2 e3 e4
    apply Subtype.ext
    change N = N'
    rw [h0.eq, h0'.eq, h1, h2, h3, h4, h5, h6, h1', h2', h3', h4', h5', h6', e1, e2, e3, e4]
  have h := LinearMap.finrank_le_finrank_of_injective hf
  simpa using h

structure IsUFiveRadicalSpace (J : Submodule F (Matrix (Fin 5) (Fin 5) F)) : Prop where
  strictUpper : ∀ M ∈ J, IsStrictUpperFive M
  comm : ∀ M ∈ J, ∀ M' ∈ J, M * M' = M' * M
  sq : ∀ M ∈ J, M * M = 0
  brk01 : ∀ M ∈ J, brkFive 0 1 M ∈ J
  brk12 : ∀ M ∈ J, brkFive 1 2 M ∈ J
  brk23 : ∀ M ∈ J, brkFive 2 3 M ∈ J
  brk34 : ∀ M ∈ J, brkFive 3 4 M ∈ J
  cent : ∀ N, IsStrictUpperFive N → (∀ M ∈ J, N * M = M * N) → N ∈ J
  finrank_eq : Module.finrank F J = 4

namespace IsUFiveRadicalSpace

variable {J : Submodule F (Matrix (Fin 5) (Fin 5) F)} (hJ : IsUFiveRadicalSpace J)
include hJ

theorem single04_mem : single 0 4 (1 : F) ∈ J :=
  hJ.cent _ (isStrictUpperFive_single (by decide) 1) fun M hM =>
    single_one_mul_comm_of (fun j => hJ.strictUpper M hM 4 j (Fin.le_last j))
      (fun i => hJ.strictUpper M hM i 0 (Fin.zero_le i))

theorem apply12_eq_zero : ∀ M ∈ J, M 1 2 = 0 := by
  intro M hM
  by_contra h12
  have hK := hJ.brk23 M hM
  have h := le_finrank_of_triangular (J := J)
    ![M, brkFive 2 3 M, brkFive 0 1 (brkFive 2 3 M), brkFive 3 4 (brkFive 2 3 M), single 0 4 1]
    (fun k => by
      fin_cases k
      exacts [hM, hK, hJ.brk01 _ hK, hJ.brk34 _ hK, hJ.single04_mem])
    ![1, 1, 0, 1, 0] ![2, 3, 3, 4, 4]
    (fun k => by fin_cases k <;> simp [h12])
    (fun k l hlk => by fin_cases k <;> fin_cases l <;> simp at hlk ⊢)
  rw [hJ.finrank_eq] at h
  omega

theorem apply23_eq_zero : ∀ M ∈ J, M 2 3 = 0 := by
  intro M hM
  by_contra h23
  have hK := hJ.brk12 M hM
  have h := le_finrank_of_triangular (J := J)
    ![M, brkFive 1 2 M, brkFive 3 4 (brkFive 1 2 M), brkFive 0 1 (brkFive 1 2 M), single 0 4 1]
    (fun k => by
      fin_cases k
      exacts [hM, hK, hJ.brk34 _ hK, hJ.brk01 _ hK, hJ.single04_mem])
    ![2, 1, 1, 0, 0] ![3, 3, 4, 3, 4]
    (fun k => by fin_cases k <;> simp [h23])
    (fun k l hlk => by fin_cases k <;> fin_cases l <;> simp at hlk ⊢)
  rw [hJ.finrank_eq] at h
  omega

theorem apply01_eq_zero_or_apply34_eq_zero : ∀ M ∈ J, M 0 1 = 0 ∨ M 3 4 = 0 := by
  intro M hM
  by_contra h
  push Not at h
  obtain ⟨h01, h34⟩ := h
  have hK := hJ.brk12 M hM
  have h := le_finrank_of_triangular (J := J)
    ![M, brkFive 1 2 M, brkFive 2 3 M, brkFive 2 3 (brkFive 1 2 M), single 0 4 1]
    (fun k => by
      fin_cases k
      exacts [hM, hK, hJ.brk23 _ hM, hJ.brk23 _ hK, hJ.single04_mem])
    ![0, 0, 2, 0, 0] ![1, 2, 4, 3, 4]
    (fun k => by fin_cases k <;> simp [h01, h34])
    (fun k l hlk => by fin_cases k <;> fin_cases l <;> simp at hlk ⊢)
  rw [hJ.finrank_eq] at h
  omega

theorem apply34_or_apply01 : (∀ M ∈ J, M 3 4 = 0) ∨ ∀ M ∈ J, M 0 1 = 0 := by
  by_contra h
  push Not at h
  obtain ⟨⟨M, hM, h34⟩, ⟨M', hM', h01⟩⟩ := h
  have hM01 := (hJ.apply01_eq_zero_or_apply34_eq_zero M hM).resolve_right h34
  have hM'34 := (hJ.apply01_eq_zero_or_apply34_eq_zero M' hM').resolve_left h01
  rcases hJ.apply01_eq_zero_or_apply34_eq_zero (M + M') (J.add_mem hM hM') with h | h
  · rw [Matrix.add_apply, hM01, zero_add] at h
    exact h01 h
  · rw [Matrix.add_apply, hM'34, add_zero] at h
    exact h34 h

theorem exists_apply01_ne_zero_or_apply34_ne_zero : ∃ M ∈ J, M 0 1 ≠ 0 ∨ M 3 4 ≠ 0 := by
  by_contra h
  push Not at h
  have hs := hJ.strictUpper
  have hrow3 : ∀ M ∈ J, ∀ j, M 3 j = 0 := fun M hM j => by
    fin_cases j
    exacts [hs M hM _ _ (by decide), hs M hM _ _ (by decide), hs M hM _ _ (by decide),
      hs M hM _ _ (by decide), (h M hM).2]
  have hcol1 : ∀ M ∈ J, ∀ i, M i 1 = 0 := fun M hM i => by
    fin_cases i
    exacts [(h M hM).1, hs M hM _ _ (by decide), hs M hM _ _ (by decide),
      hs M hM _ _ (by decide), hs M hM _ _ (by decide)]
  have h03 : single 0 3 (1 : F) ∈ J :=
    hJ.cent _ (isStrictUpperFive_single (by decide) 1) fun M hM =>
      single_one_mul_comm_of (hrow3 M hM) (fun i => hs M hM i 0 (Fin.zero_le i))
  have h13 : single 1 3 (1 : F) ∈ J :=
    hJ.cent _ (isStrictUpperFive_single (by decide) 1) fun M hM =>
      single_one_mul_comm_of (hrow3 M hM) (hcol1 M hM)
  have h14 : single 1 4 (1 : F) ∈ J :=
    hJ.cent _ (isStrictUpperFive_single (by decide) 1) fun M hM =>
      single_one_mul_comm_of (fun j => hs M hM 4 j (Fin.le_last j)) (hcol1 M hM)
  by_cases h24 : ∀ M ∈ J, M 2 4 = 0
  · have h02 : single 0 2 (1 : F) ∈ J :=
      hJ.cent _ (isStrictUpperFive_single (by decide) 1) fun M hM =>
        single_one_mul_comm_of (fun j => by
          fin_cases j
          exacts [hs M hM _ _ (by decide), hs M hM _ _ (by decide), hs M hM _ _ (by decide),
            hJ.apply23_eq_zero M hM, h24 M hM])
          (fun i => hs M hM i 0 (Fin.zero_le i))
    have h := le_finrank_of_triangular (J := J)
      ![single 0 2 1, single 0 3 1, single 0 4 1, single 1 3 1, single 1 4 1]
      (fun k => by
        fin_cases k
        exacts [h02, h03, hJ.single04_mem, h13, h14])
      ![0, 0, 0, 1, 1] ![2, 3, 4, 3, 4]
      (fun k => by fin_cases k <;> simp)
      (fun k l hlk => by fin_cases k <;> fin_cases l <;> simp at hlk ⊢)
    rw [hJ.finrank_eq] at h
    omega
  · push Not at h24
    obtain ⟨M, hM, hM24⟩ := h24
    have h := le_finrank_of_triangular (J := J)
      ![M, single 0 3 1, single 0 4 1, single 1 3 1, single 1 4 1]
      (fun k => by
        fin_cases k
        exacts [hM, h03, hJ.single04_mem, h13, h14])
      ![2, 0, 0, 1, 1] ![4, 3, 4, 3, 4]
      (fun k => by fin_cases k <;> simp [hM24])
      (fun k l hlk => by fin_cases k <;> fin_cases l <;> simp at hlk ⊢)
    rw [hJ.finrank_eq] at h
    omega

theorem exists_eq_twistedSpace (h34 : ∀ M ∈ J, M 3 4 = 0) :
    ∃ e : F, J = uFiveTwistedSpace e := by
  have hs := hJ.strictUpper
  obtain ⟨M₀, hM₀, hne⟩ := hJ.exists_apply01_ne_zero_or_apply34_ne_zero
  have h01₀ : M₀ 0 1 ≠ 0 := hne.resolve_right (not_not.2 (h34 M₀ hM₀))
  obtain ⟨M, hM, hMdef⟩ : ∃ M ∈ J, M = (M₀ 0 1)⁻¹ • M₀ := ⟨_, J.smul_mem _ hM₀, rfl⟩
  have hMs := hs M hM
  have h01 : M 0 1 = 1 := by
    rw [hMdef, Matrix.smul_apply, smul_eq_mul, inv_mul_cancel₀ h01₀]
  have h12 := hJ.apply12_eq_zero M hM
  have h23 := hJ.apply23_eq_zero M hM
  have h34M := h34 M hM
  have h04 := hJ.single04_mem
  have h03 : single 0 3 (1 : F) ∈ J :=
    hJ.cent _ (isStrictUpperFive_single (by decide) 1) fun M' hM' =>
      single_one_mul_comm_of (fun j => by
        fin_cases j
        exacts [hs M' hM' _ _ (by decide), hs M' hM' _ _ (by decide), hs M' hM' _ _ (by decide),
          hs M' hM' _ _ (by decide), h34 M' hM'])
        (fun i => hs M' hM' i 0 (Fin.zero_le i))
  have hV : brkFive 3 4 M + M 0 3 • single 0 4 (1 : F) ∈ J :=
    J.add_mem (hJ.brk34 M hM) (J.smul_mem _ h04)
  have h13 : M 1 3 = 0 := by
    have hc := congrFun (congrFun (hJ.comm M hM _ hV) 0) 4
    rw [hMs.eq] at hc
    simp [Matrix.mul_apply, Fin.sum_univ_five, h01, h23] at hc
    exact hc
  have hsq : M 1 4 = -(M 0 2 * M 2 4) := by
    have hc := congrFun (congrFun (hJ.sq M hM) 0) 4
    rw [hMs.eq] at hc
    simp [Matrix.mul_apply, Fin.sum_univ_five, h01, h34M] at hc
    linear_combination hc
  have hP := hJ.brk12 M hM
  have hQ : M + M 0 2 • brkFive 1 2 M - M 0 3 • single 0 3 (1 : F) - M 0 4 • single 0 4 1 ∈ J :=
    J.sub_mem (J.sub_mem (J.add_mem hM (J.smul_mem _ hP)) (J.smul_mem _ h03)) (J.smul_mem _ h04)
  refine ⟨M 2 4, ?_⟩
  have hvJ : ∀ k, ![M + M 0 2 • brkFive 1 2 M - M 0 3 • single 0 3 (1 : F) - M 0 4 • single 0 4 1,
      -brkFive 1 2 M, single 0 3 1, single 0 4 1] k ∈ J := fun k => by
    fin_cases k
    exacts [hQ, J.neg_mem hP, h03, h04]
  have hvT : ∀ k, ![M + M 0 2 • brkFive 1 2 M - M 0 3 • single 0 3 (1 : F) - M 0 4 • single 0 4 1,
      -brkFive 1 2 M, single 0 3 1, single 0 4 1] k ∈ uFiveTwistedSpace (M 2 4) := fun k => by
    refine ⟨hs _ (hvJ k), ?_⟩
    fin_cases k <;> simp [h01, h12, h13, h23, h34M, hsq, hMs 1 1 le_rfl, hMs 2 2 le_rfl]
  have h := le_finrank_of_triangular (J := J ⊓ uFiveTwistedSpace (M 2 4)) _
    (fun k => ⟨hvJ k, hvT k⟩) ![0, 0, 0, 0] ![1, 2, 3, 4]
    (fun k => by fin_cases k <;> simp [h01])
    (fun k l hlk => by fin_cases k <;> fin_cases l <;> simp at hlk ⊢)
  have hle : J ≤ uFiveTwistedSpace (M 2 4) := by
    rw [← Submodule.eq_of_le_of_finrank_le inf_le_left (hJ.finrank_eq.trans_le h)]
    exact inf_le_right
  exact Submodule.eq_of_le_of_finrank_le hle
    (by rw [hJ.finrank_eq]; exact finrank_uFiveTwistedSpace_le _)

end IsUFiveRadicalSpace

end CFSG.SeitzReduction.LinearPilot
