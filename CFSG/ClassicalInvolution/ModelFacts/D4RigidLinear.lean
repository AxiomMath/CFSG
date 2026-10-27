module

public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.ClassicalInvolution.ModelFacts.D4Rigid

open CFSG.LieType.Universal.Spin QuadraticMap

abbrev Idx := Fin 4 ⊕ Fin 4

variable {F : Type} [Field F]

@[expose] def tvm (p q p' q' : Idx) (v : Idx → F) : Idx → F := fun μ =>
  v μ + v p * (if μ = q then 1 else 0) - v p' * (if μ = q' then 1 else 0)

@[expose] def dg (lam : Idx → F) (v : Idx → F) : Idx → F := fun μ => lam μ * v μ

@[expose] def lamA (c : F) (μ : Idx) : F :=
  if μ = Sum.inl 0 then c ^ 2 else if μ = Sum.inr 0 then (c ^ 2)⁻¹ else 1

@[expose] def lamB (c : F) (μ : Idx) : F :=
  if μ = Sum.inl 3 then (c ^ 2)⁻¹ else if μ = Sum.inr 3 then c ^ 2 else 1

@[expose] def xrm (b : F) (v : Idx → F) : Idx → F := fun μ =>
  v μ + b * v (Sum.inl 2) * (if μ = Sum.inl 1 then 1 else 0) -
    b * v (Sum.inr 1) * (if μ = Sum.inr 2 then 1 else 0)

theorem tvm_apply (p q p' q' : Idx) (v : Idx → F) (μ : Idx) :
    tvm p q p' q' v μ = v μ + v p * (if μ = q then 1 else 0) - v p' * (if μ = q' then 1 else 0) :=
  rfl

theorem tvm_eq (p q p' q' : Idx) (v : Idx → F) :
    tvm p q p' q' v = v + v p • (Pi.single q 1 : Idx → F) - v p' • (Pi.single q' 1 : Idx → F) := by
  funext μ
  simp [tvm, Pi.single_apply]

theorem kill_tv {p q p' q' : Idx} (hqq : q ≠ q') (M : (Idx → F) → (Idx → F))
    (hcomm : ∀ v, M (tvm p q p' q' v) = tvm p q p' q' (M v)) (w : Idx → F)
    (hw : w p = 0 ∧ w p' = 0) : M w p = 0 ∧ M w p' = 0 := by
  have hUw : tvm p q p' q' w = w := by
    funext μ
    rw [tvm_apply, hw.1, hw.2]
    simp
  have h : tvm p q p' q' (M w) = M w := by rw [← hcomm, hUw]
  have h1 := congrFun h q
  have h2 := congrFun h q'
  rw [tvm_apply] at h1 h2
  simp [hqq, hqq.symm] at h1 h2
  exact ⟨h1, h2⟩

theorem kill_dg (lam : Idx → F) (M : (Idx → F) →ₗ[F] (Idx → F))
    (hcomm : ∀ v, M (dg lam v) = dg lam (M v)) (ν μ : Idx) (hne : lam μ ≠ lam ν) :
    M (Pi.single ν 1) μ = 0 := by
  classical
  have hDw : dg lam (Pi.single ν 1) = lam ν • (Pi.single ν 1 : Idx → F) := by
    funext μ'
    by_cases h : μ' = ν
    · subst h; simp [dg]
    · simp [dg, h]
  have h : dg lam (M (Pi.single ν 1)) = lam ν • M (Pi.single ν 1) := by
    rw [← hcomm, hDw, map_smul]
  have h1 := congrFun h μ
  simp only [dg, Pi.smul_apply, smul_eq_mul] at h1
  have : (lam μ - lam ν) * M (Pi.single ν 1) μ = 0 := by linear_combination h1
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

theorem comm_expand {p q p' q' : Idx} (M : (Idx → F) →ₗ[F] (Idx → F))
    (hcomm : ∀ v, M (tvm p q p' q' v) = tvm p q p' q' (M v)) (v : Idx → F) :
    v p • M (Pi.single q 1) - v p' • M (Pi.single q' 1) =
      (M v) p • (Pi.single q 1 : Idx → F) - (M v) p' • (Pi.single q' 1 : Idx → F) := by
  have h := hcomm v
  rw [tvm_eq, tvm_eq, map_sub, map_add, map_smul, map_smul, add_sub_assoc, add_sub_assoc] at h
  exact add_left_cancel h

theorem col_left {p q p' q' : Idx} (hpp : p ≠ p') (M : (Idx → F) →ₗ[F] (Idx → F))
    (hcomm : ∀ v, M (tvm p q p' q' v) = tvm p q p' q' (M v)) :
    M (Pi.single q 1) = (M (Pi.single p 1)) p • (Pi.single q 1 : Idx → F) -
      (M (Pi.single p 1)) p' • (Pi.single q' 1 : Idx → F) := by
  have := comm_expand M hcomm (Pi.single p 1)
  simpa [Pi.single_apply, hpp.symm] using this

theorem col_right {p q p' q' : Idx} (hpp : p ≠ p') (M : (Idx → F) →ₗ[F] (Idx → F))
    (hcomm : ∀ v, M (tvm p q p' q' v) = tvm p q p' q' (M v)) :
    M (Pi.single q' 1) = (M (Pi.single p' 1)) p' • (Pi.single q' 1 : Idx → F) -
      (M (Pi.single p' 1)) p • (Pi.single q 1 : Idx → F) := by
  have := comm_expand M hcomm (Pi.single p' 1)
  simp [hpp] at this
  rw [← neg_neg (M (Pi.single q' 1)), this, neg_sub]

theorem lamA_inl0 (c : F) : lamA c (Sum.inl 0) = c ^ 2 := by simp [lamA]

theorem lamA_inr0 (c : F) : lamA c (Sum.inr 0) = (c ^ 2)⁻¹ := by simp [lamA]

theorem lamA_of_ne (c : F) {μ : Idx} (h1 : μ ≠ Sum.inl 0) (h2 : μ ≠ Sum.inr 0) :
    lamA c μ = 1 := by
  simp [lamA, h1, h2]

theorem lamB_inl3 (c : F) : lamB c (Sum.inl 3) = (c ^ 2)⁻¹ := by simp [lamB]

theorem lamB_inr3 (c : F) : lamB c (Sum.inr 3) = c ^ 2 := by simp [lamB]

theorem lamB_of_ne (c : F) {μ : Idx} (h1 : μ ≠ Sum.inl 3) (h2 : μ ≠ Sum.inr 3) :
    lamB c μ = 1 := by
  simp [lamB, h1, h2]

theorem support_columns {c : F} (hc2 : c ^ 2 ≠ 1) (M : (Idx → F) ≃ₗ[F] (Idx → F))
    (h0 : ∀ v, M (tvm (.inl 0) (.inl 1) (.inr 1) (.inr 0) v) =
      tvm (.inl 0) (.inl 1) (.inr 1) (.inr 0) (M v))
    (h1 : ∀ v, M (tvm (.inr 1) (.inl 0) (.inr 0) (.inl 1) v) =
      tvm (.inr 1) (.inl 0) (.inr 0) (.inl 1) (M v))
    (h2 : ∀ v, M (tvm (.inl 2) (.inl 3) (.inr 3) (.inr 2) v) =
      tvm (.inl 2) (.inl 3) (.inr 3) (.inr 2) (M v))
    (h3 : ∀ v, M (tvm (.inl 2) (.inr 3) (.inl 3) (.inr 2) v) =
      tvm (.inl 2) (.inr 3) (.inl 3) (.inr 2) (M v))
    (hA : ∀ v, M (dg (lamA c) v) = dg (lamA c) (M v))
    (hB : ∀ v, M (dg (lamB c) v) = dg (lamB c) (M v)) :
    (∀ μ, μ ≠ Sum.inl 1 → μ ≠ Sum.inr 1 → μ ≠ Sum.inr 2 →
      M (Pi.single (Sum.inr 1) 1) μ = 0) ∧
    (∀ μ, μ ≠ Sum.inl 1 → μ ≠ Sum.inl 2 → μ ≠ Sum.inr 2 →
      M (Pi.single (Sum.inl 2) 1) μ = 0) := by
  classical
  have hc2' : (c ^ 2)⁻¹ ≠ 1 := fun h => hc2 (by simpa using h)
  have g1a : M (Pi.single (Sum.inr 1) 1) (Sum.inl 2) = 0 ∧
      M (Pi.single (Sum.inr 1) 1) (Sum.inr 3) = 0 :=
    kill_tv (by decide) M h2 _ (by simp)
  have g1b : M (Pi.single (Sum.inr 1) 1) (Sum.inl 2) = 0 ∧
      M (Pi.single (Sum.inr 1) 1) (Sum.inl 3) = 0 :=
    kill_tv (by decide) M h3 _ (by simp)
  have g2a : M (Pi.single (Sum.inl 2) 1) (Sum.inl 0) = 0 ∧
      M (Pi.single (Sum.inl 2) 1) (Sum.inr 1) = 0 :=
    kill_tv (by decide) M h0 _ (by simp)
  have g2b : M (Pi.single (Sum.inl 2) 1) (Sum.inr 1) = 0 ∧
      M (Pi.single (Sum.inl 2) 1) (Sum.inr 0) = 0 :=
    kill_tv (by decide) M h1 _ (by simp)
  have g1c : M (Pi.single (Sum.inr 1) 1) (Sum.inl 0) = 0 :=
    kill_dg (lamA c) M.toLinearMap hA (Sum.inr 1) (Sum.inl 0)
      (by rw [lamA_inl0, lamA_of_ne c (by decide) (by decide)]; exact hc2)
  have g1d : M (Pi.single (Sum.inr 1) 1) (Sum.inr 0) = 0 :=
    kill_dg (lamA c) M.toLinearMap hA (Sum.inr 1) (Sum.inr 0)
      (by rw [lamA_inr0, lamA_of_ne c (by decide) (by decide)]; exact hc2')
  have g2c : M (Pi.single (Sum.inl 2) 1) (Sum.inl 3) = 0 :=
    kill_dg (lamB c) M.toLinearMap hB (Sum.inl 2) (Sum.inl 3)
      (by rw [lamB_inl3, lamB_of_ne c (by decide) (by decide)]; exact hc2')
  have g2d : M (Pi.single (Sum.inl 2) 1) (Sum.inr 3) = 0 :=
    kill_dg (lamB c) M.toLinearMap hB (Sum.inl 2) (Sum.inr 3)
      (by rw [lamB_inr3, lamB_of_ne c (by decide) (by decide)]; exact hc2)
  refine ⟨fun μ h1 h2 h3 => ?_, fun μ h1 h2 h3 => ?_⟩
  · rcases μ with i | i <;> fin_cases i <;> simp_all
  · rcases μ with i | i <;> fin_cases i <;> simp_all

theorem eq_of_support₁ (g : Idx → F)
    (h : ∀ μ, μ ≠ Sum.inl 1 → μ ≠ Sum.inr 1 → μ ≠ Sum.inr 2 → g μ = 0) :
    g = g (Sum.inl 1) • (Pi.single (Sum.inl 1) 1 : Idx → F) +
      g (Sum.inr 1) • (Pi.single (Sum.inr 1) 1 : Idx → F) +
      g (Sum.inr 2) • (Pi.single (Sum.inr 2) 1 : Idx → F) := by
  funext μ
  rcases μ with i | i <;> fin_cases i <;> simp_all

theorem eq_of_support₂ (g : Idx → F)
    (h : ∀ μ, μ ≠ Sum.inl 1 → μ ≠ Sum.inl 2 → μ ≠ Sum.inr 2 → g μ = 0) :
    g = g (Sum.inl 1) • (Pi.single (Sum.inl 1) 1 : Idx → F) +
      g (Sum.inl 2) • (Pi.single (Sum.inl 2) 1 : Idx → F) +
      g (Sum.inr 2) • (Pi.single (Sum.inr 2) 1 : Idx → F) := by
  funext μ
  rcases μ with i | i <;> fin_cases i <;> simp_all

theorem columns_eq {c : F} (hc2 : c ^ 2 ≠ 1) (M : (Idx → F) ≃ₗ[F] (Idx → F))
    (h0 : ∀ v, M (tvm (.inl 0) (.inl 1) (.inr 1) (.inr 0) v) =
      tvm (.inl 0) (.inl 1) (.inr 1) (.inr 0) (M v))
    (h1 : ∀ v, M (tvm (.inr 1) (.inl 0) (.inr 0) (.inl 1) v) =
      tvm (.inr 1) (.inl 0) (.inr 0) (.inl 1) (M v))
    (h2 : ∀ v, M (tvm (.inl 2) (.inl 3) (.inr 3) (.inr 2) v) =
      tvm (.inl 2) (.inl 3) (.inr 3) (.inr 2) (M v))
    (h3 : ∀ v, M (tvm (.inl 2) (.inr 3) (.inl 3) (.inr 2) v) =
      tvm (.inl 2) (.inr 3) (.inl 3) (.inr 2) (M v))
    (hA : ∀ v, M (dg (lamA c) v) = dg (lamA c) (M v))
    (hB : ∀ v, M (dg (lamB c) v) = dg (lamB c) (M v)) :
    M (Pi.single (Sum.inl 0) 1) = M (Pi.single (Sum.inr 1) 1) (Sum.inr 1) •
      (Pi.single (Sum.inl 0) 1 : Idx → F) ∧
    M (Pi.single (Sum.inr 0) 1) = M (Pi.single (Sum.inr 1) 1) (Sum.inr 1) •
      (Pi.single (Sum.inr 0) 1 : Idx → F) ∧
    M (Pi.single (Sum.inl 1) 1) = M (Pi.single (Sum.inr 1) 1) (Sum.inr 1) •
      (Pi.single (Sum.inl 1) 1 : Idx → F) ∧
    M (Pi.single (Sum.inl 3) 1) = M (Pi.single (Sum.inl 2) 1) (Sum.inl 2) •
      (Pi.single (Sum.inl 3) 1 : Idx → F) ∧
    M (Pi.single (Sum.inr 3) 1) = M (Pi.single (Sum.inl 2) 1) (Sum.inl 2) •
      (Pi.single (Sum.inr 3) 1 : Idx → F) ∧
    M (Pi.single (Sum.inr 2) 1) = M (Pi.single (Sum.inl 2) 1) (Sum.inl 2) •
      (Pi.single (Sum.inr 2) 1 : Idx → F) := by
  classical
  obtain ⟨S1, S2⟩ := support_columns hc2 M h0 h1 h2 h3 hA hB
  have z1 : M (Pi.single (Sum.inr 1) 1) (Sum.inl 0) = 0 :=
    S1 _ (by decide) (by decide) (by decide)
  have z2 : M (Pi.single (Sum.inr 1) 1) (Sum.inr 0) = 0 :=
    S1 _ (by decide) (by decide) (by decide)
  have z3 : M (Pi.single (Sum.inl 2) 1) (Sum.inl 3) = 0 :=
    S2 _ (by decide) (by decide) (by decide)
  have z4 : M (Pi.single (Sum.inl 2) 1) (Sum.inr 3) = 0 :=
    S2 _ (by decide) (by decide) (by decide)
  have c1 := col_left (by decide) M.toLinearMap h1
  have c2 := col_right (by decide) M.toLinearMap h0
  have c4 := col_left (by decide) M.toLinearMap h2
  have c5 := col_left (by decide) M.toLinearMap h3
  have c3 := col_left (by decide) M.toLinearMap h0
  have c6 := col_right (by decide) M.toLinearMap h2
  simp only [LinearEquiv.coe_coe] at c1 c2 c3 c4 c5 c6
  rw [z2, zero_smul, sub_zero] at c1
  rw [z1, zero_smul, sub_zero] at c2
  rw [z4, zero_smul, sub_zero] at c4
  rw [z3, zero_smul, sub_zero] at c5
  rw [c1] at c3
  rw [c5] at c6
  simp at c3 c6
  exact ⟨c1, c2, c3, c4, c5, c6⟩

theorem pow_apply_of_eq (M : (Idx → F) ≃ₗ[F] (Idx → F)) {v : Idx → F} {a : F} (h : M v = a • v) :
    ∀ n : ℕ, (M ^ n) v = a ^ n • v := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, h, map_smul, ih, smul_smul, pow_succ, mul_comm]

theorem eq_one_of_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a : F} (h2 : a ^ 2 = 1)
    (hp : a ^ p = 1) : a = 1 := by
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
  rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul] at hp
  exact hp

theorem linear_part {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {c : F} (hc2 : c ^ 2 ≠ 1)
    (M : (Idx → F) ≃ₗ[F] (Idx → F))
    (hQ : ∀ v, quadPlus 4 F (M v) = quadPlus 4 F v)
    (hP : ∀ v w, polar (quadPlus 4 F) (M v) (M w) = polar (quadPlus 4 F) v w)
    (h0 : ∀ v, M (tvm (.inl 0) (.inl 1) (.inr 1) (.inr 0) v) =
      tvm (.inl 0) (.inl 1) (.inr 1) (.inr 0) (M v))
    (h1 : ∀ v, M (tvm (.inr 1) (.inl 0) (.inr 0) (.inl 1) v) =
      tvm (.inr 1) (.inl 0) (.inr 0) (.inl 1) (M v))
    (h2 : ∀ v, M (tvm (.inl 2) (.inl 3) (.inr 3) (.inr 2) v) =
      tvm (.inl 2) (.inl 3) (.inr 3) (.inr 2) (M v))
    (h3 : ∀ v, M (tvm (.inl 2) (.inr 3) (.inl 3) (.inr 2) v) =
      tvm (.inl 2) (.inr 3) (.inl 3) (.inr 2) (M v))
    (hA : ∀ v, M (dg (lamA c) v) = dg (lamA c) (M v))
    (hB : ∀ v, M (dg (lamB c) v) = dg (lamB c) (M v))
    (hpow : M ^ p = 1) :
    ∃ b : F, ∀ v, M v = xrm b v := by
  classical
  obtain ⟨S1, S2⟩ := support_columns hc2 M h0 h1 h2 h3 hA hB
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := columns_eq hc2 M h0 h1 h2 h3 hA hB
  have e1 := eq_of_support₁ _ S1
  have e2 := eq_of_support₂ _ S2
  have z1 : M (Pi.single (Sum.inr 1) 1) (Sum.inl 0) = 0 :=
    S1 _ (by decide) (by decide) (by decide)
  have z2 : M (Pi.single (Sum.inr 1) 1) (Sum.inr 0) = 0 :=
    S1 _ (by decide) (by decide) (by decide)
  have z3 : M (Pi.single (Sum.inr 1) 1) (Sum.inl 2) = 0 :=
    S1 _ (by decide) (by decide) (by decide)
  have z4 : M (Pi.single (Sum.inr 1) 1) (Sum.inr 3) = 0 :=
    S1 _ (by decide) (by decide) (by decide)
  have z5 : M (Pi.single (Sum.inr 1) 1) (Sum.inl 3) = 0 :=
    S1 _ (by decide) (by decide) (by decide)
  have y1 : M (Pi.single (Sum.inl 2) 1) (Sum.inl 0) = 0 :=
    S2 _ (by decide) (by decide) (by decide)
  have y2 : M (Pi.single (Sum.inl 2) 1) (Sum.inr 0) = 0 :=
    S2 _ (by decide) (by decide) (by decide)
  have y3 : M (Pi.single (Sum.inl 2) 1) (Sum.inr 1) = 0 :=
    S2 _ (by decide) (by decide) (by decide)
  have y4 : M (Pi.single (Sum.inl 2) 1) (Sum.inl 3) = 0 :=
    S2 _ (by decide) (by decide) (by decide)
  have y5 : M (Pi.single (Sum.inl 2) 1) (Sum.inr 3) = 0 :=
    S2 _ (by decide) (by decide) (by decide)
  have i1 := hP (Pi.single (Sum.inl 1) 1) (Pi.single (Sum.inr 1) 1)
  rw [c3] at i1
  simp [polar_quadPlus, Pi.single_apply] at i1
  have i2 := hP (Pi.single (Sum.inl 2) 1) (Pi.single (Sum.inr 2) 1)
  rw [c6] at i2
  simp [polar_quadPlus, Pi.single_apply] at i2
  have i3 := hQ (Pi.single (Sum.inr 1) 1)
  simp [quadPlus_apply, Pi.single_apply, Fin.sum_univ_four, z1, z2, z3, z4, z5] at i3
  have i4 := hQ (Pi.single (Sum.inl 2) 1)
  simp [quadPlus_apply, Pi.single_apply, Fin.sum_univ_four, y1, y2, y3, y4, y5] at i4
  have i5 := hP (Pi.single (Sum.inr 1) 1) (Pi.single (Sum.inl 2) 1)
  simp [polar_quadPlus, Pi.single_apply, Fin.sum_univ_four, z1, z2, z3, z4, z5, y1, y2, y3, y4,
    y5] at i5
  have ha0ne : M (Pi.single (Sum.inr 1) 1) (Sum.inr 1) ≠ 0 := by
    intro h
    rw [h] at i1
    simp at i1
  have hb0ne : M (Pi.single (Sum.inl 2) 1) (Sum.inl 2) ≠ 0 := by
    intro h
    rw [h] at i2
    simp at i2
  have a3z : M (Pi.single (Sum.inr 1) 1) (Sum.inl 1) = 0 := i3.resolve_right ha0ne
  have b3z : M (Pi.single (Sum.inl 2) 1) (Sum.inr 2) = 0 := i4.resolve_left hb0ne
  have hp1 : (Pi.single (Sum.inl 1) 1 : Idx → F) =
      M (Pi.single (Sum.inr 1) 1) (Sum.inr 1) ^ p • (Pi.single (Sum.inl 1) 1 : Idx → F) := by
    have := pow_apply_of_eq M c3 p
    rwa [hpow] at this
  have hp1' := congrFun hp1 (Sum.inl 1)
  simp at hp1'
  have ha0 : M (Pi.single (Sum.inr 1) 1) (Sum.inr 1) = 1 :=
    eq_one_of_pow hp2 (by rw [pow_two]; exact i1) hp1'.symm
  have hp2' : (Pi.single (Sum.inr 2) 1 : Idx → F) =
      M (Pi.single (Sum.inl 2) 1) (Sum.inl 2) ^ p • (Pi.single (Sum.inr 2) 1 : Idx → F) := by
    have := pow_apply_of_eq M c6 p
    rwa [hpow] at this
  have hp2'' := congrFun hp2' (Sum.inr 2)
  simp at hp2''
  have hb0 : M (Pi.single (Sum.inl 2) 1) (Sum.inl 2) = 1 :=
    eq_one_of_pow hp2 (by rw [pow_two]; exact i2) hp2''.symm
  have hlam : M (Pi.single (Sum.inr 1) 1) (Sum.inr 2) =
      -M (Pi.single (Sum.inl 2) 1) (Sum.inl 1) := by
    rw [ha0, hb0] at i5
    linear_combination i5
  rw [ha0] at c1 c2 c3 e1
  rw [hb0] at c4 c5 c6 e2
  rw [a3z, hlam] at e1
  rw [b3z] at e2
  generalize M (Pi.single (Sum.inl 2) 1) (Sum.inl 1) = m at e1 e2
  refine ⟨m, fun v => ?_⟩
  have hv : v = ∑ ν, v ν • (Pi.single ν 1 : Idx → F) := by
    funext μ
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul]
  rw [Fintype.sum_sum_type]
  simp only [Fin.sum_univ_four]
  rw [c1, c2, c3, c4, c5, c6, e1, e2]
  funext μ
  rcases μ with i | i <;> fin_cases i <;> simp [xrm] <;> ring

end CFSG.ClassicalInvolution.ModelFacts.D4Rigid
