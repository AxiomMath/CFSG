module

public import CFSG.CGT.A8S.L2FC

public section

namespace CFSG.CGT.A8S.L2

open CFSG.CosetTable CFSG.CGT.A8S.N0

theorem swap_of_conj {f : PG 5 relsN0A8 → PG 5 relsN0A8} {e₁ c u : PG 5 relsN0A8}
    (h1 : e₁ * f (dE 0) * e₁⁻¹ = thE 0) (h2 : e₁ * f (dE 1) * e₁⁻¹ = u)
    (hc : c * thE 0 = thE 0 * c) (hu : u = c * thE 1 * c⁻¹) (i : Fin 2) :
    c⁻¹ * e₁ * f (dE i) * (c⁻¹ * e₁)⁻¹ = thE i := by
  have e : c⁻¹ * e₁ * f (dE i) * (c⁻¹ * e₁)⁻¹ = c⁻¹ * (e₁ * f (dE i) * e₁⁻¹) * c := by group
  rw [e]
  fin_cases i
  · change c⁻¹ * (e₁ * f (dE 0) * e₁⁻¹) * c = thE 0
    rw [h1, mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  · change c⁻¹ * (e₁ * f (dE 1) * e₁⁻¹) * c = thE 1
    rw [h2, hu]
    group

theorem swapA8 (f : PG 5 relsN0A8 → PG 5 relsN0A8)
    (hfD : ∀ x ∈ D0, f x ∈ D0)
    (hfmul : ∀ x ∈ D0, ∀ y ∈ D0, f (x * y) = f x * f y)
    (hfinj : ∀ x ∈ D0, ∀ y ∈ D0, f x = f y → x = y)
    (hfA : ∀ a ∈ D0, a ∈ T0 → f a ∈ B0) (hfB : ∀ b ∈ B0, f b ∈ T0) :
    ∃ e ∈ D0, ∀ i, e * f (dE i) * e⁻¹ = thE i := by
  have hf1 : f 1 = 1 := by
    have h := hfmul 1 D0.one_mem 1 D0.one_mem
    rw [one_mul] at h
    exact left_eq_mul.1 h
  have hd0 := dE_mem 0
  have hd1 := dE_mem 1
  have hd3 : dE 0 * (dE 0 * dE 0) = 1 :=
    avc_inj (by rw [avc_mul, avc_mul, avc_dE, avc_one]; exact goodC_spec.2.2.2)
  have hx3 : f (dE 0) * (f (dE 0) * f (dE 0)) = 1 := by
    rw [← hfmul _ hd0 _ hd0, ← hfmul _ hd0 _ (D0.mul_mem hd0 hd0), hd3, hf1]
  have hx1 : f (dE 0) ≠ 1 := by
    intro h
    have h' := congrArg avc (hfinj _ hd0 _ D0.one_mem (h.trans hf1.symm))
    rw [avc_dE, avc_one] at h'
    exact absurd h' (by decide)
  have hord : isOrd3 (avc (f (dE 0))) = true := by
    simp only [isOrd3, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true']
    refine ⟨by rw [← avc_mul, ← avc_mul, hx3, avc_one], ?_⟩
    rw [Bool.eq_false_iff]
    intro h
    exact hx1 (avc_inj ((Nat.eq_of_beq_eq_true h).trans avc_one.symm))
  have h1 := forall_D0 fc1_check (hfD _ hd0)
  rw [hord] at h1
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Nat.beq_eq] at h1
  obtain ⟨ec, hec, he⟩ := h1
  obtain ⟨e₁, he₁D, rfl⟩ := exists_mem_D0 hec
  have he₁ : e₁ * f (dE 0) * e₁⁻¹ = thE 0 := by
    rw [mul_eq_mul_of_cmul (by rw [avc_thE]; exact he : cmul (avc e₁) (avc (f (dE 0))) =
      cmul (avc (thE 0)) (avc e₁)), mul_inv_cancel_right]
  set f' : PG 5 relsN0A8 → PG 5 relsN0A8 := fun x => e₁ * f x * e₁⁻¹ with hf'
  have hf'mul : ∀ x ∈ D0, ∀ y ∈ D0, f' (x * y) = f' x * f' y := by
    intro x hx y hy
    simp only [hf', hfmul x hx y hy]
    group
  have hf'1 : f' 1 = 1 := by simp [hf', hf1]
  have hf'D : ∀ x ∈ D0, f' x ∈ D0 := fun x hx =>
    D0.mul_mem (D0.mul_mem he₁D (hfD x hx)) (D0.inv_mem he₁D)
  have hev : ∀ w, f' (evalD (dE 0) (dE 1) w) = evalD (thE 0) (f' (dE 1)) w := by
    intro w
    rw [evalD_of_mulOn hf'mul hf'1 hd0 hd1 w]
    simp only [hf', he₁]
  have hcode : ∀ w, avc (f' (evalD (dE 0) (dE 1) w)) = evD 3675 (avc (f' (dE 1))) w := by
    intro w
    rw [hev, avc_evalD, avc_thE]
    rfl
  have hcond : fcCond (avc (f' (dE 1))) = true := by
    simp only [fcCond, Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨fun w hw => ?_, fun w hw => ?_⟩, fun w hw => ?_⟩
    · have ha := List.all_eq_true.1 aWd_T0 w hw
      rw [← avc_evalD_dE, ← mem_T0_iff] at ha
      have hb := hfA _ (evalD_mem hd0 hd1 w) ha
      have hb' : f' (evalD (dE 0) (dE 1) w) ∈ B0 :=
        (Subgroup.mem_normalizer_iff.1 he₁D _).1 hb
      rw [← hcode, List.contains_iff_mem]
      exact (mem_B0_iff _).1 hb'
    · have hb := List.all_eq_true.1 bWd_B0 w hw
      rw [← avc_evalD_dE, List.contains_iff_mem, ← mem_B0_iff] at hb
      rw [← hcode, ← mem_T0_iff]
      exact conj_mem_T0 (hfB _ hb) e₁
    · have hne := List.all_eq_true.1 d0Words_ne w hw
      rw [← avc_evalD_dE] at hne
      rw [← hcode, Bool.not_eq_true', Bool.eq_false_iff]
      intro h
      have h' : f' (evalD (dE 0) (dE 1) w) = f' 1 :=
        avc_inj ((Nat.eq_of_beq_eq_true h).trans (by rw [hf'1, avc_one]))
      have hinj : evalD (dE 0) (dE 1) w = 1 := by
        refine hfinj _ (evalD_mem hd0 hd1 w) _ D0.one_mem ?_
        have h'' : e₁ * f (evalD (dE 0) (dE 1) w) * e₁⁻¹ = e₁ * f 1 * e₁⁻¹ := h'
        simpa using h''
      rw [hinj, avc_one] at hne
      exact absurd hne (by decide)
  have h2 := forall_D0 fc2_check (hf'D _ hd1)
  rw [hcond] at h2
  simp only [Bool.not_true, Bool.false_or, List.contains_iff_mem, goodC, List.mem_cons,
    List.not_mem_nil, or_false] at h2
  have hθ3 : thE 0 * (thE 0 * thE 0) = 1 :=
    avc_inj (by rw [avc_mul, avc_mul, avc_thE, avc_one]; exact goodC_spec.2.2.1)
  have hθinv : (thE 0)⁻¹ = thE 0 * thE 0 := inv_eq_of_mul_eq_one_right hθ3
  have hsw : ∀ c : PG 5 relsN0A8, c ∈ D0 → c * thE 0 = thE 0 * c →
      f' (dE 1) = c * thE 1 * c⁻¹ → ∃ e ∈ D0, ∀ i, e * f (dE i) * e⁻¹ = thE i :=
    fun c hcD hc hu => ⟨c⁻¹ * e₁, D0.mul_mem (D0.inv_mem hcD) he₁D,
      swap_of_conj he₁ rfl hc hu⟩
  rcases h2 with h2 | h2 | h2
  · refine hsw 1 D0.one_mem (by group) ?_
    rw [one_mul, inv_one, mul_one]
    exact avc_inj (h2.trans (avc_thE 1).symm)
  · refine hsw (thE 0) (thE_mem 0) rfl ?_
    rw [hθinv]
    exact avc_inj (by rw [h2, avc_mul, avc_mul, avc_mul, avc_thE, avc_thE]; exact goodC_spec.1.symm)
  · have hc3inv : (thE 0 * thE 0)⁻¹ = thE 0 :=
      inv_eq_of_mul_eq_one_right (by rw [mul_assoc]; exact hθ3)
    refine hsw (thE 0 * thE 0) (D0.mul_mem (thE_mem 0) (thE_mem 0)) (by group) ?_
    rw [hc3inv]
    exact avc_inj (by
      rw [h2, avc_mul, avc_mul, avc_mul, avc_thE, avc_thE]
      exact goodC_spec.2.1.symm)

end CFSG.CGT.A8S.L2
