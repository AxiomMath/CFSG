module

public import Mathlib.LinearAlgebra.Transvection.Generation
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Submodule

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zmod_two_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 :=
  (zmod_two_eq_zero_or_one a).resolve_left h

theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

theorem two_add_self (x : E) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem two_neg (x : E) : -x = x :=
  neg_eq_of_add_eq_zero_left (two_add_self x)

theorem two_sub (x y : E) : x - y = x + y := by
  rw [sub_eq_add_neg, two_neg]

theorem two_add_eq_iff {x y z : E} : x + y = z ↔ x = z + y := by
  constructor
  · rintro rfl
    rw [add_assoc, two_add_self, add_zero]
  · rintro rfl
    rw [add_assoc, two_add_self, add_zero]

theorem mem_span_singleton_iff_two {e x : E} : x ∈ (ZMod 2) ∙ e ↔ x = 0 ∨ x = e := by
  rw [mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rcases zmod_two_eq_zero_or_one a with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem transvection_apply {f : Dual (ZMod 2) E} {d : E} (h : f d = 0) (x : E) :
    LinearEquiv.transvection h x = x + f x • d :=
  rfl

theorem transvection_mul_self {f : Dual (ZMod 2) E} {d : E} (h : f d = 0) :
    LinearEquiv.transvection h * LinearEquiv.transvection h = 1 := by
  ext x
  rw [LinearEquiv.mul_apply, transvection_apply (x := x), transvection_apply, map_add, map_smul,
    h, smul_zero, add_zero, add_assoc, two_add_self, add_zero]
  rfl

theorem transvection_inv {f : Dual (ZMod 2) E} {d : E} (h : f d = 0) :
    (LinearEquiv.transvection h)⁻¹ = LinearEquiv.transvection h :=
  inv_eq_of_mul_eq_one_left (transvection_mul_self h)

theorem mul_transvection_mul_inv (g : E ≃ₗ[ZMod 2] E) {f : Dual (ZMod 2) E} {d : E}
    (h : f d = 0) (h' : (f ∘ₗ (g.symm : E →ₗ[ZMod 2] E)) (g d) = 0) :
    g * LinearEquiv.transvection h * g⁻¹ = LinearEquiv.transvection h' := by
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, transvection_apply, transvection_apply,
    map_add, map_smul]
  change g (g.symm x) + _ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem transvection_comp_apply_eq_zero (g : E ≃ₗ[ZMod 2] E) {f : Dual (ZMod 2) E} {d : E}
    (h : f d = 0) : (f ∘ₗ (g.symm : E →ₗ[ZMod 2] E)) (g d) = 0 := by
  simp [h]

theorem transvection_commute {f f' : Dual (ZMod 2) E} {d d' : E} (h : f d = 0) (h' : f' d' = 0)
    (h₁ : f d' = 0) (h₂ : f' d = 0) :
    LinearEquiv.transvection h * LinearEquiv.transvection h' =
      LinearEquiv.transvection h' * LinearEquiv.transvection h := by
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, transvection_apply (x := x),
    transvection_apply (x := x), transvection_apply, transvection_apply, map_add, map_add,
    map_smul, map_smul, h₁, h₂, smul_zero, smul_zero, add_zero, add_zero]
  abel

theorem transvection_mul_transvection_left {f : Dual (ZMod 2) E} {d d' : E} (h : f d = 0)
    (h' : f d' = 0) (h'' : f (d + d') = 0) :
    LinearEquiv.transvection h * LinearEquiv.transvection h' = LinearEquiv.transvection h'' := by
  ext x
  rw [LinearEquiv.mul_apply, transvection_apply (x := x), transvection_apply, transvection_apply,
    map_add, map_smul, h', smul_zero, add_zero, smul_add]
  abel

theorem transvection_mul_transvection_right {f f' : Dual (ZMod 2) E} {d : E} (h : f d = 0)
    (h' : f' d = 0) (h'' : (f + f') d = 0) :
    LinearEquiv.transvection h * LinearEquiv.transvection h' = LinearEquiv.transvection h'' := by
  ext x
  rw [LinearEquiv.mul_apply, transvection_apply (x := x), transvection_apply, transvection_apply,
    map_add, map_smul, h, smul_zero, add_zero, LinearMap.add_apply, add_smul]
  abel

theorem transvection_eq_one {f : Dual (ZMod 2) E} (h : f 0 = 0) :
    LinearEquiv.transvection h = 1 := by
  ext x
  rw [transvection_apply, smul_zero, add_zero]
  rfl

theorem transvection_zero_form {d : E} (h : (0 : Dual (ZMod 2) E) d = 0) :
    LinearEquiv.transvection h = 1 := by
  ext x
  rw [transvection_apply, LinearMap.zero_apply, zero_smul, add_zero]
  rfl

theorem not_isExceptional [FiniteDimensional (ZMod 2) E] (e : E ≃ₗ[ZMod 2] E) :
    ¬ e.IsExceptional := by
  rintro ⟨hlt, hne, a, ha⟩
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · have hsub : Subsingleton (E ⧸ (e : E →ₗ[ZMod 2] E).fixedSubmodule) := by
      refine ⟨fun x y => e.fixedReduce.injective ?_⟩
      rw [ha, ha, zero_smul, zero_smul]
    have := finrank_zero_of_subsingleton (R := ZMod 2)
      (M := E ⧸ (e : E →ₗ[ZMod 2] E).fixedSubmodule)
    omega
  · exact hne (LinearEquiv.ext fun x => by rw [ha, one_smul]; rfl)

theorem mem_transvections_of_mem_dilatransvections {e : E ≃ₗ[ZMod 2] E}
    (he : e ∈ LinearEquiv.dilatransvections (ZMod 2) E) :
    e ∈ LinearEquiv.transvections (ZMod 2) E := by
  obtain ⟨f, v, hev⟩ := he
  have hfv : f v = 0 := by
    by_contra hne
    have h1 : f v = 1 := zmod_two_eq_one_of_ne_zero hne
    have hv : e v = 0 := by
      have := congrArg (fun φ : E →ₗ[ZMod 2] E => φ v) hev
      simp only [LinearEquiv.coe_coe, LinearMap.transvection.apply, h1, one_smul] at this
      rw [this, two_add_self]
    have : v = 0 := e.injective (by rw [hv, map_zero])
    rw [this, map_zero] at h1
    exact zero_ne_one h1
  refine ⟨f, v, hfv, LinearEquiv.ext fun x => ?_⟩
  have := congrArg (fun φ : E →ₗ[ZMod 2] E => φ x) hev
  simpa only [LinearEquiv.coe_coe, LinearEquiv.transvection.coe_apply] using this

open scoped Pointwise in
theorem mem_closure_of_mem_pow {s : Set (E ≃ₗ[ZMod 2] E)} :
    ∀ (m : ℕ) {x : E ≃ₗ[ZMod 2] E}, x ∈ s ^ m → x ∈ Subgroup.closure s
  | 0, x, hx => by
    rw [pow_zero, Set.mem_one] at hx
    rw [hx]
    exact one_mem _
  | m + 1, x, hx => by
    rw [pow_succ] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
    exact mul_mem (mem_closure_of_mem_pow m hy) (Subgroup.subset_closure hz)

theorem closure_transvections_eq_top [FiniteDimensional (ZMod 2) E] :
    Subgroup.closure (LinearEquiv.transvections (ZMod 2) E) = ⊤ := by
  refine eq_top_iff.2 fun e _ => ?_
  have he := LinearEquiv.mem_transvections_pow_mul_dilatransvections_of_not_isExceptional
    (not_isExceptional e)
  obtain ⟨t, ht, d, hd, rfl⟩ := Set.mem_mul.1 he
  exact mul_mem (mem_closure_of_mem_pow _ ht)
    (Subgroup.subset_closure (mem_transvections_of_mem_dilatransvections hd))

theorem exists_dual_eq_one_of_notMem {S : Submodule (ZMod 2) E} {w : E} (hw : w ∉ S) :
    ∃ χ : Dual (ZMod 2) E, (∀ s ∈ S, χ s = 0) ∧ χ w = 1 := by
  obtain ⟨χ, hχ, hS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
  refine ⟨χ, fun s hs => ?_, zmod_two_eq_one_of_ne_zero hχ⟩
  have : χ s ∈ S.map χ := mem_map_of_mem hs
  rwa [hS, mem_bot] at this

theorem exists_mem_notMem_of_finrank_lt [FiniteDimensional (ZMod 2) E]
    {U S : Submodule (ZMod 2) E} (h : finrank (ZMod 2) S < finrank (ZMod 2) U) :
    ∃ k ∈ U, k ∉ S := by
  by_contra! hk
  exact absurd (Submodule.finrank_mono hk) (not_le.2 h)

theorem finrank_span_pair_le (a b : E) : finrank (ZMod 2) (span (ZMod 2) {a, b}) ≤ 2 := by
  classical
  have h := finrank_span_finset_le_card (R := ZMod 2) ({a, b} : Finset E)
  rw [Finset.coe_insert, Finset.coe_singleton] at h
  exact h.trans Finset.card_le_two

theorem finrank_ker_add_one_ge [FiniteDimensional (ZMod 2) E] (f : Dual (ZMod 2) E) :
    finrank (ZMod 2) E ≤ finrank (ZMod 2) (LinearMap.ker f) + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker f
  have h1 : finrank (ZMod 2) (LinearMap.range f) ≤ 1 :=
    (Submodule.finrank_le _).trans (by rw [finrank_self])
  omega

theorem finrank_ker_inf_ker_add_two_ge [FiniteDimensional (ZMod 2) E] (f f' : Dual (ZMod 2) E) :
    finrank (ZMod 2) E ≤ finrank (ZMod 2) ↥(LinearMap.ker f ⊓ LinearMap.ker f') + 2 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) (LinearMap.ker f')
  have h1 := finrank_ker_add_one_ge f
  have h2 := finrank_ker_add_one_ge f'
  have h3 := Submodule.finrank_le (LinearMap.ker f ⊔ LinearMap.ker f')
  omega

theorem exists_ne_zero_mem_of_finrank_pos [FiniteDimensional (ZMod 2) E] {U : Submodule (ZMod 2) E}
    (h : 0 < finrank (ZMod 2) U) : ∃ k ∈ U, k ≠ 0 := by
  refine Submodule.exists_mem_ne_zero_of_ne_bot fun hU => ?_
  rw [hU, finrank_bot] at h
  exact lt_irrefl 0 h

theorem mem_span_of_forall_smul_mem_span [FiniteDimensional (ZMod 2) E] {U : Submodule (ZMod 2) E}
    (hU : 3 ≤ finrank (ZMod 2) U) (e₀ w : E)
    (h : ∀ (χ : Dual (ZMod 2) E) (k : E), χ e₀ = 0 → χ k = 0 → k ∈ U → χ w • k ∈ (ZMod 2) ∙ e₀) :
    w ∈ (ZMod 2) ∙ e₀ := by
  by_contra hw
  obtain ⟨k, hkU, hk⟩ := exists_mem_notMem_of_finrank_lt (U := U) (S := span (ZMod 2) {e₀, w})
    ((finrank_span_pair_le e₀ w).trans_lt (by omega))
  have hwk : w ∉ span (ZMod 2) {e₀, k} := by
    intro hmem
    obtain ⟨a, b, hab⟩ := mem_span_pair.1 hmem
    rcases zmod_two_eq_zero_or_one b with rfl | rfl
    · exact hw (by rw [← hab, zero_smul, add_zero]; exact smul_mem _ _ (mem_span_singleton_self _))
    · refine hk (mem_span_pair.2 ⟨a, 1, ?_⟩)
      rw [one_smul, ← hab, one_smul, ← add_assoc, two_add_self, zero_add]
  obtain ⟨χ, hχ, hχw⟩ := exists_dual_eq_one_of_notMem hwk
  have h' := h χ k (hχ _ (subset_span (by simp))) (hχ _ (subset_span (by simp))) hkU
  rw [hχw, one_smul] at h'
  exact hk (span_mono (by simp) h')

theorem exists_eval_of_ker_le [FiniteDimensional (ZMod 2) E] {V₁ : Type*} [AddCommGroup V₁]
    [Module (ZMod 2) V₁] (κ : V₁ →ₗ[ZMod 2] Dual (ZMod 2) E) (μ : Dual (ZMod 2) V₁)
    (h : ∀ x, κ x = 0 → μ x = 0) : ∃ v : E, ∀ x, μ x = κ x v := by
  have hμ : μ ∈ (LinearMap.ker κ).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    exact fun x hx => h x hx
  obtain ⟨φ, hφ⟩ := (LinearMap.range_dualMap_eq_dualAnnihilator_ker κ).ge hμ
  refine ⟨(Module.evalEquiv (ZMod 2) E).symm φ, fun x => ?_⟩
  rw [← hφ, LinearMap.dualMap_apply]
  conv_lhs => rw [← (Module.evalEquiv (ZMod 2) E).apply_symm_apply φ]
  rfl

theorem exists_transvection_apply_eq {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ (f : Dual (ZMod 2) E) (d : E) (h : f d = 0), LinearEquiv.transvection h a = b := by
  by_cases hab : a = b
  · exact ⟨0, 0, by simp, by rw [hab, transvection_apply, smul_zero, add_zero]⟩
  have hind : b ∉ (ZMod 2) ∙ a := by
    rw [mem_span_singleton_iff_two]
    rintro (h | h)
    · exact hb h
    · exact hab h.symm
  obtain ⟨φ₁, hφ₁, hφ₁b⟩ := exists_dual_eq_one_of_notMem hind
  have ha' : a ∉ (ZMod 2) ∙ b := by
    rw [mem_span_singleton_iff_two]
    rintro (h | h)
    · exact ha h
    · exact hab h
  obtain ⟨φ₂, hφ₂, hφ₂a⟩ := exists_dual_eq_one_of_notMem ha'
  refine ⟨φ₁ + φ₂, a + b, ?_, ?_⟩
  · simp [hφ₁ a (mem_span_singleton_self a), hφ₁b, hφ₂ b (mem_span_singleton_self b), hφ₂a,
      two_add_self]
  · rw [transvection_apply]
    simp only [LinearMap.add_apply, hφ₁ a (mem_span_singleton_self a), hφ₂a, zero_add, one_smul]
    rw [← add_assoc, two_add_self, zero_add]

theorem exists_comp_eq_of_apply_eq_zero {e₀ : E} {φ ψ : Dual (ZMod 2) E} (hφ : φ ≠ 0)
    (hψ : ψ ≠ 0) (hφ₀ : φ e₀ = 0) (hψ₀ : ψ e₀ = 0) :
    ∃ g : E ≃ₗ[ZMod 2] E, g e₀ = e₀ ∧ φ ∘ₗ (g : E →ₗ[ZMod 2] E) = ψ := by
  by_cases hφψ : φ = ψ
  · exact ⟨1, rfl, by rw [hφψ]; rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra! h
    exact hφ (LinearMap.ext h)
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 0 := by
    by_contra! h
    exact hψ (LinearMap.ext h)
  obtain ⟨z, hz⟩ : ∃ z, (φ + ψ) z ≠ 0 := by
    by_contra! h
    refine hφψ (LinearMap.ext fun t => ?_)
    have := h t
    rw [LinearMap.add_apply] at this
    exact (two_add_eq_iff.1 this).trans (zero_add _)
  have hx1 := zmod_two_eq_one_of_ne_zero hx
  have hy1 := zmod_two_eq_one_of_ne_zero hy
  have hz1 := zmod_two_eq_one_of_ne_zero hz
  rw [LinearMap.add_apply] at hz1
  obtain ⟨w, hw1, hw2⟩ : ∃ w, φ w = 1 ∧ ψ w = 1 := by
    rcases zmod_two_eq_zero_or_one (ψ x) with hψx | hψx
    · rcases zmod_two_eq_zero_or_one (φ y) with hφy | hφy
      · refine ⟨x + y, ?_, ?_⟩ <;> simp [hx1, hy1, hψx, hφy]
      · exact ⟨y, hφy, hy1⟩
    · exact ⟨x, hx1, hψx⟩
  have hfd : (φ + ψ) w = 0 := by rw [LinearMap.add_apply, hw1, hw2]; rfl
  refine ⟨LinearEquiv.transvection hfd, ?_, LinearMap.ext fun t => ?_⟩
  · rw [transvection_apply, LinearMap.add_apply, hφ₀, hψ₀, add_zero, zero_smul, add_zero]
  · change φ (LinearEquiv.transvection hfd t) = ψ t
    rw [transvection_apply, map_add, map_smul, hw1, smul_eq_mul, mul_one, LinearMap.add_apply,
      ← add_assoc, two_add_self, zero_add]

end CFSG.GroupTheory.GLnTwoSplitting
