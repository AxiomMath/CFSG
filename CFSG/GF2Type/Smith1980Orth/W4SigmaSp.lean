module

public import CFSG.Assembly.LowTwoRankDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth.W4Sigma

namespace Radical

open Module

variable {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] {β : LinearMap.BilinForm (ZMod 2) A}

theorem zmod2_add_self (v : A) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem zmod2_neg (v : A) : -v = v :=
  (eq_neg_of_add_eq_zero_left (zmod2_add_self v)).symm

theorem zmod2_eq_of_add_eq_zero {a b : A} (h : a + b = 0) : a = b := by
  rw [eq_neg_of_add_eq_zero_left h, zmod2_neg]

theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  revert x hx
  decide

theorem zmod2_eq_zero_of_ne_one {x : ZMod 2} (hx : x ≠ 1) : x = 0 := by
  revert x hx
  decide

theorem alt_comm (hβ : β.IsAlt) (a b : A) : β a b = β b a := by
  rw [← hβ.neg_eq a b, ZMod.neg_eq_self_mod_two]

theorem not_mem_span_of_perp {z x₀ : A} (hβ : β.IsAlt) (hx₀ : β z x₀ = 1) {u : A}
    (hu : β x₀ u = 0) (hu0 : u ≠ 0) : u ∉ (ZMod 2) ∙ z := by
  intro hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  rw [LinearMap.BilinForm.smul_right, alt_comm hβ, hx₀, mul_one] at hu
  exact hu0 (by rw [hu, zero_smul])

structure Elt (β : LinearMap.BilinForm (ZMod 2) A) (z : A) (q : A ≃ₗ[ZMod 2] A) : Prop where
  isometry : ∀ a b, β (q a) (q b) = β a b
  fix : q z = z
  triv : ∀ v, β z v = 0 → q v - v ∈ (ZMod 2) ∙ z

variable {z x₀ : A} {q q' : A ≃ₗ[ZMod 2] A}

theorem Elt.pairing (hq : Elt β z q) (a : A) : β z (q a) = β z a := by
  have h := hq.isometry z a
  rwa [hq.fix] at h

theorem Elt.perp_move (hq : Elt β z q) (a : A) : β z (q a - a) = 0 := by
  rw [LinearMap.BilinForm.sub_right, hq.pairing, sub_self]

theorem Elt.apply_perp (hq : Elt β z q) {x : A} (hx : β z x = 1) {v : A}
    (hv : β z v = 0) : q v = v + β v (q x - x) • z := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hq.triv v hv)
  have hqv : q v = v + c • z := by rw [hc]; abel
  have hp := hq.perp_move x
  have h1 := hq.isometry v x
  have hqx : q x = x + (q x - x) := by abel
  generalize q x - x = p at hp hqx ⊢
  rw [hqv, hqx] at h1
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, hx, hp] at h1
  have h2 : c = β v p := by grind
  rw [hqv, h2]

theorem Elt.mul_move (hq : Elt β z q) (hq' : Elt β z q') {x : A} (hx : β z x = 1) :
    (q * q') x - x = (q x - x) + (q' x - x) + β (q' x - x) (q x - x) • z := by
  have h := hq.apply_perp hx (hq'.perp_move x)
  have e1 : q (q' x) = q x + q (q' x - x) := by
    rw [← map_add]
    congr 1
    abel
  rw [LinearEquiv.mul_apply, e1, h]
  abel

theorem pairing_congr (hβ : β.IsAlt) {a a' b b' : A} (ha' : β z a' = 0) (hb' : β z b' = 0)
    (ha : a - a' ∈ (ZMod 2) ∙ z) (hb : b - b' ∈ (ZMod 2) ∙ z) : β a b = β a' b' := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hb
  have ea : a = a' + c • z := by rw [hc]; abel
  have eb : b = b' + d • z := by rw [hd]; abel
  have ha'z : β a' z = 0 := by rw [alt_comm hβ, ha']
  rw [ea, eb]
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hβ.self_eq_zero, ha'z, hb']
  grind

theorem Elt.theta_eq (hβ : β.IsAlt) (hq : Elt β z q) {x₁ x₂ : A} (h₁ : β z x₁ = 1)
    (h₂ : β z x₂ = 1) : β x₂ (q x₂ - x₂) = β x₁ (q x₁ - x₁) := by
  obtain ⟨d, rfl⟩ : ∃ d, x₂ = x₁ + d := ⟨x₂ - x₁, by abel⟩
  have hd : β z d = 0 := by
    rw [LinearMap.BilinForm.add_right, h₁] at h₂
    grind
  have hqd := hq.apply_perp h₁ hd
  have e : q (x₁ + d) - (x₁ + d) = (q x₁ - x₁) + β d (q x₁ - x₁) • z := by
    rw [map_add, hqd]
    abel
  have h1z : β x₁ z = 1 := by rw [alt_comm hβ, h₁]
  have hdz : β d z = 0 := by rw [alt_comm hβ, hd]
  rw [e]
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_right, h1z, hdz]
  grind

structure Data (β : LinearMap.BilinForm (ZMod 2) A) (z x₀ : A)
    (Qh : Subgroup (A ≃ₗ[ZMod 2] A)) : Prop where
  alt : β.IsAlt
  base : β z x₀ = 1
  elt : ∀ q ∈ Qh, Elt β z q
  faithful : ∀ q ∈ Qh, (∀ v, β z v = 0 → q v = v) → q = 1

theorem eq_of_sub_mem {Qh : Subgroup (A ≃ₗ[ZMod 2] A)} (hD : Data β z x₀ Qh)
    (hq : q ∈ Qh) (hq' : q' ∈ Qh) (h : q x₀ - q' x₀ ∈ (ZMod 2) ∙ z) : q = q' := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have hv : ∀ v, β z v = 0 → q v = q' v := by
    intro v hv
    have hvz : β v z = 0 := by rw [alt_comm hD.alt, hv]
    have e : q x₀ - x₀ = (q' x₀ - x₀) + c • z := by rw [hc]; abel
    rw [(hD.elt q hq).apply_perp hD.base hv, (hD.elt q' hq').apply_perp hD.base hv, e,
      LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hvz, mul_zero, add_zero]
  have h1 : q⁻¹ * q' = 1 := by
    refine hD.faithful _ (Qh.mul_mem (Qh.inv_mem hq) hq') fun v hv' => ?_
    rw [LinearEquiv.mul_apply, ← hv v hv']
    simp
  exact inv_mul_eq_one.mp h1

def Graph (β : LinearMap.BilinForm (ZMod 2) A) (z x₀ : A) (Qh : Subgroup (A ≃ₗ[ZMod 2] A))
    (u : A) (t : ZMod 2) : Prop :=
  ∃ q ∈ Qh, q x₀ - x₀ - u ∈ (ZMod 2) ∙ z ∧ β x₀ (q x₀ - x₀) = t

variable {Qh : Subgroup (A ≃ₗ[ZMod 2] A)}

theorem Graph.unique (hD : Data β z x₀ Qh) {u : A} {t t' : ZMod 2}
    (h : Graph β z x₀ Qh u t) (h' : Graph β z x₀ Qh u t') : t = t' := by
  obtain ⟨q, hq, hqu, rfl⟩ := h
  obtain ⟨q', hq', hq'u, rfl⟩ := h'
  have hqq : q = q' := by
    refine eq_of_sub_mem hD hq hq' ?_
    have := Submodule.sub_mem _ hqu hq'u
    rwa [show q x₀ - x₀ - u - (q' x₀ - x₀ - u) = q x₀ - q' x₀ by abel] at this
  rw [hqq]

theorem Graph.shift {u y : A} {t : ZMod 2} (h : Graph β z x₀ Qh u t) (hy : y ∈ (ZMod 2) ∙ z) :
    Graph β z x₀ Qh (u + y) t := by
  obtain ⟨q, hq, hqu, ht⟩ := h
  refine ⟨q, hq, ?_, ht⟩
  rw [show q x₀ - x₀ - (u + y) = (q x₀ - x₀ - u) - y by abel]
  exact Submodule.sub_mem _ hqu hy

theorem Graph.add (hD : Data β z x₀ Qh) {u u' : A} {t t' : ZMod 2} (hu : β z u = 0)
    (hu' : β z u' = 0) (h : Graph β z x₀ Qh u t) (h' : Graph β z x₀ Qh u' t') :
    Graph β z x₀ Qh (u + u') (t + t' + β u u') := by
  obtain ⟨q, hq, hqu, rfl⟩ := h
  obtain ⟨q', hq', hq'u, rfl⟩ := h'
  have hm := (hD.elt q hq).mul_move (hD.elt q' hq') hD.base
  refine ⟨q * q', Qh.mul_mem hq hq', ?_, ?_⟩
  · rw [hm, show q x₀ - x₀ + (q' x₀ - x₀) + β (q' x₀ - x₀) (q x₀ - x₀) • z - (u + u') =
      (q x₀ - x₀ - u) + (q' x₀ - x₀ - u') + β (q' x₀ - x₀) (q x₀ - x₀) • z by abel]
    exact Submodule.add_mem _ (Submodule.add_mem _ hqu hq'u)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z))
  · have h2 : β (q' x₀ - x₀) (q x₀ - x₀) = β u u' := by
      rw [pairing_congr hD.alt hu' hu hq'u hqu, alt_comm hD.alt]
    have hx0z : β x₀ z = 1 := by rw [alt_comm hD.alt, hD.base]
    rw [hm, LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_right, hx0z, h2, mul_one]

theorem conj_apply_sub (h q : A ≃ₗ[ZMod 2] A) (x : A) :
    (h * q * h⁻¹) x - x = h (q (h⁻¹ x) - h⁻¹ x) := by
  simp

theorem map_mem_span {h : A ≃ₗ[ZMod 2] A} (hz : h z = z) {y : A} (hy : y ∈ (ZMod 2) ∙ z) :
    h y ∈ (ZMod 2) ∙ z := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [map_smul, hz]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)

theorem Graph.map (hD : Data β z x₀ Qh) {h : A ≃ₗ[ZMod 2] A}
    (hhβ : ∀ a b, β (h a) (h b) = β a b) (hhz : h z = z)
    (hQn : ∀ q ∈ Qh, h * q * h⁻¹ ∈ Qh) {u : A} {t : ZMod 2}
    (hr : Graph β z x₀ Qh u t) : Graph β z x₀ Qh (h u) t := by
  obtain ⟨q, hq, hqu, rfl⟩ := hr
  have hx₁ : β z (h⁻¹ x₀) = 1 := by
    have := hhβ z (h⁻¹ x₀)
    rw [hhz] at this
    simpa [hD.base] using this.symm
  refine ⟨h * q * h⁻¹, hQn q hq, ?_, ?_⟩
  · have hd : β z (h⁻¹ x₀ - x₀) = 0 := by
      rw [LinearMap.BilinForm.sub_right, hx₁, hD.base, sub_self]
    have h1 := (hD.elt q hq).triv _ hd
    have h2 : q (h⁻¹ x₀) - h⁻¹ x₀ - u ∈ (ZMod 2) ∙ z := by
      rw [show q (h⁻¹ x₀) - h⁻¹ x₀ - u = (q (h⁻¹ x₀ - x₀) - (h⁻¹ x₀ - x₀)) +
        (q x₀ - x₀ - u) by rw [map_sub]; abel]
      exact Submodule.add_mem _ h1 hqu
    rw [conj_apply_sub, ← map_sub]
    exact map_mem_span hhz h2
  · rw [conj_apply_sub]
    calc β x₀ (h (q (h⁻¹ x₀) - h⁻¹ x₀))
        = β (h (h⁻¹ x₀)) (h (q (h⁻¹ x₀) - h⁻¹ x₀)) := by rw [show h (h⁻¹ x₀) = x₀ by simp]
      _ = β (h⁻¹ x₀) (q (h⁻¹ x₀) - h⁻¹ x₀) := hhβ _ _
      _ = β x₀ (q x₀ - x₀) := (hD.elt q hq).theta_eq hD.alt hD.base hx₁

theorem exists_pair_of_mem_perp (hβ : β.IsAlt) (hnd : β.Nondegenerate) (hx₀ : β z x₀ = 1)
    {u : A} (hz : β z u = 0) (hx : β x₀ u = 0) (hu : u ≠ 0) :
    ∃ u' : A, β z u' = 0 ∧ β x₀ u' = 0 ∧ β u u' = 1 := by
  obtain ⟨a, ha⟩ : ∃ a, β u a ≠ 0 := by
    by_contra! hcon
    exact hu (hnd.1 u hcon)
  have hx0z : β x₀ z = 1 := by rw [alt_comm hβ, hx₀]
  have huz : β u z = 0 := by rw [alt_comm hβ, hz]
  have hux : β u x₀ = 0 := by rw [alt_comm hβ, hx]
  have hax : β x₀ a = β a x₀ := alt_comm hβ _ _
  refine ⟨a - β a x₀ • z - β z a • x₀, ?_, ?_, ?_⟩
  · simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right,
      hβ.self_eq_zero, hx₀]
    grind
  · simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right,
      hβ.self_eq_zero, hx0z, hax]
    grind
  · simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, huz, hux]
    have := zmod2_eq_one_of_ne_zero ha
    grind

theorem exists_ker_not_mem_span {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (f : V →ₗ[ZMod 2] W)
    (h : finrank (ZMod 2) W + 1 < finrank (ZMod 2) V) (x : V) :
    ∃ y, f y = 0 ∧ y ∉ (ZMod 2) ∙ x := by
  by_contra! hcon
  have h1 : LinearMap.ker f ≤ (ZMod 2) ∙ x := fun y hy => hcon y (LinearMap.mem_ker.mp hy)
  have h2 := Submodule.finrank_mono h1
  have h3 : finrank (ZMod 2) ((ZMod 2) ∙ x) ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [Submodule.span_zero_singleton, finrank_bot]
      exact Nat.zero_le _
    · exact (finrank_span_singleton hx).le
  have h4 := LinearMap.finrank_range_add_finrank_ker f
  have h5 : finrank (ZMod 2) (LinearMap.range f) ≤ finrank (ZMod 2) W := Submodule.finrank_le _
  omega

variable [FiniteDimensional (ZMod 2) A]

theorem exists_mem_perp_ne_zero (β : LinearMap.BilinForm (ZMod 2) A)
    (h6 : finrank (ZMod 2) A = 6) (z x₀ : A) : ∃ u : A, β z u = 0 ∧ β x₀ u = 0 ∧ u ≠ 0 := by
  obtain ⟨y, hy, hy0⟩ := exists_ker_not_mem_span ((β z).prod (β x₀))
    (by simp [finrank_prod, h6]) 0
  have hy' : β z y = 0 ∧ β x₀ y = 0 := Prod.mk_eq_zero.mp hy
  exact ⟨y, hy'.1, hy'.2, fun h => hy0 (by rw [h]; exact Submodule.zero_mem _)⟩

theorem exists_orth_ne (β : LinearMap.BilinForm (ZMod 2) A) (h6 : finrank (ZMod 2) A = 6)
    (z x₀ u₁ : A) :
    ∃ u₃ : A, β z u₃ = 0 ∧ β x₀ u₃ = 0 ∧ β u₁ u₃ = 0 ∧ u₃ ≠ 0 ∧ u₃ ≠ u₁ := by
  obtain ⟨y, hy, hy0⟩ := exists_ker_not_mem_span ((β z).prod ((β x₀).prod (β u₁)))
    (by simp [finrank_prod, h6]) u₁
  have hy' : β z y = 0 ∧ β x₀ y = 0 ∧ β u₁ y = 0 :=
    ⟨(Prod.mk_eq_zero.mp hy).1, (Prod.mk_eq_zero.mp (Prod.mk_eq_zero.mp hy).2).1,
      (Prod.mk_eq_zero.mp (Prod.mk_eq_zero.mp hy).2).2⟩
  exact ⟨y, hy'.1, hy'.2.1, hy'.2.2, fun h => hy0 (by rw [h]; exact Submodule.zero_mem _),
    fun h => hy0 (by rw [h]; exact Submodule.mem_span_singleton_self _)⟩

theorem exists_two_values (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h6 : finrank (ZMod 2) A = 6) (hx₀ : β z x₀ = 1) {T : A → ZMod 2}
    (hT : ∀ u u', β z u = 0 → β z u' = 0 → T (u + u') = T u + T u' + β u u') :
    (∃ v : A, β z v = 0 ∧ β x₀ v = 0 ∧ v ≠ 0 ∧ T v = 0) ∧
      ∃ w : A, β z w = 0 ∧ β x₀ w = 0 ∧ w ≠ 0 ∧ T w = 1 := by
  obtain ⟨u₁, hz1, hx1, h10⟩ := exists_mem_perp_ne_zero β h6 z x₀
  obtain ⟨u₂, hz2, hx2, h12⟩ := exists_pair_of_mem_perp hβ hnd hx₀ hz1 hx1 h10
  obtain ⟨u₃, hz3, hx3, h13, h30, h31⟩ := exists_orth_ne β h6 z x₀ u₁
  have hsum : ∀ a b : A, a ≠ b → a + b ≠ 0 := fun a b hab h =>
    hab (zmod2_eq_of_add_eq_zero h)
  have hadd : ∀ a b : A, β z a = 0 → β z b = 0 → β z (a + b) = 0 := fun a b ha hb => by
    rw [LinearMap.BilinForm.add_right, ha, hb, add_zero]
  have hadd' : ∀ a b : A, β x₀ a = 0 → β x₀ b = 0 → β x₀ (a + b) = 0 := fun a b ha hb => by
    rw [LinearMap.BilinForm.add_right, ha, hb, add_zero]
  constructor
  · have hT13 := hT u₁ u₃ hz1 hz3
    rw [h13] at hT13
    by_cases h1 : T u₁ = 0
    · exact ⟨u₁, hz1, hx1, h10, h1⟩
    by_cases h3 : T u₃ = 0
    · exact ⟨u₃, hz3, hx3, h30, h3⟩
    refine ⟨u₁ + u₃, hadd _ _ hz1 hz3, hadd' _ _ hx1 hx3, hsum _ _ h31.symm, ?_⟩
    rw [hT13, zmod2_eq_one_of_ne_zero h1, zmod2_eq_one_of_ne_zero h3]
    decide
  · have hT12 := hT u₁ u₂ hz1 hz2
    rw [h12] at hT12
    have h20 : u₂ ≠ 0 := fun h => by simp [h] at h12
    by_cases h1 : T u₁ = 1
    · exact ⟨u₁, hz1, hx1, h10, h1⟩
    by_cases h2 : T u₂ = 1
    · exact ⟨u₂, hz2, hx2, h20, h2⟩
    refine ⟨u₁ + u₂, hadd _ _ hz1 hz2, hadd' _ _ hx1 hx2, hsum _ _ ?_, ?_⟩
    · rintro rfl
      simp [hβ.self_eq_zero] at h12
    · rw [hT12, zmod2_eq_zero_of_ne_one h1, zmod2_eq_zero_of_ne_one h2]
      decide

end Radical

theorem exists_not_transitive_of_radical
    {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (β : LinearMap.BilinForm (ZMod 2) A) (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h6 : Module.finrank (ZMod 2) A = 6) {z x₀ : A} (hz : z ≠ 0) (hx₀ : β z x₀ = 1)
    (Hz : Subgroup (A ≃ₗ[ZMod 2] A))
    (hHβ : ∀ h ∈ Hz, ∀ a b : A, β (h a) (h b) = β a b) (hHz : ∀ h ∈ Hz, h z = z)
    (Qh : Subgroup (A ≃ₗ[ZMod 2] A)) (hQH : Qh ≤ Hz)
    (hQn : ∀ h ∈ Hz, ∀ q ∈ Qh, h * q * h⁻¹ ∈ Qh)
    (hQ1 : ∀ q ∈ Qh, ∀ v : A, β z v = 0 → q v - v ∈ (ZMod 2) ∙ z)
    (hQsurj : ∀ w : A, β z w = 0 → ∃ q ∈ Qh, q x₀ - x₀ - w ∈ (ZMod 2) ∙ z)
    (hQt : ∀ q ∈ Qh, (∀ v : A, β z v = 0 → q v = v) → q = 1) :
    ∃ v w : A, β z v = 0 ∧ β z w = 0 ∧ v ∉ (ZMod 2) ∙ z ∧ w ∉ (ZMod 2) ∙ z ∧
      ∀ h ∈ Hz, h v - w ∉ (ZMod 2) ∙ z := by
  have _ := hz
  have hD : Radical.Data β z x₀ Qh :=
    ⟨hβ, hx₀, fun q hq => ⟨hHβ q (hQH hq), hHz q (hQH hq), hQ1 q hq⟩, hQt⟩
  have hex : ∀ u : A, ∃ t : ZMod 2, β z u = 0 → Radical.Graph β z x₀ Qh u t := by
    intro u
    by_cases hu : β z u = 0
    · obtain ⟨q, hq, hqu⟩ := hQsurj u hu
      exact ⟨_, fun _ => ⟨q, hq, hqu, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hu⟩
  choose T hT using hex
  have hperp : ∀ h ∈ Hz, ∀ u : A, β z u = 0 → β z (h u) = 0 := by
    intro h hh u hu
    have := hHβ h hh z u
    rwa [hHz h hh, hu] at this
  have hT1 : ∀ u u' : A, β z u = 0 → β z u' = 0 → T (u + u') = T u + T u' + β u u' := by
    intro u u' hu hu'
    refine Radical.Graph.unique hD (hT (u + u') ?_)
      (Radical.Graph.add hD hu hu' (hT u hu) (hT u' hu'))
    rw [LinearMap.BilinForm.add_right, hu, hu', add_zero]
  have hT2 : ∀ u y : A, β z u = 0 → y ∈ (ZMod 2) ∙ z → T (u + y) = T u := by
    intro u y hu hy
    refine Radical.Graph.unique hD (hT (u + y) ?_) ((hT u hu).shift hy)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [LinearMap.BilinForm.add_right, hu, LinearMap.BilinForm.smul_right,
      hβ.self_eq_zero, mul_zero, add_zero]
  have hT3 : ∀ h ∈ Hz, ∀ u : A, β z u = 0 → T (h u) = T u := fun h hh u hu =>
    Radical.Graph.unique hD (hT (h u) (hperp h hh u hu))
      (Radical.Graph.map hD (hHβ h hh) (hHz h hh) (hQn h hh) (hT u hu))
  obtain ⟨⟨v, hvz, hvx, hv0, hTv⟩, ⟨w, hwz, hwx, hw0, hTw⟩⟩ :=
    Radical.exists_two_values hβ hnd h6 hx₀ hT1
  refine ⟨v, w, hvz, hwz, Radical.not_mem_span_of_perp hβ hx₀ hvx hv0,
    Radical.not_mem_span_of_perp hβ hx₀ hwx hw0, fun h hh hmem => ?_⟩
  have hy : w - h v ∈ (ZMod 2) ∙ z := by
    rw [← neg_sub]
    exact Submodule.neg_mem _ hmem
  have := hT2 (h v) (w - h v) (hperp h hh v hvz) hy
  rw [add_sub_cancel, hT3 h hh v hvz, hTv, hTw] at this
  exact absurd this one_ne_zero

end CFSG.GF2Type.Smith1980Orth.W4Sigma
