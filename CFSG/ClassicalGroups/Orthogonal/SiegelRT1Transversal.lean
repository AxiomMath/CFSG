module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 CFSG.HardMathSupport.GuralnickMalle QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

section Transversal

variable {A A' : Submodule K V}

omit [CharP K 2] in
private theorem exists_mem_polar_ne_zero {x : V} (hx : x ∈ A) (hx0 : x ≠ 0)
    (h : A ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' = ⊥) :
    ∃ y ∈ A', polar Qf x y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hxperp : x ∈ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' :=
    mem_orthogonal_iff_polar.mpr fun w hw => by rw [polar_comm]; exact hcon w hw
  have hxbot : x ∈ A ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' :=
    Submodule.mem_inf.mpr ⟨hx, hxperp⟩
  rw [h, Submodule.mem_bot] at hxbot
  exact hx0 hxbot

omit [CharP K 2] in
private theorem finrank_ker_polar_eq_one (hA'2 : finrank K A' = 2)
    (h : A ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' = ⊥) {x : V} (hx : x ∈ A)
    (hx0 : x ≠ 0) :
    finrank K (LinearMap.ker ((polarBilin Qf x).domRestrict A')) = 1 := by
  have : FiniteDimensional K A' := Module.finite_of_finrank_pos (by omega)
  obtain ⟨y, hyA', hxy⟩ := exists_mem_polar_ne_zero hx hx0 h
  have hrank := LinearMap.finrank_range_add_finrank_ker ((polarBilin Qf x).domRestrict A')
  have hle : finrank K (LinearMap.range ((polarBilin Qf x).domRestrict A')) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range ((polarBilin Qf x).domRestrict A'))
    rwa [Module.finrank_self] at this
  have hpos : 0 < finrank K (LinearMap.range ((polarBilin Qf x).domRestrict A')) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨(polarBilin Qf x).domRestrict A' ⟨y, hyA'⟩, LinearMap.mem_range_self _ _⟩, ?_⟩
    intro h0
    have h1 : (polarBilin Qf x).domRestrict A' ⟨y, hyA'⟩ = 0 := congrArg Subtype.val h0
    exact hxy h1
  omega

omit [CharP K 2] in
private theorem exists_smul_of_polar_eq_zero (hA'2 : finrank K A' = 2)
    (h : A ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' = ⊥) {x x' y : V}
    (hx : x ∈ A) (hx0 : x ≠ 0) (hx'A' : x' ∈ A') (hx'0 : x' ≠ 0)
    (hxx' : polar Qf x x' = 0) (hyA' : y ∈ A') (hxy : polar Qf x y = 0) :
    ∃ c : K, y = c • x' := by
  have hN := finrank_ker_polar_eq_one hA'2 h hx hx0
  have hv : (⟨⟨x', hx'A'⟩, LinearMap.mem_ker.mpr hxx'⟩ :
      LinearMap.ker ((polarBilin Qf x).domRestrict A')) ≠ 0 := by
    intro h0
    have h1 : (⟨x', hx'A'⟩ : A') = 0 := congrArg Subtype.val h0
    exact hx'0 (congrArg Subtype.val h1)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).mp hN
    ⟨⟨y, hyA'⟩, LinearMap.mem_ker.mpr hxy⟩
  have h2 : c • (⟨x', hx'A'⟩ : A') = (⟨y, hyA'⟩ : A') := congrArg Subtype.val hc
  have h3 : c • x' = y := congrArg Subtype.val h2
  exact ⟨c, h3.symm⟩

omit [CharP K 2] in
theorem exists_transversal_point (hA'2 : finrank K A' = 2)
    (h : A ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' = ⊥) {x : V} (hx : x ∈ A)
    (hx0 : x ≠ 0) :
    ∃ x' ∈ A', x' ≠ 0 ∧ polar Qf x x' = 0 ∧
      ∀ y ∈ A', polar Qf x y = 0 → ∃ c : K, y = c • x' := by
  obtain ⟨v, hv0, -⟩ := finrank_eq_one_iff'.mp (finrank_ker_polar_eq_one hA'2 h hx hx0)
  obtain ⟨⟨x', hx'A'⟩, hxker⟩ := v
  have hxx' : polar Qf x x' = 0 := LinearMap.mem_ker.mp hxker
  have hx'0 : x' ≠ 0 := fun h0 => hv0 (Subtype.ext (Subtype.ext h0))
  exact ⟨x', hx'A', hx'0, hxx', fun y hyA' hxy =>
    exists_smul_of_polar_eq_zero hA'2 h hx hx0 hx'A' hx'0 hxx' hyA' hxy⟩

omit [CharP K 2] in
theorem eq_span_pair_of_transversal
    (hA's : ∀ w ∈ A', Qf w = 0)
    (hAA' : A ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' = ⊥)
    (hA'2 : finrank K A' = 2) {L : Submodule K V} (hL2 : finrank K L = 2)
    (hLs : ∀ w ∈ L, Qf w = 0) (hLA' : L ⊓ A' ≠ ⊥)
    {x x' : V} (hxL : x ∈ L) (hxA : x ∈ A) (hx0 : x ≠ 0) (hx'A' : x' ∈ A') (hx'0 : x' ≠ 0)
    (hxx' : polar Qf x x' = 0) :
    L = Submodule.span K ({x, x'} : Set V) := by
  obtain ⟨y, hyLA, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLA'
  obtain ⟨hyL, hyA'⟩ := Submodule.mem_inf.mp hyLA
  obtain ⟨c, hc⟩ := exists_smul_of_polar_eq_zero hA'2 hAA' hxA hx0 hx'A' hx'0 hxx' hyA'
    (polar_eq_zero_of_totallySingular hLs hxL hyL)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hy0
    rw [hc, zero_smul]
  have hx'L : x' ∈ L := by
    have hx'eq : x' = c⁻¹ • y := by
      rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hx'eq]
    exact L.smul_mem c⁻¹ hyL
  have hind : LinearIndependent K ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hsx : s • x = -(t • x') := eq_neg_of_add_eq_zero_left hst
    have hsA' : s • x ∈ A' := by
      rw [hsx]
      exact A'.neg_mem (A'.smul_mem t hx'A')
    have hsx0 : s • x = 0 := by
      have hmem : s • x ∈ A ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' :=
        Submodule.mem_inf.mpr ⟨A.smul_mem s hxA, le_orthogonal_of_totallySingular hA's hsA'⟩
      rw [hAA', Submodule.mem_bot] at hmem
      exact hmem
    have hs : s = 0 := (smul_eq_zero.mp hsx0).resolve_right hx0
    subst hs
    rw [zero_smul, zero_add] at hst
    exact ⟨rfl, (smul_eq_zero.mp hst).resolve_right hx'0⟩
  exact (span_pair_eq_of_finrank_eq_two hL2 hxL hx'L hind).symm

omit [CharP K 2] in
private theorem mem_orthogonal_span_pair_of_polar_eq_zero {x y z : V}
    (hx : polar Qf x z = 0) (hy : polar Qf y z = 0) :
    z ∈ LinearMap.BilinForm.orthogonal (polarBilin Qf) (Submodule.span K ({x, y} : Set V)) := by
  rw [mem_orthogonal_iff_polar]
  intro n hn
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hn
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, smul_eq_mul, hx, hy,
    mul_zero, add_zero]

omit [CharP K 2] in
private theorem exists_smul_eq_of_not_linearIndependent_pair {x y : V} (hx0 : x ≠ 0)
    (hy0 : y ≠ 0) (hxy : ¬LinearIndependent K ![x, y]) :
    ∃ c : K, c ≠ 0 ∧ y = c • x := by
  rw [linearIndependent_fin2] at hxy
  simp only [not_and, not_forall, ne_eq, not_not, Matrix.cons_val_one,
    Matrix.cons_val_zero] at hxy
  obtain ⟨a, ha⟩ := hxy hy0
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [← ha, zero_smul])
  exact ⟨a⁻¹, inv_ne_zero ha0, by rw [← ha, inv_smul_smul₀ ha0]⟩

omit [CharP K 2] in
theorem disjoint_span_pair_of_transversal
    (hA's : ∀ w ∈ A', Qf w = 0)
    (hAA' : A ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' = ⊥)
    (hA'A : A' ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A = ⊥)
    (hA2 : finrank K A = 2)
    {x y x' y' : V} (hxA : x ∈ A) (hyA : y ∈ A) (hxy : LinearIndependent K ![x, y])
    (hx'A' : x' ∈ A') (hy'A' : y' ∈ A') (hx'0 : x' ≠ 0) (_hy'0 : y' ≠ 0)
    (hxx' : polar Qf x x' = 0) (hyy' : polar Qf y y' = 0) :
    Disjoint (Submodule.span K ({x, x'} : Set V)) (Submodule.span K ({y, y'} : Set V)) := by
  have hspan : Submodule.span K ({x, y} : Set V) = A :=
    span_pair_eq_of_finrank_eq_two hA2 hxA hyA hxy
  rw [Submodule.disjoint_def]
  intro v hv1 hv2
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv1
  obtain ⟨γ, δ, hv⟩ := Submodule.mem_span_pair.mp hv2
  have hwA : α • x + (-γ) • y ∈ A := A.add_mem (A.smul_mem α hxA) (A.smul_mem (-γ) hyA)
  have hwA' : α • x + (-γ) • y ∈ A' := by
    have he : α • x + (-γ) • y = δ • y' + (-β) • x' := by
      linear_combination (norm := module) -hv
    rw [he]
    exact A'.add_mem (A'.smul_mem δ hy'A') (A'.smul_mem (-β) hx'A')
  have hw0 : α • x + (-γ) • y = 0 := by
    have hmem : α • x + (-γ) • y ∈ A ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' :=
      Submodule.mem_inf.mpr ⟨hwA, le_orthogonal_of_totallySingular hA's hwA'⟩
    rw [hAA', Submodule.mem_bot] at hmem
    exact hmem
  obtain ⟨hα, hγ⟩ := LinearIndependent.pair_iff.mp hxy α (-γ) hw0
  have hγ' : γ = 0 := neg_eq_zero.mp hγ
  subst hα hγ'
  simp only [zero_smul, zero_add] at hv
  have hβ : β = 0 := by
    by_contra hβ
    have hpy : polar Qf y x' = 0 := by
      have h1 : polar Qf y (δ • y') = polar Qf y (β • x') := congrArg (polar Qf y) hv
      rw [QuadraticMap.polar_smul_right, hyy', smul_zero, QuadraticMap.polar_smul_right,
        smul_eq_mul] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left hβ
    have hx'orth : x' ∈ LinearMap.BilinForm.orthogonal (polarBilin Qf) A := by
      have h := mem_orthogonal_span_pair_of_polar_eq_zero hxx' hpy
      rwa [hspan] at h
    have hmem : x' ∈ A' ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A :=
      Submodule.mem_inf.mpr ⟨hx'A', hx'orth⟩
    rw [hA'A, Submodule.mem_bot] at hmem
    exact hx'0 hmem
  subst hβ
  simp

omit [CharP K 2] in
theorem eq_of_transversal_inf_ne_bot
    (hA's : ∀ w ∈ A', Qf w = 0)
    (hAA' : A ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' = ⊥)
    (hA'A : A' ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) A = ⊥) (hA2 : finrank K A = 2)
    (hA'2 : finrank K A' = 2) {L L' : Submodule K V} (hL2 : finrank K L = 2)
    (hL'2 : finrank K L' = 2) (hLs : ∀ w ∈ L, Qf w = 0) (hL's : ∀ w ∈ L', Qf w = 0)
    (hLA : L ⊓ A ≠ ⊥) (hLA' : L ⊓ A' ≠ ⊥) (hL'A : L' ⊓ A ≠ ⊥) (hL'A' : L' ⊓ A' ≠ ⊥)
    (hLL' : L ⊓ L' ≠ ⊥) : L = L' := by
  obtain ⟨x, hxLA, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLA
  obtain ⟨y, hyL'A, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL'A
  have hxL : x ∈ L := (Submodule.mem_inf.mp hxLA).1
  have hxA : x ∈ A := (Submodule.mem_inf.mp hxLA).2
  have hyL' : y ∈ L' := (Submodule.mem_inf.mp hyL'A).1
  have hyA : y ∈ A := (Submodule.mem_inf.mp hyL'A).2
  obtain ⟨x', hx'A', hx'0, hxx', -⟩ := exists_transversal_point hA'2 hAA' hxA hx0
  obtain ⟨y', hy'A', hy'0, hyy', -⟩ := exists_transversal_point hA'2 hAA' hyA hy0
  have hLeq : L = Submodule.span K ({x, x'} : Set V) :=
    eq_span_pair_of_transversal hA's hAA' hA'2 hL2 hLs hLA' hxL hxA hx0 hx'A' hx'0 hxx'
  have hL'eq : L' = Submodule.span K ({y, y'} : Set V) :=
    eq_span_pair_of_transversal hA's hAA' hA'2 hL'2 hL's hL'A' hyL' hyA hy0 hy'A' hy'0 hyy'
  by_cases hxy : LinearIndependent K ![x, y]
  ·
    exfalso
    have hdisj := disjoint_span_pair_of_transversal hA's hAA' hA'A hA2 hxA hyA hxy hx'A' hy'A'
      hx'0 hy'0 hxx' hyy'
    apply hLL'
    rw [hLeq, hL'eq]
    exact disjoint_iff.mp hdisj
  ·
    obtain ⟨c, hc0, hyc⟩ := exists_smul_eq_of_not_linearIndependent_pair hx0 hy0 hxy
    have hyx' : polar Qf y x' = 0 := by
      rw [hyc, QuadraticMap.polar_smul_left, smul_eq_mul, hxx', mul_zero]
    have hL'eq' : L' = Submodule.span K ({y, x'} : Set V) :=
      eq_span_pair_of_transversal hA's hAA' hA'2 hL'2 hL's hL'A' hyL' hyA hy0 hx'A' hx'0 hyx'
    have hxmem : x ∈ Submodule.span K ({y, x'} : Set V) := by
      have hx_eq : x = c⁻¹ • y := by rw [hyc, inv_smul_smul₀ hc0]
      rw [hx_eq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert y {x'}))
    have hymem : y ∈ Submodule.span K ({x, x'} : Set V) := by
      rw [hyc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert x {x'}))
    rw [hLeq, hL'eq']
    refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · exact Set.insert_subset_iff.mpr ⟨hxmem, Set.singleton_subset_iff.mpr
        (Submodule.subset_span (Set.mem_insert_of_mem y (Set.mem_singleton x')))⟩
    · exact Set.insert_subset_iff.mpr ⟨hymem, Set.singleton_subset_iff.mpr
        (Submodule.subset_span (Set.mem_insert_of_mem x (Set.mem_singleton x')))⟩

end Transversal

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
