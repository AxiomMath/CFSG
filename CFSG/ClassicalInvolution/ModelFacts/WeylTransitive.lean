module

public import CFSG.ClassicalInvolution.ModelFacts.RootLength
public import CFSG.LieType.Steinberg.Bridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

section Abstract

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem roots_empty_subset (D : Set I) : roots hA ∅ ⊆ roots hA D := by
  rintro γ (⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩)
  · exact Or.inl ⟨w, i, rfl⟩
  · exact absurd hi (Set.notMem_empty i)

theorem exists_reflection {γ : I → ℤ} (hγ : γ ∈ roots hA ∅) :
    ∃ s : (coxeterMatrix hA).Group, ∀ v : I → ℤ, ∃ m : ℤ,
      (m : ℚ) * lenSq hA γ = 2 * form hA (toRat γ) (toRat v) ∧
        weylAction hA s v = v - m • γ := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · exact ⟨w * (coxeterMatrix hA).toCoxeterSystem.simple i * w⁻¹, fun v =>
      ⟨coroot A i (weylAction hA w⁻¹ v), OfCartan.coroot_mul_form_self hA w i v,
        OfCartan.weylAction_conj_simple hA w i v⟩⟩
  · exact absurd hi (Set.notMem_empty i)

theorem exists_weylAction_eq_neg {γ : I → ℤ} (hγ : γ ∈ roots hA ∅) :
    ∃ s : (coxeterMatrix hA).Group, weylAction hA s γ = -γ := by
  obtain ⟨s, hs⟩ := exists_reflection hA hγ
  obtain ⟨m, hm, hsm⟩ := hs γ
  have hpos := lenSq_pos hA (ne_zero_of_mem_roots hA ∅ hγ)
  have h2 : (m : ℚ) = 2 := mul_right_cancel₀ hpos.ne' (by rw [hm]; rfl)
  have hm2 : m = 2 := by exact_mod_cast h2
  refine ⟨s, ?_⟩
  rw [hsm, hm2, two_smul]
  abel

private def Orth (α y : I → ℤ) : Prop :=
  ∀ w : (coxeterMatrix hA).Group, form hA (toRat (weylAction hA w α)) (toRat y) = 0

private theorem Orth.sub {α y z : I → ℤ} (hy : Orth hA α y) (hz : Orth hA α z) :
    Orth hA α (y - z) := by
  intro w
  rw [map_sub, map_sub, hy w, hz w, sub_zero]

private theorem Orth.of_zsmul {α y : I → ℤ} {m : ℤ} (hm : m ≠ 0) (h : Orth hA α (m • y)) :
    Orth hA α y := by
  intro w
  have := h w
  rw [map_zsmul, map_zsmul, zsmul_eq_mul] at this
  exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast hm)

private theorem Orth.map_reflection {α y : I → ℤ} (i : I) (hy : Orth hA α y) :
    Orth hA α (reflection A i y) := by
  intro w
  have h := form_reflection hA i (weylAction hA w α) (reflection A i y)
  have hii : reflection A i (reflection A i y) = y := by
    simpa using LinearMap.congr_fun (reflection_mul_self (hA.apply_self i)) y
  rw [hii] at h
  have h' := hy ((coxeterMatrix hA).toCoxeterSystem.simple i * w)
  rw [weylAction_mul_apply, weylAction_simple] at h'
  rw [← h]
  exact h'

private theorem orth_single_or (α : I → ℤ) (i : I) :
    Orth hA α (Pi.single i 1) ∨ ∀ y, Orth hA α y → coroot A i y = 0 := by
  by_cases hi : Orth hA α (Pi.single i 1)
  · exact Or.inl hi
  · right
    intro y hy
    by_contra hne
    apply hi
    have h1 := (hy.map_reflection hA i).sub hA hy
    have e : reflection A i y - y = (-coroot A i y) • (Pi.single i 1 : I → ℤ) := by
      rw [reflection_apply_coroot]
      simp
    rw [e] at h1
    exact h1.of_zsmul hA (neg_ne_zero.mpr hne)

theorem eq_zero_of_forall_form_weylAction (hirr : IsIrreducible A) {α : I → ℤ} (hα : α ≠ 0)
    {y : I → ℤ}
    (hy : ∀ w : (coxeterMatrix hA).Group,
      form hA (toRat (weylAction hA w α)) (toRat y) = 0) : y = 0 := by
  have hyO : Orth hA α y := hy
  by_cases hS : ∃ i, Orth hA α (Pi.single i 1)
  · exfalso
    obtain ⟨i₀, hi₀⟩ := hS
    have hall : ∀ j, Orth hA α (Pi.single j 1) := by
      have := hirr {j | Orth hA α (Pi.single j 1)} ⟨i₀, hi₀⟩ ?_
      · exact fun j => this j
      · intro i hi j hij
        rcases orth_single_or hA α j with hj | hj
        · exact hj
        · exfalso
          have h1 := hj _ hi
          rw [coroot_single] at h1
          exact hij (hA.apply_eq_zero_iff.mpr h1)
    have h0 : form hA (toRat α) (toRat α) = 0 := by
      rw [form_eq_sum]
      refine Finset.sum_eq_zero fun l _ => ?_
      have h := hall l 1
      rw [map_one, Module.End.one_apply, toRat_single] at h
      rw [h, mul_zero]
    exact (lenSq_pos hA hα).ne' h0
  · push Not at hS
    have hcor : ∀ i, coroot A i y = 0 := fun i =>
      (orth_single_or hA α i).resolve_left (hS i) y hyO
    by_contra hy0
    have hy0' : toRat y ≠ 0 := fun h => hy0 (toRat_injective (by rw [h, map_zero]))
    refine (form_pos hA hy0').ne' ?_
    rw [form_eq_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h := hcor l
    rw [coroot_apply] at h
    have h' : ∑ k, (A l k : ℚ) * (y k : ℚ) = 0 := by exact_mod_cast h
    rw [form_single_right]
    simp [toRat_apply, h']

theorem exists_weylAction_eq_of_lenSq_eq (hirr : IsIrreducible A) {α β : I → ℤ}
    (hα : α ∈ roots hA ∅) (hβ : β ∈ roots hA ∅) (h : lenSq hA α = lenSq hA β) :
    ∃ w : (coxeterMatrix hA).Group, weylAction hA w α = β := by
  have hα0 := ne_zero_of_mem_roots hA ∅ hα
  have hβ0 := ne_zero_of_mem_roots hA ∅ hβ
  have hc : 0 < lenSq hA β := lenSq_pos hA hβ0
  obtain ⟨w₀, hw₀⟩ : ∃ w : (coxeterMatrix hA).Group,
      form hA (toRat (weylAction hA w α)) (toRat β) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hβ0 (eq_zero_of_forall_form_weylAction hA hirr hα0 hcon)
  obtain ⟨w, hw⟩ : ∃ w : (coxeterMatrix hA).Group,
      0 < form hA (toRat (weylAction hA w α)) (toRat β) := by
    rcases lt_or_gt_of_ne hw₀ with hneg | hpos
    · obtain ⟨s, hs⟩ := exists_weylAction_eq_neg hA (weylAction_mem_roots hA w₀ hα)
      refine ⟨s * w₀, ?_⟩
      rw [weylAction_mul_apply, hs, map_neg, map_neg, LinearMap.neg_apply]
      linarith
    · exact ⟨w₀, hpos⟩
  have hγ : weylAction hA w α ∈ roots hA ∅ := weylAction_mem_roots hA w hα
  have hγl : lenSq hA (weylAction hA w α) = lenSq hA β := by rw [lenSq_weylAction, h]
  set γ := weylAction hA w α with hγdef
  set b := form hA (toRat γ) (toRat β) with hb
  obtain ⟨sβ, hsβ⟩ := exists_reflection hA hβ
  obtain ⟨sγ, hsγ⟩ := exists_reflection hA hγ
  obtain ⟨m₁, hm₁, hs₁⟩ := hsβ γ
  obtain ⟨m₂, hm₂, hs₂⟩ := hsγ β
  obtain ⟨m₃, hm₃, hs₃⟩ := hsγ γ
  have hbc : form hA (toRat β) (toRat γ) = b := form_comm hA _ _
  have hm₁b : (m₁ : ℚ) * lenSq hA β = 2 * b := by rw [hm₁, hbc]
  have hm₂b : (m₂ : ℚ) * lenSq hA β = 2 * b := by rw [← hγl]; exact hm₂
  have hm₁₂ : m₁ = m₂ := by
    have : (m₁ : ℚ) = m₂ := mul_right_cancel₀ hc.ne' (hm₁b.trans hm₂b.symm)
    exact_mod_cast this
  have hm₃2 : m₃ = 2 := by
    have : (m₃ : ℚ) = 2 := mul_right_cancel₀ (lenSq_pos hA (ne_zero_of_mem_roots hA ∅ hγ)).ne'
      (by rw [hm₃]; rfl)
    exact_mod_cast this
  have h3 : weylAction hA sγ γ = -γ := by rw [hs₃, hm₃2, two_smul]; abel
  have hcs : b ^ 2 ≤ lenSq hA β * lenSq hA β := by
    have := sq_form_le hA (toRat γ) (toRat β)
    rw [← hb] at this
    have e : form hA (toRat γ) (toRat γ) = lenSq hA β := hγl
    rwa [e] at this
  have hm_pos : 0 < m₁ := by
    have : (0 : ℚ) < m₁ := by
      by_contra hneg
      push Not at hneg
      nlinarith
    exact_mod_cast this
  have hm_le : m₁ ≤ 2 := by
    by_contra hgt
    push Not at hgt
    have h3 : (3 : ℚ) ≤ m₁ := by exact_mod_cast hgt
    have hb3 : 3 * lenSq hA β ≤ 2 * b := by
      rw [← hm₁b]
      exact mul_le_mul_of_nonneg_right h3 hc.le
    nlinarith [mul_pos hc hc,
      mul_nonneg (sub_nonneg.2 hb3) (by linarith : 0 ≤ 2 * b + 3 * lenSq hA β)]
  interval_cases m₁
  ·
    have h1 : weylAction hA sβ γ = γ - β := by rw [hs₁, one_smul]
    have h2 : weylAction hA sγ β = β - γ := by rw [hs₂, ← hm₁₂, one_smul]
    refine ⟨sγ * sβ * sγ * w, ?_⟩
    simp only [weylAction_mul_apply]
    rw [← hγdef, h3, map_neg, h1, map_neg, map_sub, h3, h2]
    abel
  ·
    have hbc2 : b = lenSq hA β := by
      have := hm₁b
      push_cast at this
      linarith
    by_contra hne
    have hγβ : γ - β ≠ 0 := fun h0 => hne ⟨w, sub_eq_zero.mp h0⟩
    have hpos := lenSq_pos hA hγβ
    have e : lenSq hA (γ - β) = lenSq hA γ - 2 * b + lenSq hA β := by
      simp only [lenSq, map_sub, LinearMap.sub_apply]
      rw [hbc, ← hb]
      ring
    rw [e, hγl, hbc2] at hpos
    linarith

theorem exists_weylAction_eq_of_isLongest (hirr : IsIrreducible A) {D : Set I}
    (hD : ∀ i ∈ D, ∀ j, symmetrizer hA j < 4 * symmetrizer hA i)
    {γ γ' : I → ℤ} (hγ : IsLongest hA D γ) (hγ' : IsLongest hA D γ') :
    ∃ w : (coxeterMatrix hA).Group, weylAction hA w γ = γ' := by
  have hl := hγ.lenSq_eq hγ'
  have h4 : ∀ (x : I → ℤ), lenSq hA (2 • x) = 4 * lenSq hA x := lenSq_two_nsmul hA
  rcases hγ.mem with ⟨u, i, rfl⟩ | ⟨u, i, hi, rfl⟩ <;>
    rcases hγ'.mem with ⟨u', i', rfl⟩ | ⟨u', i', hi', rfl⟩
  · exact exists_weylAction_eq_of_lenSq_eq hA hirr (Or.inl ⟨u, i, rfl⟩) (Or.inl ⟨u', i', rfl⟩) hl
  · exfalso
    have := hγ.2 _ hγ'.mem
    rw [h4, lenSq_weylAction, lenSq_weylAction, lenSq_single, lenSq_single] at this
    have := hD i' hi' i
    linarith
  · exfalso
    have := hγ'.2 _ hγ.mem
    rw [h4, lenSq_weylAction, lenSq_weylAction, lenSq_single, lenSq_single] at this
    have := hD i hi i'
    linarith
  · rw [h4, h4] at hl
    obtain ⟨w, hw⟩ := exists_weylAction_eq_of_lenSq_eq hA hirr (Or.inl ⟨u, i, rfl⟩)
      (Or.inl ⟨u', i', rfl⟩) (by linarith)
    exact ⟨w, by rw [map_nsmul, hw]⟩

end Abstract

section Group

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem exists_map_conj_rootGroup
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (w : (coxeterMatrix D.isFiniteType).Group) :
    ∃ g : K, ∀ γ ∈ D.roots, (D.rootGroup γ).map (MulAut.conj g).toMonoidHom =
      D.rootGroup (weylAction D.isFiniteType w γ) := by
  induction w using (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_induction_left with
  | one =>
    refine ⟨1, fun γ _ => ?_⟩
    have : (MulAut.conj (1 : K)).toMonoidHom = MonoidHom.id K := by ext; simp
    rw [this, Subgroup.map_id, map_one, Module.End.one_apply]
  | mul_simple_left w i ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨n i * g, fun γ hγ => ?_⟩
    have hwγ : weylAction D.isFiniteType w γ ∈ D.roots := weylAction_mem_roots _ w hγ
    have e : (D.rootGroup γ).map (MulAut.conj (n i * g)).toMonoidHom =
        ((D.rootGroup γ).map (MulAut.conj g).toMonoidHom).map (MulAut.conj (n i)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [mul_assoc]
    rw [e, hg γ hγ, map_conj_rootGroup hct i hwγ, weylAction_mul_apply, weylAction_simple]
    rfl

theorem exists_map_conj_rankOne
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (w : (coxeterMatrix D.isFiniteType).Group) :
    ∃ g : K, ∀ γ ∈ D.roots,
      (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom =
        D.rootGroup (weylAction D.isFiniteType w γ) ⊔
          D.rootGroup (-weylAction D.isFiniteType w γ) := by
  obtain ⟨g, hg⟩ := exists_map_conj_rootGroup hct w
  refine ⟨g, fun γ hγ => ?_⟩
  rw [Subgroup.map_sup, hg γ hγ, hg (-γ) (OfCartan.neg_mem_roots D.isFiniteType hγ), map_neg]

theorem exists_map_conj_rankOne_of_isLongest
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hirr : IsIrreducible D.cartan)
    (hD : ∀ i ∈ D.divisible, ∀ j,
      symmetrizer D.isFiniteType j < 4 * symmetrizer D.isFiniteType i)
    {γ γ' : Fin D.rank → ℤ} (hγ : IsLongestRoot D γ) (hγ' : IsLongestRoot D γ') :
    ∃ g : K, (D.rootGroup γ).map (MulAut.conj g).toMonoidHom = D.rootGroup γ' ∧
      (D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom = D.rootGroup (-γ') := by
  obtain ⟨w, hw⟩ := exists_weylAction_eq_of_isLongest D.isFiniteType hirr hD hγ hγ'
  obtain ⟨g, hg⟩ := exists_map_conj_rootGroup hct w
  refine ⟨g, ?_, ?_⟩
  · rw [hg γ hγ.mem, hw]
  · rw [hg (-γ) (OfCartan.neg_mem_roots D.isFiniteType hγ.mem), map_neg, hw]

theorem exists_conj_of_isLongest
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hirr : IsIrreducible D.cartan)
    (hD : ∀ i ∈ D.divisible, ∀ j,
      symmetrizer D.isFiniteType j < 4 * symmetrizer D.isFiniteType i)
    {γ γ' : Fin D.rank → ℤ} (hγ : IsLongestRoot D γ) (hγ' : IsLongestRoot D γ') :
    ∃ g : K, (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom =
      D.rootGroup γ' ⊔ D.rootGroup (-γ') := by
  obtain ⟨g, h1, h2⟩ := exists_map_conj_rankOne_of_isLongest hct hirr hD hγ hγ'
  exact ⟨g, by rw [Subgroup.map_sup, h1, h2]⟩

theorem exists_map_conj_rankOne_of_lenSq_eq
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hirr : IsIrreducible D.cartan) {γ γ' : Fin D.rank → ℤ}
    (hγ : γ ∈ roots D.isFiniteType ∅) (hγ' : γ' ∈ roots D.isFiniteType ∅)
    (h : lenSq D.isFiniteType γ = lenSq D.isFiniteType γ') :
    ∃ g : K, (D.rootGroup γ).map (MulAut.conj g).toMonoidHom = D.rootGroup γ' ∧
      (D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom = D.rootGroup (-γ') := by
  have hroots : ∀ x ∈ roots D.isFiniteType ∅, x ∈ D.roots := fun x hx =>
    roots_empty_subset D.isFiniteType D.divisible hx
  obtain ⟨w, hw⟩ := exists_weylAction_eq_of_lenSq_eq D.isFiniteType hirr hγ hγ' h
  obtain ⟨g, hg⟩ := exists_map_conj_rootGroup hct w
  refine ⟨g, ?_, ?_⟩
  · rw [hg γ (hroots γ hγ), hw]
  · rw [hg (-γ) (OfCartan.neg_mem_roots D.isFiniteType (hroots γ hγ)), map_neg, hw]

end Group

end CFSG.ClassicalInvolution.ModelFacts
