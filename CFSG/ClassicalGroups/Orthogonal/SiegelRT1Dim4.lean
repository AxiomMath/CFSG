module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 CFSG.HardMathSupport.GuralnickMalle QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

section Dim4

variable [FiniteDimensional K V]

omit [CharP K 2] in
private theorem finrank_le_sub_finrank_of_totallySingular
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {W : Submodule K V}
    (hW : ∀ w ∈ W, Qf w = 0) : finrank K W ≤ finrank K V - finrank K W := by
  have h := Submodule.finrank_mono (le_orthogonal_of_totallySingular hW)
  rwa [finrank_orthogonal_polar hnd W] at h

omit [CharP K 2] in
theorem two_mul_finrank_le_of_totallySingular
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {W : Submodule K V}
    (hW : ∀ w ∈ W, Qf w = 0) : 2 * finrank K W ≤ finrank K V := by
  have h := finrank_le_sub_finrank_of_totallySingular hnd hW
  omega

omit [CharP K 2] in
private theorem eq_orthogonal_of_totallySingular_of_finrank_four
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) (h4 : finrank K V = 4)
    {W : Submodule K V} (hW : ∀ w ∈ W, Qf w = 0) (hW2 : finrank K W = 2) :
    W = LinearMap.BilinForm.orthogonal (polarBilin Qf) W := by
  have hdim := finrank_orthogonal_polar hnd W
  exact Submodule.eq_of_le_of_finrank_eq (le_orthogonal_of_totallySingular hW) (by omega)

omit [CharP K 2] in
theorem not_le_orthogonal_of_ne_of_finrank_four
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) (h4 : finrank K V = 4)
    {A A' : Submodule K V} (hA2 : finrank K A = 2) (hA's : ∀ w ∈ A', Qf w = 0)
    (hA'2 : finrank K A' = 2) (_hAs : ∀ w ∈ A, Qf w = 0) (hne : A ≠ A') :
    ¬ A ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) A' := by
  intro hAle
  have hA'eq := eq_orthogonal_of_totallySingular_of_finrank_four hnd h4 hA's hA'2
  have hAA' : A ≤ A' := hAle.trans (le_of_eq hA'eq.symm)
  exact hne (Submodule.eq_of_le_of_finrank_eq hAA' (by omega))

omit [CharP K 2] [FiniteDimensional K V] in
private theorem qf_add_three_smul (a b c : K) (p q s : V) :
    Qf (a • p + b • q + c • s) = a * a * Qf p + b * b * Qf q + c * c * Qf s
      + a * b * polar Qf p q + a * c * polar Qf p s + b * c * polar Qf q s := by
  simp only [QuadraticMap.map_add Qf, QuadraticMap.map_smul Qf,
    QuadraticMap.polar_add_left Qf, QuadraticMap.polar_smul_left Qf,
    QuadraticMap.polar_smul_right Qf, smul_eq_mul]
  ring

omit [CharP K 2] [FiniteDimensional K V] in
private theorem polar_eq_zero_of_mem_span_singleton {r y x : V} (hry : polar Qf r y = 0)
    (hx : x ∈ Submodule.span K {r}) : polar Qf x y = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [QuadraticMap.polar_smul_left, hry, smul_zero]

omit [CharP K 2] [FiniteDimensional K V] in
private theorem linearIndependent_pair_of_not_mem_span {r x : V} (hr0 : r ≠ 0)
    (hx : x ∉ Submodule.span K {r}) : LinearIndependent K ![r, x] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  have hrS : g 0 • r ∈ Submodule.span K {r} :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self r)
  have h1 : g 1 = 0 := by
    by_contra h1
    apply hx
    have hy : g 1 • x ∈ Submodule.span K {r} :=
      (Submodule.add_mem_iff_right _ hrS).1 (by rw [hg]; exact Submodule.zero_mem _)
    exact (Submodule.smul_mem_iff _ h1).1 hy
  rw [h1, zero_smul, add_zero] at hg
  have h0 : g 0 = 0 := (smul_eq_zero.1 hg).resolve_right hr0
  intro i
  fin_cases i <;> simp [h0, h1]

omit [CharP K 2] [FiniteDimensional K V] in
private theorem span_pair_le {L : Submodule K V} {r x : V} (hrL : r ∈ L) (hxL : x ∈ L) :
    Submodule.span K (Set.range ![r, x]) ≤ L := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hrL
  · exact hxL

omit [CharP K 2] in
private theorem eq_of_finrank_two_of_mem {L M : Submodule K V} (hL : finrank K L = 2)
    (hM : finrank K M = 2) {r x : V} (hrL : r ∈ L) (hxL : x ∈ L) (hrM : r ∈ M) (hxM : x ∈ M)
    (hr0 : r ≠ 0) (hx : x ∉ Submodule.span K {r}) : L = M := by
  have hli := linearIndependent_pair_of_not_mem_span hr0 hx
  have hrank : finrank K (Submodule.span K (Set.range ![r, x])) = 2 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have e₁ : Submodule.span K (Set.range ![r, x]) = L :=
    Submodule.eq_of_le_of_finrank_eq (span_pair_le hrL hxL) (by rw [hrank, hL])
  have e₂ : Submodule.span K (Set.range ![r, x]) = M :=
    Submodule.eq_of_le_of_finrank_eq (span_pair_le hrM hxM) (by rw [hrank, hM])
  exact e₁.symm.trans e₂

omit [CharP K 2] [FiniteDimensional K V] in
private theorem exists_mem_not_mem_span_singleton_of_finrank_two {L : Submodule K V}
    (hL : finrank K L = 2) {r : V} (hr0 : r ≠ 0) :
    ∃ x ∈ L, x ∉ Submodule.span K {r} := by
  by_contra h
  have hle : L ≤ Submodule.span K {r} := fun x hx => by
    by_contra hx'
    exact h ⟨x, hx, hx'⟩
  have hmono := Submodule.finrank_mono hle
  rw [finrank_span_singleton hr0, hL] at hmono
  omega

omit [CharP K 2] [FiniteDimensional K V] in
private theorem linearIndependent_three_of_not_mem {L : Submodule K V} {r x₁ x₂ : V}
    (hr0 : r ≠ 0) (hrL : r ∈ L) (hx₁L : x₁ ∈ L) (hx₁ : x₁ ∉ Submodule.span K {r})
    (hx₂ : x₂ ∉ L) : LinearIndependent K ![r, x₁, x₂] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hg
  have hA : g 0 • r + g 1 • x₁ ∈ L := L.add_mem (L.smul_mem _ hrL) (L.smul_mem _ hx₁L)
  have h2 : g 2 = 0 := by
    by_contra h2
    apply hx₂
    have hy : g 2 • x₂ ∈ L :=
      (Submodule.add_mem_iff_right L hA).1 (by rw [hg]; exact L.zero_mem)
    exact (Submodule.smul_mem_iff L h2).1 hy
  rw [h2, zero_smul, add_zero] at hg
  have hrS : g 0 • r ∈ Submodule.span K {r} :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self r)
  have h1 : g 1 = 0 := by
    by_contra h1
    apply hx₁
    have hy : g 1 • x₁ ∈ Submodule.span K {r} :=
      (Submodule.add_mem_iff_right _ hrS).1 (by rw [hg]; exact Submodule.zero_mem _)
    exact (Submodule.smul_mem_iff _ h1).1 hy
  rw [h1, zero_smul, add_zero] at hg
  have h0 : g 0 = 0 := (smul_eq_zero.1 hg).resolve_right hr0
  intro i
  fin_cases i <;> simp [h0, h1, h2]

omit [CharP K 2] in
theorem false_of_three_orthogonal_singular
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) (h4 : finrank K V = 4)
    {p q s : V} (hp : Qf p = 0) (hq : Qf q = 0) (hs : Qf s = 0)
    (hpq : polar Qf p q = 0) (hps : polar Qf p s = 0) (hqs : polar Qf q s = 0)
    (hli : LinearIndependent K ![p, q, s]) : False := by
  have hTs : ∀ w ∈ Submodule.span K (Set.range ![p, q, s]), Qf w = 0 := by
    intro w hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [qf_add_three_smul, hp, hq, hs, hpq, hps, hqs]
    ring
  have h := two_mul_finrank_le_of_totallySingular hnd hTs
  rw [finrank_span_eq_card hli, Fintype.card_fin, h4] at h
  omega

private theorem false_of_common_nonzero_vector (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (h4 : finrank K V = 4) {L₁ L₂ L₃ : Submodule K V} (h₁ : finrank K L₁ = 2)
    (h₂ : finrank K L₂ = 2) (h₃ : finrank K L₃ = 2) (s₁ : ∀ w ∈ L₁, Qf w = 0)
    (s₂ : ∀ w ∈ L₂, Qf w = 0) (s₃ : ∀ w ∈ L₃, Qf w = 0) (n₁₂ : L₁ ≠ L₂) (n₁₃ : L₁ ≠ L₃)
    (n₂₃ : L₂ ≠ L₃) {r : V} (hr0 : r ≠ 0) (hrL₁ : r ∈ L₁) (hrL₂ : r ∈ L₂) (hrL₃ : r ∈ L₃) :
    False := by
  obtain ⟨x₁, hx₁L₁, hx₁⟩ := exists_mem_not_mem_span_singleton_of_finrank_two h₁ hr0
  obtain ⟨x₂, hx₂L₂, hx₂⟩ := exists_mem_not_mem_span_singleton_of_finrank_two h₂ hr0
  obtain ⟨x₃, hx₃L₃, hx₃⟩ := exists_mem_not_mem_span_singleton_of_finrank_two h₃ hr0
  have hx₂L₁ : x₂ ∉ L₁ := fun h => n₁₂ (eq_of_finrank_two_of_mem h₁ h₂ hrL₁ h hrL₂ hx₂L₂ hr0 hx₂)
  have hli := linearIndependent_three_of_not_mem hr0 hrL₁ hx₁L₁ hx₁ hx₂L₁
  have hQr : Qf r = 0 := s₁ r hrL₁
  have hQ1 : Qf x₁ = 0 := s₁ x₁ hx₁L₁
  have hQ2 : Qf x₂ = 0 := s₂ x₂ hx₂L₂
  have hQ3 : Qf x₃ = 0 := s₃ x₃ hx₃L₃
  have hr1 : polar Qf r x₁ = 0 := polar_eq_zero_of_totallySingular s₁ hrL₁ hx₁L₁
  have hr2 : polar Qf r x₂ = 0 := polar_eq_zero_of_totallySingular s₂ hrL₂ hx₂L₂
  have hr3 : polar Qf r x₃ = 0 := polar_eq_zero_of_totallySingular s₃ hrL₃ hx₃L₃
  by_cases hP : polar Qf x₁ x₂ = 0
  · exact false_of_three_orthogonal_singular hnd h4 hQr hQ1 hQ2 hr1 hr2 hP hli
  have hO : ∀ y, polar Qf r y = 0 →
      y ∈ LinearMap.BilinForm.orthogonal (polarBilin Qf) (Submodule.span K {r}) :=
    fun y hy => mem_orthogonal_iff_polar.2 fun x hx => polar_eq_zero_of_mem_span_singleton hy hx
  have hle : Submodule.span K (Set.range ![r, x₁, x₂]) ≤
      LinearMap.BilinForm.orthogonal (polarBilin Qf) (Submodule.span K {r}) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hO r (polar_self_eq_zero r)
    · exact hO x₁ hr1
    · exact hO x₂ hr2
  have hA3 : finrank K (Submodule.span K (Set.range ![r, x₁, x₂])) = 3 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hO3 : finrank K
      (LinearMap.BilinForm.orthogonal (polarBilin Qf) (Submodule.span K {r})) = 3 := by
    have h := finrank_orthogonal_polar hnd (Submodule.span K {r})
    rw [finrank_span_singleton hr0, h4] at h
    omega
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hA3, hO3])
  have hx₃O := hO x₃ hr3
  rw [← heq] at hx₃O
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx₃O
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hc
  have hkey : c 1 * c 2 * polar Qf x₁ x₂ = 0 := by
    have h := hQ3
    rw [← hc, qf_add_three_smul, hQr, hQ1, hQ2, hr1, hr2] at h
    linear_combination h
  rcases mul_eq_zero.1 hkey with h12 | hP'
  · rcases mul_eq_zero.1 h12 with hc1 | hc2
    · have hx₃L₂ : x₃ ∈ L₂ := by
        rw [← hc, hc1, zero_smul, add_zero]
        exact L₂.add_mem (L₂.smul_mem _ hrL₂) (L₂.smul_mem _ hx₂L₂)
      exact n₂₃ (eq_of_finrank_two_of_mem h₂ h₃ hrL₂ hx₃L₂ hrL₃ hx₃L₃ hr0 hx₃)
    · have hx₃L₁ : x₃ ∈ L₁ := by
        rw [← hc, hc2, zero_smul, add_zero]
        exact L₁.add_mem (L₁.smul_mem _ hrL₁) (L₁.smul_mem _ hx₁L₁)
      exact n₁₃ (eq_of_finrank_two_of_mem h₁ h₃ hrL₁ hx₃L₁ hrL₃ hx₃L₃ hr0 hx₃)
  · exact hP hP'

omit [CharP K 2] in
private theorem false_of_inf_eq_bot (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (h4 : finrank K V = 4) {L₁ L₂ L₃ : Submodule K V} (s₁ : ∀ w ∈ L₁, Qf w = 0)
    (s₂ : ∀ w ∈ L₂, Qf w = 0) (s₃ : ∀ w ∈ L₃, Qf w = 0) (hS : L₁ ⊓ L₂ ⊓ L₃ = ⊥)
    {p₁₂ p₁₃ p₂₃ : V} (hp₁₂ : p₁₂ ∈ L₁ ⊓ L₂) (hp₁₂0 : p₁₂ ≠ 0) (hp₁₃ : p₁₃ ∈ L₁ ⊓ L₃)
    (hp₁₃0 : p₁₃ ≠ 0) (hp₂₃ : p₂₃ ∈ L₂ ⊓ L₃) (hp₂₃0 : p₂₃ ≠ 0) : False := by
  have hzero : ∀ v : V, v ∈ L₁ → v ∈ L₂ → v ∈ L₃ → v = 0 := by
    intro v h1 h2 h3
    have hv : v ∈ L₁ ⊓ L₂ ⊓ L₃ := Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨h1, h2⟩, h3⟩
    rw [hS, Submodule.mem_bot] at hv
    exact hv
  obtain ⟨h12₁, h12₂⟩ := Submodule.mem_inf.1 hp₁₂
  obtain ⟨h13₁, h13₃⟩ := Submodule.mem_inf.1 hp₁₃
  obtain ⟨h23₂, h23₃⟩ := Submodule.mem_inf.1 hp₂₃
  have hp₂₃L₁ : p₂₃ ∉ L₁ := fun h => hp₂₃0 (hzero p₂₃ h h23₂ h23₃)
  have hp₁₃span : p₁₃ ∉ Submodule.span K {p₁₂} := by
    intro h
    have hsub : Submodule.span K {p₁₂} ≤ L₂ :=
      Submodule.span_le.2 (Set.singleton_subset_iff.2 h12₂)
    exact hp₁₃0 (hzero p₁₃ h13₁ (hsub h) h13₃)
  have hli := linearIndependent_three_of_not_mem hp₁₂0 h12₁ h13₁ hp₁₃span hp₂₃L₁
  exact false_of_three_orthogonal_singular hnd h4 (s₁ _ h12₁) (s₁ _ h13₁) (s₂ _ h23₂)
    (polar_eq_zero_of_totallySingular s₁ h12₁ h13₁)
    (polar_eq_zero_of_totallySingular s₂ h12₂ h23₂)
    (polar_eq_zero_of_totallySingular s₃ h13₃ h23₃) hli

theorem false_of_three_totallySingular_planes_pairwise_meet
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) (h4 : finrank K V = 4)
    {L₁ L₂ L₃ : Submodule K V} (h₁ : finrank K L₁ = 2) (h₂ : finrank K L₂ = 2)
    (h₃ : finrank K L₃ = 2) (s₁ : ∀ w ∈ L₁, Qf w = 0) (s₂ : ∀ w ∈ L₂, Qf w = 0)
    (s₃ : ∀ w ∈ L₃, Qf w = 0) (n₁₂ : L₁ ≠ L₂) (n₁₃ : L₁ ≠ L₃) (n₂₃ : L₂ ≠ L₃)
    (m₁₂ : L₁ ⊓ L₂ ≠ ⊥) (m₁₃ : L₁ ⊓ L₃ ≠ ⊥) (m₂₃ : L₂ ⊓ L₃ ≠ ⊥) : False := by
  by_cases hS : L₁ ⊓ L₂ ⊓ L₃ = ⊥
  · obtain ⟨p₁₂, hp₁₂, hp₁₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot m₁₂
    obtain ⟨p₁₃, hp₁₃, hp₁₃0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot m₁₃
    obtain ⟨p₂₃, hp₂₃, hp₂₃0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot m₂₃
    exact false_of_inf_eq_bot hnd h4 s₁ s₂ s₃ hS hp₁₂ hp₁₂0 hp₁₃ hp₁₃0 hp₂₃ hp₂₃0
  · obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    obtain ⟨hrL₁₂, hrL₃⟩ := Submodule.mem_inf.1 hr
    obtain ⟨hrL₁, hrL₂⟩ := Submodule.mem_inf.1 hrL₁₂
    exact false_of_common_nonzero_vector hnd h4 h₁ h₂ h₃ s₁ s₂ s₃ n₁₂ n₁₃ n₂₃ hr0 hrL₁ hrL₂
      hrL₃

end Dim4

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
