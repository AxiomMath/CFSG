module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 CFSG.HardMathSupport.GuralnickMalle QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

theorem movedSpace_le_orthogonal_or_inf_ne_bot_of_commute {x y : V ≃ₗ[K] V}
    (hx : IsLongRootElement Qf x) (hy : IsLongRootElement Qf y) (hcomm : x * y = y * x) :
    movedSpace x ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace y) ∨
      movedSpace x ⊓ movedSpace y ≠ ⊥ := by
  by_cases h : Disjoint (movedSpace x) (movedSpace y)
  · exact Or.inl (movedSpace_le_orthogonal_of_commute hy hx hcomm.symm h.symm)
  · exact Or.inr (fun h' => h (disjoint_iff.mpr h'))

omit [CharP K 2] in
theorem exists_pair_of_mem_of_finrank_eq_two {A : Submodule K V} (hA : finrank K A = 2) {r : V}
    (hr : r ∈ A) (hr0 : r ≠ 0) :
    ∃ b ∈ A, LinearIndependent K ![r, b] ∧ Submodule.span K ({r, b} : Set V) = A := by
  obtain ⟨b, hbA, hb⟩ : ∃ b ∈ A, b ∉ Submodule.span K {r} := by
    by_contra hcon
    push Not at hcon
    have hmono := Submodule.finrank_mono (show A ≤ Submodule.span K {r} from hcon)
    rw [finrank_span_singleton hr0, hA] at hmono
    omega
  have hli : LinearIndependent K ![r, b] := by
    rw [LinearIndependent.pair_iff' hr0]
    intro a ha
    exact hb (ha ▸ Submodule.smul_mem _ a (Submodule.mem_span_singleton_self r))
  exact ⟨b, hbA, hli, span_pair_eq_of_finrank_eq_two hA hr hbA hli⟩

omit [CharP K 2] in
private theorem qf_add_three_smul (a b c : K) (p q s : V) :
    Qf (a • p + b • q + c • s) = a * a * Qf p + b * b * Qf q + c * c * Qf s
      + a * b * polar Qf p q + a * c * polar Qf p s + b * c * polar Qf q s := by
  simp only [QuadraticMap.map_add Qf, QuadraticMap.map_smul Qf,
    QuadraticMap.polar_add_left Qf, QuadraticMap.polar_smul_left Qf,
    QuadraticMap.polar_smul_right Qf, smul_eq_mul]
  ring

theorem exists_qf_ne_zero_of_mem_movedSpace_mul
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s')
    (h1 : finrank K ↥(movedSpace s ⊓ movedSpace s') = 1)
    (h2 : ¬ movedSpace s ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s')) :
    ∃ w ∈ movedSpace (s * s'), Qf w ≠ 0 := by
  have hA2 := hs.finrank_movedSpace hnd
  have hA'2 := hs'.finrank_movedSpace hnd
  have hAs : ∀ w ∈ movedSpace s, Qf w = 0 := fun w hw => hs.qf_eq_zero_of_mem_movedSpace hw
  have hA's : ∀ w ∈ movedSpace s', Qf w = 0 := fun w hw => hs'.qf_eq_zero_of_mem_movedSpace hw
  have hne : movedSpace s ⊓ movedSpace s' ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hrA, hrA'⟩ := Submodule.mem_inf.mp hr
  obtain ⟨b, hbA, hli, hspan⟩ := exists_pair_of_mem_of_finrank_eq_two hA2 hrA hr0
  obtain ⟨b', hb'A', hli', hspan'⟩ := exists_pair_of_mem_of_finrank_eq_two hA'2 hrA' hr0
  obtain ⟨c, hc0, hc⟩ := exists_siegel_scalar hnd hs.isometry hli hspan hAs
  obtain ⟨c', hc'0, hc'⟩ := exists_siegel_scalar hnd hs'.isometry hli' hspan' hA's
  have hQr : Qf r = 0 := hAs r hrA
  have hQb : Qf b = 0 := hAs b hbA
  have hQb' : Qf b' = 0 := hA's b' hb'A'
  have hbr : polar Qf b r = 0 := polar_eq_zero_of_totallySingular hAs hbA hrA
  have hrb : polar Qf r b = 0 := polar_eq_zero_of_totallySingular hAs hrA hbA
  have hb'r : polar Qf b' r = 0 := polar_eq_zero_of_totallySingular hA's hb'A' hrA'
  have hrb' : polar Qf r b' = 0 := polar_eq_zero_of_totallySingular hA's hrA' hb'A'
  have hbb' : polar Qf b b' ≠ 0 := by
    intro h0
    apply h2
    intro u hu
    rw [mem_orthogonal_iff_polar]
    intro y hy
    rw [← hspan] at hu
    rw [← hspan'] at hy
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
    obtain ⟨α', β', rfl⟩ := Submodule.mem_span_pair.mp hy
    have h0' : polar Qf b' b = 0 := by rw [polar_comm]; exact h0
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
      polar_self_eq_zero, hrb, hb'r, h0', smul_zero, add_zero]
  obtain ⟨x, hxr, hxb⟩ := exists_polar_pair hnd hli 1 0
  refine ⟨(s * s') x - x, sub_mem_movedSpace (s * s') x, ?_⟩
  have hy : s' x = x + c' • b' + (c' * polar Qf x b') • r := by
    rw [hc' x, hxr]
    module
  have hy1 : polar Qf (s' x) r = 1 := by
    rw [hy]
    simp only [polar_add_left, polar_smul_left, hxr, hb'r, polar_self_eq_zero, smul_eq_mul,
      mul_zero, add_zero]
  have hy2 : polar Qf (s' x) b = c' * polar Qf b' b := by
    rw [hy]
    simp only [polar_add_left, polar_smul_left, hxb, hrb, smul_eq_mul, mul_zero, add_zero,
      zero_add]
  have hw : (s * s') x - x = c • b + c' • b' +
      (c' * polar Qf x b' + c * (c' * polar Qf b' b)) • r := by
    rw [LinearEquiv.mul_apply, hc (s' x), hy1, hy2]
    conv_lhs => rw [hy]
    module
  rw [hw, qf_add_three_smul, hQb, hQb', hQr, hbr, hb'r]
  simp [hc0, hc'0, hbb']

theorem not_isLongRootElement_mul
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s')
    (h1 : finrank K ↥(movedSpace s ⊓ movedSpace s') = 1)
    (h2 : ¬ movedSpace s ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s')) :
    ¬ IsLongRootElement Qf (s * s') := by
  intro hss'
  obtain ⟨w, hw, hQw⟩ := exists_qf_ne_zero_of_mem_movedSpace_mul hnd hs hs' h1 h2
  exact hQw (hss'.qf_eq_zero_of_mem_movedSpace hw)

theorem sub_mem_span_singleton_of_polar_eq_zero
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) {r : V} (hr : r ∈ movedSpace s) (hr0 : r ≠ 0) {x : V}
    (hx : polar Qf x r = 0) : s x - x ∈ Submodule.span K ({r} : Set V) := by
  obtain ⟨b, -, hli, hspan⟩ :=
    exists_pair_of_mem_of_finrank_eq_two (hs.finrank_movedSpace hnd) hr hr0
  obtain ⟨c, -, hc⟩ := exists_siegel_scalar hnd hs.isometry hli hspan
    (fun w hw => hs.qf_eq_zero_of_mem_movedSpace hw)
  rw [hc x, hx]
  refine Submodule.mem_span_singleton.mpr ⟨c * polar Qf x b, ?_⟩
  module

theorem pow_four_eq_one_of_inf_orthogonal_ne_bot
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s')
    (h : movedSpace s ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s') ≠ ⊥) :
    (s * s') ^ 4 = 1 := by
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨hrA, hrA'⟩ := Submodule.mem_inf.mp hr
  rw [mem_orthogonal_iff_polar] at hrA'
  have hAs : ∀ w ∈ movedSpace s, Qf w = 0 := fun w hw => hs.qf_eq_zero_of_mem_movedSpace hw
  have hsr : s r = r := hs.apply_eq_self_of_mem_movedSpace hrA
  have hs'r : s' r = r := by
    have hmem : r ∈ LinearMap.ker ((s' : V →ₗ[K] V) - 1) := by
      rw [ker_sub_one_eq_orthogonal_movedSpace hnd hs'.isometry, mem_orthogonal_iff_polar]
      exact hrA'
    simpa [sub_eq_zero] using hmem
  have h1 : ∀ x, polar Qf (s x - x) r = 0 := fun x => by
    rw [polar_comm]
    exact polar_eq_zero_of_totallySingular hAs hrA (sub_mem_movedSpace s x)
  have h2 : ∀ x, polar Qf (s' x - x) r = 0 := fun x => hrA' _ (sub_mem_movedSpace s' x)
  have h3 : ∀ x, polar Qf x r = 0 → s x - x ∈ Submodule.span K ({r} : Set V) := fun x hx =>
    sub_mem_span_singleton_of_polar_eq_zero hnd hs hrA hr0 hx
  have h4 : ∀ x, s' (s' x - x) = s' x - x := fun x =>
    hs'.apply_eq_self_of_mem_movedSpace (sub_mem_movedSpace s' x)
  set g : V ≃ₗ[K] V := s * s' with hg
  let n : V →ₗ[K] V := (g : V →ₗ[K] V) - 1
  have hn : ∀ x, n x = g x - x := fun x => by simp [n]
  have hgx : ∀ x, g x = s (s' x) := fun x => rfl
  have hnr : n r = 0 := by rw [hn, hgx, hs'r, hsr, sub_self]
  have hn1 : ∀ x, polar Qf (n x) r = 0 := fun x => by
    have e : n x = (s (s' x) - s' x) + (s' x - x) := by rw [hn, hgx]; abel
    rw [e, polar_add_left, h1, h2, add_zero]
  have hn2 : ∀ x, polar Qf x r = 0 → n (n x) ∈ Submodule.span K ({r} : Set V) := by
    intro x hx
    have hx' : polar Qf (s' x) r = 0 := by
      have e : s' x = (s' x - x) + x := by abel
      rw [e, polar_add_left, h2, hx, add_zero]
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (h3 (s' x) hx')
    have hnx : n x = k • r + (s' x - x) := by
      have e : s (s' x) - x = (s (s' x) - s' x) + (s' x - x) := by abel
      rw [hn, hgx, e, ← hk]
    have e2 : n (n x) = n (s' x - x) := by
      rw [hnx, map_add, map_smul, hnr, smul_zero, zero_add]
    rw [e2, hn, hgx, h4]
    exact h3 _ (h2 x)
  have hn3 : ∀ x, polar Qf x r = 0 → n (n (n x)) = 0 := by
    intro x hx
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (hn2 x hx)
    rw [← hk, map_smul, hnr, smul_zero]
  have hn4 : ∀ x, n (n (n (n x))) = 0 := fun x => hn3 (n x) (hn1 x)
  have e2 : ∀ z : V, z + z = 0 := fun z => by rw [← two_smul K z, CharTwo.two_eq_zero, zero_smul]
  have hnn : ∀ y, n (n y) = g (g y) + y := by
    intro y
    rw [hn (n y), hn y, map_sub]
    linear_combination (norm := module) (-1 : K) • e2 (g y)
  have hg4 : ∀ x, g (g (g (g x))) = x := by
    intro x
    have h4x := hn4 x
    rw [hnn (n (n x)), hnn x] at h4x
    simp only [map_add] at h4x
    linear_combination (norm := module) h4x - e2 (g (g x)) - e2 x
  apply LinearEquiv.ext
  intro x
  simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq]
  exact hg4 x

theorem pow_four_swap_eq_one_iff {s s' : V ≃ₗ[K] V} (hs : IsLongRootElement Qf s)
    (hs' : IsLongRootElement Qf s') : (s' * s) ^ 4 = 1 ↔ (s * s') ^ 4 = 1 := by
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs.mul_self
  have hs1' : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'.mul_self
  have e : s' * s = (s * s')⁻¹ := by rw [mul_inv_rev, hs1, hs1']
  rw [e, inv_pow, inv_eq_one]

theorem inf_orthogonal_eq_bot_of_pow_four_ne_one
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s') (h4 : (s * s') ^ 4 ≠ 1) :
    movedSpace s ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s') = ⊥ := by
  by_contra h
  exact h4 (pow_four_eq_one_of_inf_orthogonal_ne_bot hnd hs hs' h)

theorem corollary_one_three
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s') (h4 : (s * s') ^ 4 ≠ 1) :
    movedSpace s ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s') = ⊥ ∧
    movedSpace s' ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s) = ⊥ ∧
    Disjoint (movedSpace s) (movedSpace s') ∧
    finrank K ↥(movedSpace s ⊔ movedSpace s') = 4 ∧
    ∀ x ∈ movedSpace s ⊔ movedSpace s',
      (∀ y ∈ movedSpace s ⊔ movedSpace s', polar Qf x y = 0) → x = 0 := by
  have hAs : ∀ w ∈ movedSpace s, Qf w = 0 := fun w hw => hs.qf_eq_zero_of_mem_movedSpace hw
  have hA's : ∀ w ∈ movedSpace s', Qf w = 0 := fun w hw => hs'.qf_eq_zero_of_mem_movedSpace hw
  have h1 := inf_orthogonal_eq_bot_of_pow_four_ne_one hnd hs hs' h4
  have h2 : movedSpace s' ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s) = ⊥ :=
    inf_orthogonal_eq_bot_of_pow_four_ne_one hnd hs' hs
      (fun h => h4 ((pow_four_swap_eq_one_iff hs hs').mp h))
  have h3 : movedSpace s ⊓ movedSpace s' = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rw [← h1]
    exact inf_le_inf_left _ (le_orthogonal_of_totallySingular hA's)
  refine ⟨h1, h2, disjoint_iff.mpr h3, ?_, ?_⟩
  · have hA2 := hs.finrank_movedSpace hnd
    have hA'2 := hs'.finrank_movedSpace hnd
    have : Module.Finite K (movedSpace s) := Module.finite_of_finrank_pos (by omega)
    have : Module.Finite K (movedSpace s') := Module.finite_of_finrank_pos (by omega)
    have h := Submodule.finrank_sup_add_finrank_inf_eq (movedSpace s) (movedSpace s')
    rw [h3, finrank_bot, hA2, hA'2] at h
    omega
  · intro x hx hx0
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hx
    have hu0 : u = 0 := by
      have hmem : u ∈ movedSpace s ⊓
          LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s') := by
        refine Submodule.mem_inf.mpr ⟨hu, mem_orthogonal_iff_polar.mpr fun y hy => ?_⟩
        have h := hx0 y (Submodule.mem_sup_right hy)
        rw [polar_add_left, polar_eq_zero_of_totallySingular hA's hu' hy, add_zero] at h
        rw [polar_comm]
        exact h
      rw [h1, Submodule.mem_bot] at hmem
      exact hmem
    have hu'0 : u' = 0 := by
      have hmem : u' ∈ movedSpace s' ⊓
          LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s) := by
        refine Submodule.mem_inf.mpr ⟨hu', mem_orthogonal_iff_polar.mpr fun y hy => ?_⟩
        have h := hx0 y (Submodule.mem_sup_left hy)
        rw [polar_add_left, polar_eq_zero_of_totallySingular hAs hu hy, zero_add] at h
        rw [polar_comm]
        exact h
      rw [h2, Submodule.mem_bot] at hmem
      exact hmem
    rw [hu0, hu'0, add_zero]

omit [CharP K 2] in
theorem finrank_inf_eq_one_of_finrank_two {A A' : Submodule K V} (hA : finrank K A = 2)
    (hA' : finrank K A' = 2) (hne : A ≠ A') (hbot : A ⊓ A' ≠ ⊥) :
    finrank K ↥(A ⊓ A') = 1 := by
  have : FiniteDimensional K A := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional K A' := Module.finite_of_finrank_pos (by omega)
  have hle : finrank K ↥(A ⊓ A') ≤ 2 := hA ▸ Submodule.finrank_mono inf_le_left
  have hne2 : finrank K ↥(A ⊓ A') ≠ 2 := by
    intro h2
    have hAeq : A ⊓ A' = A := Submodule.eq_of_le_of_finrank_eq inf_le_left (h2.trans hA.symm)
    exact hne (Submodule.eq_of_le_of_finrank_eq (hAeq ▸ inf_le_right) (hA.trans hA'.symm))
  have hne0 : finrank K ↥(A ⊓ A') ≠ 0 := fun h0 => hbot (Submodule.finrank_eq_zero.mp h0)
  omega

theorem movedSpace_le_orthogonal_of_commute_of_isLongRootElement_mul
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s') (hcomm : s * s' = s' * s)
    (hmul : IsLongRootElement Qf (s * s')) :
    movedSpace s ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace s') := by
  rcases movedSpace_le_orthogonal_or_inf_ne_bot_of_commute hs hs' hcomm with h | hne
  · exact h
  by_cases heq : movedSpace s = movedSpace s'
  · rw [← heq]
    exact le_orthogonal_of_totallySingular fun w hw => hs.qf_eq_zero_of_mem_movedSpace hw
  by_contra h2
  exact not_isLongRootElement_mul hnd hs hs'
    (finrank_inf_eq_one_of_finrank_two (hs.finrank_movedSpace hnd) (hs'.finrank_movedSpace hnd)
      heq hne) h2 hmul

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
