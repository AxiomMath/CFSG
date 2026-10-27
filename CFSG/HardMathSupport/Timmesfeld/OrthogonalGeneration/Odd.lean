module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Commutator
public import CFSG.ClassicalGroups.Orthogonal.Lines

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {K V : Type*} [Field K] [IsF2 K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  [FiniteDimensional K V]

theorem sq_mem_elementaryGroup (hQ : (polarBilin Q).Nondegenerate) (hd : 4 ≤ finrank K V)
    (hE : 5 ≤ finrank K V ∨
      ¬ ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    g * g ∈ elementaryGroup Q := by
  have hcomm := commutator_orthogonalGroup_le_elementaryGroup hQ hd hE
  rw [orthogonalGroup_eq_closure_reflect' hQ (by omega) hE] at hg
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨v, rfl⟩ := hs
    rw [reflect_mul_self]
    exact one_mem _
  | one => rw [mul_one]; exact one_mem _
  | mul a b ha hb iha ihb =>
    have hgen := orthogonalGroup_eq_closure_reflect' hQ (by omega) hE
    have haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hgen ▸ ha
    have hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hgen ▸ hb
    have hc : ⁅a⁻¹, b⁆ ∈ elementaryGroup Q :=
      hcomm (Subgroup.commutator_mem_commutator (inv_mem haO) hbO)
    have : a * b * (a * b) = (a * a) * ⁅a⁻¹, b⁆ * (b * b) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact mul_mem (mul_mem iha hc) ihb
  | inv a ha iha =>
    have : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [this]
    exact inv_mem iha

theorem mem_elementaryGroup_of_pow_eq_one_of_odd (hQ : (polarBilin Q).Nondegenerate)
    (hd : 4 ≤ finrank K V)
    (hE : 5 ≤ finrank K V ∨
      ¬ ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {N : ℕ} (hN : Odd N)
    (hgN : g ^ N = 1) : g ∈ elementaryGroup Q := by
  obtain ⟨k, rfl⟩ := hN
  have hsq := sq_mem_elementaryGroup hQ hd hE hg
  have h1 : g = ((g * g) ^ k)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_two, ← pow_mul, ← pow_succ']
    exact hgN
  rw [h1]
  exact inv_mem (pow_mem hsq k)

theorem exists_smul_of_fixed_by_rootGroup (hQ : (polarBilin Q).Nondegenerate)
    (hd : 3 ≤ finrank K V) {u x : V} (hu : Q u = 0) (hu0 : u ≠ 0)
    (hfix : ∀ w, polar Q u w = 0 → eichler Q u w x = x) : ∃ c : K, x = c • u := by
  have key : ∀ w, polar Q u w = 0 →
      polar Q x u • w = (polar Q x w + Q w * polar Q x u) • u := fun w hw => by
    have := hfix w hw
    rw [eichler_apply hu hw] at this
    linear_combination (norm := module) this
  rcases IsF2.eq_zero_or_one (polar Q x u) with h0 | h1
  · refine exists_smul_of_forall_polar_eq_zero hQ fun w hw => ?_
    have := key w hw
    rw [h0, zero_smul, mul_zero, add_zero] at this
    rcases eq_or_ne (polar Q x w) 0 with h | h
    · exact h
    · exact absurd (smul_eq_zero.mp this.symm) (not_or.mpr ⟨h, hu0⟩)
  · exfalso
    set f := polarBilin Q u
    have hker : LinearMap.ker f ≤ Submodule.span K {u} := by
      intro w hw
      have hw' : polar Q u w = 0 := by simpa [f, polarBilin_apply_apply] using hw
      have := key w hw'
      rw [h1, one_smul] at this
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    have h1' := Submodule.finrank_mono hker
    rw [finrank_span_singleton hu0] at h1'
    have h2 := LinearMap.finrank_range_add_finrank_ker f
    have h3 : finrank K (LinearMap.range f) ≤ 1 :=
      (Submodule.finrank_le _).trans (by simp)
    omega

theorem exists_orth_hypPairs (hQ : (polarBilin Q).Nondegenerate) (hd : 6 ≤ finrank K V) :
    ∃ P P' : HypPair Q, P.Orth P' := by
  obtain ⟨x₀, hx₀, hQx₀⟩ := exists_ne_zero_map_eq_zero' (Q := Q) (by omega)
  obtain ⟨P, -⟩ := exists_hypPair hQ hQx₀ hx₀
  set W := P.perp with hW
  have hWnd : PolarNondegOn Q W := P.polarNondegOn_perp hQ
  have hWdim : 4 ≤ finrank K W := by
    have hWeq : W = LinearMap.ker ((polarBilin Q P.e).prod (polarBilin Q P.f)) := by
      ext x
      simp [hW, HypPair.mem_perp]
    have h2 := LinearMap.finrank_range_add_finrank_ker ((polarBilin Q P.e).prod (polarBilin Q P.f))
    have h3 : finrank K (LinearMap.range ((polarBilin Q P.e).prod (polarBilin Q P.f))) ≤ 2 :=
      (Submodule.finrank_le _).trans (by simp)
    rw [hWeq]
    omega
  obtain ⟨x, hx0, hQx⟩ := exists_ne_zero_map_eq_zero' (Q := Q.restrict W) (by omega)
  have hxW : (x : V) ∈ W := x.2
  have hx0' : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hQx' : Q x = 0 := hQx
  obtain ⟨y, hyW, hxy⟩ := hWnd.exists_polar_ne_zero hxW hx0'
  have hxy1 : polar Q x y = 1 := by
    rcases IsF2.eq_zero_or_one (polar Q x y) with h | h
    · exact absurd h hxy
    · exact h
  refine ⟨P, HypPair.ofPolarEqOne hQx' hxy1, ?_⟩
  have hf : (HypPair.ofPolarEqOne hQx' hxy1).f ∈ W := by
    rw [HypPair.ofPolarEqOne_f]
    exact Submodule.sub_mem _ hyW (Submodule.smul_mem _ _ hxW)
  have h1 := HypPair.mem_perp.mp hxW
  have h2 := HypPair.mem_perp.mp hf
  exact ⟨h1.1, h2.1, h1.2, h2.2⟩

theorem eq_one_of_commute_elementaryGroup (hQ : (polarBilin Q).Nondegenerate)
    (hd : 6 ≤ finrank K V) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : ∀ x ∈ elementaryGroup Q, g * x = x * g) : g = 1 := by
  obtain ⟨P, P', hPP'⟩ := exists_orth_hypPairs hQ hd
  have hfix : ∀ v, v ≠ 0 → Q v = 0 → ∃ c : K, g v = c • v := by
    intro u hu0 hu
    refine exists_smul_of_fixed_by_rootGroup hQ (by omega) hu hu0 fun w hw => ?_
    have h1 := hc (eichler Q u w) (eichler_mem_elementaryGroup Q u w)
    have h2 := congrArg (fun z => z u) h1
    simp only [LinearEquiv.mul_apply, eichler_apply_self] at h2
    exact h2.symm
  have hsc := mem_scalars_of_forall_singular hPP' hg hfix
  obtain ⟨c, hcs⟩ := mem_scalars.mp hsc
  have hc1 : c = 1 := by
    rcases IsF2.eq_zero_or_one c with h | h
    · exfalso
      have := hcs P.e
      rw [h, zero_smul, LinearEquiv.map_eq_zero_iff] at this
      exact P.e_ne_zero this
    · exact h
  refine LinearEquiv.ext fun v => ?_
  rw [hcs v, hc1, one_smul]
  rfl

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
