module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassN
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open Module Submodule
  CFSG.LocalAnalysis.ComponentInitial

section
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

@[expose] def i28_14_N_OG (Q : QuadraticForm (ZMod 2) U) :
    Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U) :=
  (TauCeti.QuadraticMap.orthogonalGroup Q).comap
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).toMonoidHom

theorem i28_14_N_mem_OG {Q : QuadraticForm (ZMod 2) U}
    {g : LinearMap.GeneralLinearGroup (ZMod 2) U} :
    g ∈ i28_14_N_OG Q ↔ ∀ x, Q ((g : U →ₗ[ZMod 2] U) x) = Q x := by
  unfold i28_14_N_OG
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  exact Iff.rfl

theorem i28_14_N_Q_add_smul (Q : QuadraticForm (ZMod 2) U) (x y : U) (c : ZMod 2) :
    Q (x + c • y) = Q x + c * Q y + c * QuadraticMap.polar Q x y := by
  rw [QuadraticMap.map_add Q x (c • y), QuadraticMap.map_smul, QuadraticMap.polar_smul_right, smul_eq_mul,
    smul_eq_mul]
  generalize c = d
  generalize Q x = α
  generalize Q y = β
  generalize QuadraticMap.polar Q x y = γ
  revert d α β γ
  decide

theorem i28_14_N_Q_add (Q : QuadraticForm (ZMod 2) U) (x y : U) :
    Q (x + y) = Q x + Q y + QuadraticMap.polar Q x y := by
  have := i28_14_N_Q_add_smul Q x y 1
  rwa [one_smul, one_mul, one_mul] at this

theorem i28_14_N_polar_self (Q : QuadraticForm (ZMod 2) U) (x : U) :
    QuadraticMap.polar Q x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul]
  exact zmod2_scalar_add_self _

theorem i28_14_N_orth_tv_mem {Q : QuadraticForm (ZMod 2) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {φ : Dual (ZMod 2) U} {a : U}
    (h : φ a = 0) (hφ : φ ≠ 0) (ha : a ≠ 0) (hmem : tv φ a h ∈ i28_14_N_OG Q) :
    QuadraticMap.polarBilin Q a = φ ∧ Q a = 1 := by
  obtain ⟨x₀, hx₀⟩ := exists_apply_eq_one hφ
  have hP : ∀ x, φ x * (Q a + QuadraticMap.polar Q x a) = 0 := by
    intro x
    have e := (i28_14_N_mem_OG.mp hmem) x
    rw [tv_apply, i28_14_N_Q_add_smul] at e
    generalize φ x = c at e ⊢
    generalize Q a = α at e ⊢
    generalize QuadraticMap.polar Q x a = β at e ⊢
    generalize Q x = γ at e ⊢
    revert c α β γ
    decide
  have h1 : QuadraticMap.polar Q x₀ a = Q a := by
    have := hP x₀
    rw [hx₀, one_mul] at this
    generalize Q a = α at this ⊢
    generalize QuadraticMap.polar Q x₀ a = β at this ⊢
    revert α β
    decide
  have hy : ∀ y, QuadraticMap.polar Q a y = φ y * Q a := by
    intro y
    rw [QuadraticMap.polar_comm]
    rcases zmod2_eq_zero_or_one (φ y) with h0 | h0
    · rw [h0, zero_mul]
      have hs : φ (x₀ + y) = 1 := by rw [map_add, hx₀, h0, add_zero]
      have h2 := hP (x₀ + y)
      rw [hs, one_mul, QuadraticMap.polar_add_left, h1] at h2
      generalize Q a = α at h2 ⊢
      generalize QuadraticMap.polar Q y a = β at h2 ⊢
      revert α β
      decide
    · have h2 := hP y
      rw [h0, one_mul] at h2
      rw [h0, one_mul]
      generalize Q a = α at h2 ⊢
      generalize QuadraticMap.polar Q y a = β at h2 ⊢
      revert α β
      decide
  have hc : Q a = 1 := by
    rcases zmod2_eq_zero_or_one (Q a) with h0 | h0
    · exfalso
      refine ha (hQ.1 a fun y => ?_)
      rw [QuadraticMap.polarBilin_apply_apply, hy y, h0, mul_zero]
    · exact h0
  refine ⟨LinearMap.ext fun y => ?_, hc⟩
  rw [QuadraticMap.polarBilin_apply_apply, hy y, hc, mul_one]

theorem i28_14_N_orth_reflection_mem (Q : QuadraticForm (ZMod 2) U) {a : U} (ha : Q a = 1) :
    ∃ h : QuadraticMap.polarBilin Q a a = 0, tv (QuadraticMap.polarBilin Q a) a h ∈ i28_14_N_OG Q := by
  have h : QuadraticMap.polarBilin Q a a = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply]
    exact i28_14_N_polar_self Q a
  refine ⟨h, i28_14_N_mem_OG.mpr fun x => ?_⟩
  rw [tv_apply, i28_14_N_Q_add_smul, QuadraticMap.polarBilin_apply_apply, ha,
    QuadraticMap.polar_comm Q a x]
  generalize QuadraticMap.polar Q x a = γ
  generalize Q x = α
  revert α γ
  decide

theorem i28_14_N_orth_key {Q : QuadraticForm (ZMod 2) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {g : LinearMap.GeneralLinearGroup (ZMod 2) U}
    (hg : ∀ x ∈ i28_14_N_OG Q, g * x * g⁻¹ ∈ i28_14_N_OG Q) {v : U} (hv : Q v = 1) :
    Q ((g : U →ₗ[ZMod 2] U) v) = 1 ∧ ∀ w, QuadraticMap.polar Q ((g : U →ₗ[ZMod 2] U) v)
      ((g : U →ₗ[ZMod 2] U) w) = QuadraticMap.polar Q v w := by
  obtain ⟨h0, hmem⟩ := i28_14_N_orth_reflection_mem Q hv
  have hv0 : v ≠ 0 := fun h => by
    rw [h, QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨h', he⟩ := i28_14_N_conj g (QuadraticMap.polarBilin Q v) v h0
  have ht := hg _ hmem
  rw [he] at ht
  have hne : QuadraticMap.polarBilin Q v ≠ 0 := fun h => hv0 (hQ.1 v fun y => by rw [h]; rfl)
  obtain ⟨hB, hQ1⟩ := i28_14_N_orth_tv_mem hQ h' (i28_14_N_dual_comp_ne_zero g hne)
    (i28_14_N_apply_ne_zero g hv0) ht
  refine ⟨hQ1, fun w => ?_⟩
  have := LinearMap.congr_fun hB ((g : U →ₗ[ZMod 2] U) w)
  simp only [QuadraticMap.polarBilin_apply_apply, LinearMap.comp_apply,
    i28_14_N_inv_apply] at this
  exact this

theorem i28_14_N_orth {Q : QuadraticForm (ZMod 2) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hirr : IsTvIrred (i28_14_N_OG Q))
    {g : LinearMap.GeneralLinearGroup (ZMod 2) U}
    (hg : ∀ x ∈ i28_14_N_OG Q, g * x * g⁻¹ ∈ i28_14_N_OG Q) : g ∈ i28_14_N_OG Q := by
  obtain ⟨⟨S, ⟨t, ht⟩, hS, hG⟩, hirr2⟩ := hirr
  have htG : t ∈ i28_14_N_OG Q := hG ▸ Subgroup.subset_closure ht
  obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff t).mp (hS t ht)
  have ha1 : Q a = 1 := (i28_14_N_orth_tv_mem hQ h hφ ha htG).2
  have hinv : ∀ k ∈ i28_14_N_OG Q, ∀ w ∈ span (ZMod 2) {v : U | Q v = 1},
      (k : U →ₗ[ZMod 2] U) w ∈ span (ZMod 2) {v : U | Q v = 1} := by
    intro k hk w hw
    induction hw using Submodule.span_induction with
    | mem b hb =>
      refine subset_span ?_
      change Q _ = 1
      rw [i28_14_N_mem_OG.mp hk]
      exact hb
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact smul_mem _ c hx
  have hW : span (ZMod 2) {v : U | Q v = 1} = ⊤ := by
    rcases hirr2 _ hinv with h0 | h0
    · exfalso
      have : a ∈ span (ZMod 2) {v : U | Q v = 1} := subset_span ha1
      rw [h0, mem_bot] at this
      exact ha this
    · exact h0
  have key := fun {v : U} (hv : Q v = 1) => i28_14_N_orth_key hQ hg hv
  have hB : ∀ x y, QuadraticMap.polar Q ((g : U →ₗ[ZMod 2] U) x) ((g : U →ₗ[ZMod 2] U) y) =
      QuadraticMap.polar Q x y := by
    intro x y
    have hx : x ∈ span (ZMod 2) {v : U | Q v = 1} := hW ▸ mem_top
    induction hx using Submodule.span_induction with
    | mem v hv => exact (key hv).2 y
    | zero =>
      rw [map_zero, QuadraticMap.polar_zero_left, QuadraticMap.polar_zero_left]
    | add x x' _ _ h1 h2 =>
      rw [map_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_left, h1, h2]
    | smul c x _ h1 =>
      rw [map_smul, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, h1]
  refine i28_14_N_mem_OG.mpr fun x => ?_
  have hx : x ∈ span (ZMod 2) {v : U | Q v = 1} := hW ▸ mem_top
  induction hx using Submodule.span_induction with
  | mem v hv => rw [(key hv).1, hv]
  | zero => rw [map_zero, QuadraticMap.map_zero]
  | add x y _ _ h1 h2 =>
    rw [map_add, i28_14_N_Q_add, i28_14_N_Q_add, h1, h2, hB]
  | smul c x _ h1 =>
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul, map_zero, QuadraticMap.map_zero]
    · rw [one_smul]
      exact h1

end

section
variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

set_option linter.unusedSectionVars false in
theorem tvN_orth {Q : QuadraticForm (ZMod 2) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hirr : IsTvIrred ((TauCeti.QuadraticMap.orthogonalGroup Q).comap
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).toMonoidHom))
    {g : LinearMap.GeneralLinearGroup (ZMod 2) U}
    (hg : ∀ x ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).comap
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).toMonoidHom,
        g * x * g⁻¹ ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).comap
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).toMonoidHom) :
    g ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).comap
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).toMonoidHom :=
  i28_14_N_orth hQ hirr hg

end

end CFSG.HardMathSupport.Solomon.Coordinator
