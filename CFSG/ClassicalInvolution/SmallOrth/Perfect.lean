module

public import CFSG.ClassicalInvolution.SmallOrth.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem commutatorElement_eichler_smul {h : V ≃ₗ[K] V}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u v : V} {l : K} (hhu : h u = l • u)
    (hhv : h v = v) (hv : polar Q u v = 0) :
    ⁅h, eichler Q u v⁆ = eichler Q u ((l - 1) • v) := by
  have hlv : polar Q u (l • v) = 0 := by rw [polar_smul_right_eq, hv, mul_zero]
  have hnv : polar Q u (-v) = 0 := by rw [polar_neg_right, hv, neg_zero]
  rw [commutatorElement_def, eichler_conj hh, hhu, hhv, eichler_smul_left, eichler_inv hv,
    eichler_mul hlv hnv, sub_smul, one_smul, sub_eq_add_neg]

variable (P : HypPair Q)

theorem eichler_mem_commutator_of_mem_perp (h2 : (2 : K) ≠ 0) {a : V} (ha : a ∈ P.perp)
    (hc : Q a ≠ 0) {τ : K} (hτ : τ ≠ 0) (hτ2 : τ ^ 2 ≠ 1) {v : V} (hv : v ∈ P.perp) :
    (⟨eichler Q P.e v, eichler_mem_elementaryGroup Q _ _⟩ : elementaryGroup Q) ∈
      commutator (elementaryGroup Q) := by
  have hτ' : τ ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hτ2
  set v' := (τ ^ 2 - 1)⁻¹ • v with hv'
  have hv'P : v' ∈ P.perp := P.perp.smul_mem _ hv
  have hev' : polar Q P.e v' = 0 := (HypPair.mem_perp.mp hv'P).1
  have hhe := torus_apply_e P ha hc hτ one_ne_zero
  have hhv := torus_apply_of_mem_perp P h2 ha hc hτ one_ne_zero hv'P
  have key := commutatorElement_eichler_smul (torus_mem_orthogonalGroup P a τ 1) hhe hhv hev'
  have hl : τ ^ 2 / 1 ^ 2 - 1 = τ ^ 2 - 1 := by rw [one_pow, div_one]
  rw [hl, hv', smul_smul, mul_inv_cancel₀ hτ', one_smul] at key
  have hmem := Subgroup.commutator_mem_commutator (Subgroup.mem_top
    (⟨torus Q P a τ 1, torus_mem P a τ 1⟩ : elementaryGroup Q))
    (Subgroup.mem_top (⟨eichler Q P.e v', eichler_mem_elementaryGroup Q _ _⟩ :
      elementaryGroup Q))
  have heq : (⁅(⟨torus Q P a τ 1, torus_mem P a τ 1⟩ : elementaryGroup Q),
      ⟨eichler Q P.e v', eichler_mem_elementaryGroup Q _ _⟩⁆ : elementaryGroup Q) =
        ⟨eichler Q P.e v, eichler_mem_elementaryGroup Q _ _⟩ := Subtype.ext key
  rw [heq] at hmem
  exact hmem

theorem eichler_mem_commutator_of_center (h2 : (2 : K) ≠ 0) {a : V} (ha : a ∈ P.perp)
    (hc : Q a ≠ 0) {τ : K} (hτ : τ ≠ 0) (hτ2 : τ ^ 2 ≠ 1) {v : V} (hv : polar Q P.e v = 0) :
    (⟨eichler Q P.e v, eichler_mem_elementaryGroup Q _ _⟩ : elementaryGroup Q) ∈
      commutator (elementaryGroup Q) := by
  have hdecomp : v = P.proj v + polar Q v P.f • P.e := by
    have := P.eq_add_proj v
    rw [polar_comm Q v P.e, hv, zero_smul, add_zero] at this
    rw [add_comm]
    exact this
  have h := eichler_add_smul_self P.Q_e (P.proj v) (polar Q v P.f)
  rw [← hdecomp] at h
  have := eichler_mem_commutator_of_mem_perp P h2 ha hc hτ hτ2 (P.proj_mem_perp v)
  convert this using 1
  exact Subtype.ext h

theorem commutator_elementaryGroup_eq_top_small (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hA : HasAnisoPerp Q) {τ : K} (hτ : τ ≠ 0)
    (hτ2 : τ ^ 2 ≠ 1) : commutator (elementaryGroup Q) = ⊤ := by
  by_cases hex : ∃ x : V, Q x = 0 ∧ x ≠ 0
  swap
  ·
    push Not at hex
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨u, w, hu, hw, rfl⟩ := hx
      by_cases hu0 : u = 0
      · subst hu0
        have : (⟨eichler Q 0 w, eichler_mem_elementaryGroup Q 0 w⟩ : elementaryGroup Q) = 1 :=
          Subtype.ext (eichler_zero_left Q w)
        rw [this]
        exact Subgroup.one_mem _
      · exact absurd (hex u hu) hu0
    | one => exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx => exact Subgroup.inv_mem _ ihx
  obtain ⟨x₀, hx₀, hx₀0⟩ := hex
  obtain ⟨P, rfl⟩ := exists_hypPair hQ hx₀ hx₀0
  obtain ⟨a, ha, hc⟩ := hA P
  set N := commutator (elementaryGroup Q)
  have hN : N.Normal := inferInstance
  have hgen : ∀ u w, Q u = 0 → polar Q u w = 0 →
      (⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩ : elementaryGroup Q) ∈ N := by
    intro u w hu hw
    by_cases hu0 : u = 0
    · subst hu0
      have : (⟨eichler Q 0 w, eichler_mem_elementaryGroup Q 0 w⟩ : elementaryGroup Q) = 1 :=
        Subtype.ext (eichler_zero_left Q w)
      rw [this]
      exact N.one_mem
    obtain ⟨g, hg, c, hc0, hgu⟩ := exists_mem_elementaryGroup_apply_eq_smul hQ hA P.Q_e hu
      P.e_ne_zero hu0
    have hgO := elementaryGroup_le_orthogonalGroup Q hg
    have hv : polar Q P.e (c⁻¹ • g⁻¹ w) = 0 := by
      rw [polar_smul_right_eq, ← polar_map_of_mem hgO P.e (g⁻¹ w), hgu,
        LinearEquiv.apply_inv_apply', polar_smul_left_eq, hw, mul_zero, mul_zero]
    have hmem := hN.conj_mem _ (eichler_mem_commutator_of_center P h2 ha hc hτ hτ2 hv) ⟨g, hg⟩
    convert hmem using 1
    apply Subtype.ext
    change eichler Q u w = g * eichler Q P.e (c⁻¹ • g⁻¹ w) * g⁻¹
    rw [eichler_conj hgO, hgu, map_smul, LinearEquiv.apply_inv_apply', eichler_smul_left,
      smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, w, hu, hw, rfl⟩ := hx
    exact hgen u w hu hw
  | one => exact N.one_mem
  | mul x y hx hy ihx ihy => exact N.mul_mem ihx ihy
  | inv x hx ihx => exact N.inv_mem ihx

end CFSG.ClassicalGroups.Orthogonal.Small
