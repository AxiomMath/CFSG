module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasTwo
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem orthogonal_fixed_norm_normal_form [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ : HypPair Q} (h : P₁.Orth P₂) {x : V}
    (hx : x ≠ 0) : ∃ g ∈ orthElementaryGroup Q, g x = Q x • P₁.e + P₁.f := by
  have hy : Q x • P₁.e + P₁.f ≠ 0 := fun h0 => by
    have h1 := congrArg (polar Q P₁.e) h0
    rw [polar_add_right, polar_smul_right_eq, P₁.polar_ee, P₁.polar_ef, polar_zero_right] at h1
    simp at h1
  have hQy : Q x = Q (Q x • P₁.e + P₁.f) := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, P₁.Q_e, P₁.Q_f, polar_smul_left_eq, P₁.polar_ef]
    ring
  exact exists_mem_elementaryGroup_apply_eq hQ h hx hy hQy

theorem exists_orth_hypPairs_of_plane [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 2 ∧ ∀ x ∈ T, Q x = 0) :
    ∃ P₁ P₂ : HypPair Q, P₁.Orth P₂ := by
  obtain ⟨T, hT2, hTs⟩ := hT
  obtain ⟨e, he, he0⟩ := exists_ne_zero_of_one_le_finrank (T := T) (by omega)
  obtain ⟨P₁, P₂, -, h⟩ := quadratic_two_hyperbolic_pairs hQ ⟨T, hT2, hTs⟩ (hTs e he) he0
  exact ⟨P₁, P₂, h⟩

theorem orthogonal_norm_shell_transitive [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 2 ∧ ∀ x ∈ T, Q x = 0) :
    (∀ x y : V, x ≠ 0 → y ≠ 0 → Q x = Q y → ∃ g ∈ orthElementaryGroup Q, g x = y) ∧
    ∀ x y : V, x ≠ 0 → y ≠ 0 → Q x = 0 → Q y = 0 →
      ∃ g ∈ orthElementaryGroup Q,
        (Submodule.span K {x}).map (g : V →ₗ[K] V) = Submodule.span K {y} := by
  obtain ⟨P₁, P₂, h⟩ := exists_orth_hypPairs_of_plane hQ hT
  have htr : ∀ x y : V, x ≠ 0 → y ≠ 0 → Q x = Q y → ∃ g ∈ orthElementaryGroup Q, g x = y :=
    fun x y hx hy hxy => exists_mem_elementaryGroup_apply_eq hQ h hx hy hxy
  refine ⟨htr, fun x y hx hy hQx hQy => ?_⟩
  obtain ⟨g, hg, hgx⟩ := htr x y hx hy (by rw [hQx, hQy])
  refine ⟨g, hg, ?_⟩
  rw [Submodule.map_span, Set.image_singleton]
  change Submodule.span K {g x} = _
  rw [hgx]

section Perfect

variable {P₁ P₂ P₃ : HypPair Q}

theorem eichler_e₂_eq_commutator (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    (t : K) : eichler Q P₁.e (t • P₂.e) = ⁅eichler Q P₃.e (t • P₂.e), eichler Q P₁.e P₃.f⁆ := by
  have hg := eichler_mem_orthogonalGroup Q P₃.e (t • P₂.e)
  have hgu : eichler Q P₃.e (t • P₂.e) P₁.e = P₁.e :=
    eichler_apply_of_polar_eq_zero (by rw [h₁₃.ee]) (by rw [polar_smul_right_eq, h₁₂.ee,
      mul_zero])
  have hgf : eichler Q P₃.e (t • P₂.e) P₃.f - P₃.f = t • P₂.e := by
    rw [eichler_apply P₃.Q_e (by rw [polar_smul_right_eq, polar_comm, h₂₃.ee, mul_zero]),
      polar_smul_right_eq, polar_comm Q P₃.f P₂.e, h₂₃.ef, map_smul_eq_sq, P₂.Q_e, P₃.polar_fe]
    simp
  rw [commutatorElement_eichler hg hgu h₁₃.ef, hgf]

theorem eichler_f₂_eq_commutator (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    (t : K) : eichler Q P₁.e (t • P₂.f) = ⁅eichler Q P₃.e (t • P₂.f), eichler Q P₁.e P₃.f⁆ := by
  have hg := eichler_mem_orthogonalGroup Q P₃.e (t • P₂.f)
  have hgu : eichler Q P₃.e (t • P₂.f) P₁.e = P₁.e :=
    eichler_apply_of_polar_eq_zero (by rw [h₁₃.ee]) (by rw [polar_smul_right_eq, h₁₂.ef,
      mul_zero])
  have hgf : eichler Q P₃.e (t • P₂.f) P₃.f - P₃.f = t • P₂.f := by
    rw [eichler_apply P₃.Q_e (by rw [polar_smul_right_eq, polar_comm, h₂₃.fe, mul_zero]),
      polar_smul_right_eq, polar_comm Q P₃.f P₂.f, h₂₃.ff, map_smul_eq_sq, P₂.Q_f, P₃.polar_fe]
    simp
  rw [commutatorElement_eichler hg hgu h₁₃.ef, hgf]

theorem eichler_w_eq_commutator (h₁₂ : P₁.Orth P₂) {w : V} (hw₁ : polar Q P₁.e w = 0)
    (hw₂ : polar Q P₂.e w = 0) (hw₂' : polar Q P₂.f w = 0) :
    eichler Q P₁.e (w - Q w • P₂.e) = ⁅eichler Q P₂.e w, eichler Q P₁.e P₂.f⁆ := by
  have hg := eichler_mem_orthogonalGroup Q P₂.e w
  have hgu : eichler Q P₂.e w P₁.e = P₁.e :=
    eichler_apply_of_polar_eq_zero (by rw [h₁₂.ee]) hw₁
  have hgf : eichler Q P₂.e w P₂.f - P₂.f = w - Q w • P₂.e := by
    rw [eichler_apply P₂.Q_e hw₂, hw₂', P₂.polar_fe]
    simp only [one_smul, zero_add, mul_one]
    abel
  rw [commutatorElement_eichler hg hgu h₁₂.ef, hgf]

theorem eichler_center_eq_three_commutators (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃)
    (h₂₃ : P₂.Orth P₃) {v : V} (hv : polar Q P₁.e v = 0) :
    ∃ a₁ ∈ orthElementaryGroup Q, ∃ b₁ ∈ orthElementaryGroup Q, ∃ a₂ ∈ orthElementaryGroup Q,
      ∃ b₂ ∈ orthElementaryGroup Q, ∃ a₃ ∈ orthElementaryGroup Q, ∃ b₃ ∈ orthElementaryGroup Q,
        eichler Q P₁.e v = ⁅a₁, b₁⁆ * ⁅a₂, b₂⁆ * ⁅a₃, b₃⁆ := by
  set a := polar Q v P₂.f
  set b := polar Q v P₂.e
  set w := v - polar Q v P₁.f • P₁.e - a • P₂.e - b • P₂.f with hw
  have hw₁ : polar Q P₁.e w = 0 := by
    rw [hw, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_smul_right_eq, hv, P₁.polar_ee, h₁₂.ee, h₁₂.ef]
    ring
  have hw₂ : polar Q P₂.e w = 0 := by
    rw [hw, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_smul_right_eq, P₂.polar_ee, P₂.polar_ef, polar_comm Q P₂.e P₁.e,
      h₁₂.ee, polar_comm Q P₂.e v]
    ring
  have hw₂' : polar Q P₂.f w = 0 := by
    rw [hw, polar_sub_right, polar_sub_right, polar_sub_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_smul_right_eq, P₂.polar_ff, P₂.polar_fe, polar_comm Q P₂.f P₁.e,
      h₁₂.ef, polar_comm Q P₂.f v]
    ring
  have hdecomp : v = (a • P₂.e + b • P₂.f + w) + polar Q v P₁.f • P₁.e := by
    rw [hw]
    abel
  have he₂ : polar Q P₁.e ((a + Q w) • P₂.e) = 0 := by rw [polar_smul_right_eq, h₁₂.ee, mul_zero]
  have hf₂ : polar Q P₁.e (b • P₂.f) = 0 := by rw [polar_smul_right_eq, h₁₂.ef, mul_zero]
  have hw' : polar Q P₁.e (w - Q w • P₂.e) = 0 := by
    rw [polar_sub_right, polar_smul_right_eq, hw₁, h₁₂.ee, mul_zero, sub_zero]
  have hprod : eichler Q P₁.e v = eichler Q P₁.e ((a + Q w) • P₂.e) *
      eichler Q P₁.e (b • P₂.f) * eichler Q P₁.e (w - Q w • P₂.e) := by
    rw [eichler_mul he₂ hf₂, eichler_mul (by rw [polar_add_right, he₂, hf₂, add_zero]) hw',
      hdecomp, eichler_add_smul_self P₁.Q_e]
    congr 1
    rw [add_smul]
    abel
  have hE : ∀ u x : V, eichler Q u x ∈ orthElementaryGroup Q := fun u x =>
    eichler_mem_elementaryGroup Q u x
  refine ⟨eichler Q P₃.e ((a + Q w) • P₂.e), hE _ _, eichler Q P₁.e P₃.f, hE _ _,
    eichler Q P₃.e (b • P₂.f), hE _ _, eichler Q P₁.e P₃.f, hE _ _, eichler Q P₂.e w, hE _ _,
    eichler Q P₁.e P₂.f, hE _ _, ?_⟩
  rw [hprod, eichler_e₂_eq_commutator h₁₂ h₁₃ h₂₃, eichler_f₂_eq_commutator h₁₂ h₁₃ h₂₃,
    eichler_w_eq_commutator h₁₂ hw₁ hw₂ hw₂']

theorem orthogonal_elementary_perfect [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    Group.IsPerfect (orthElementaryGroup Q) ∧
    ∀ u v : V, Q u = 0 → polar Q u v = 0 →
      ∃ a₁ ∈ orthElementaryGroup Q, ∃ b₁ ∈ orthElementaryGroup Q, ∃ a₂ ∈ orthElementaryGroup Q,
        ∃ b₂ ∈ orthElementaryGroup Q, ∃ a₃ ∈ orthElementaryGroup Q, ∃ b₃ ∈ orthElementaryGroup Q,
          eichler Q u v = ⁅a₁, b₁⁆ * ⁅a₂, b₂⁆ * ⁅a₃, b₃⁆ := by
  obtain ⟨T, hT3, hTs⟩ := hT
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_hypPairs hQ (T := T) hT3.ge hTs
  refine ⟨⟨commutator_elementaryGroup_eq_top h₁₂ h₁₃ h₂₃ hQ⟩, fun u v hu hv => ?_⟩
  have hE : ∀ x y : V, eichler Q x y ∈ orthElementaryGroup Q := fun x y =>
    eichler_mem_elementaryGroup Q x y
  by_cases hu0 : u = 0
  · subst hu0
    refine ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, 1, one_mem _, 1, one_mem _, 1, one_mem _,
      ?_⟩
    simp [eichler_zero_left]
  obtain ⟨g, hg, hgu⟩ := exists_mem_elementaryGroup_apply_eq hQ h₁₂ P₁.e_ne_zero hu0
    (by rw [P₁.Q_e, hu])
  have hgO := elementaryGroup_le_orthogonalGroup Q hg
  have hv' : polar Q P₁.e (g⁻¹ v) = 0 := by
    rw [← polar_map_of_mem hgO, hgu, LinearEquiv.apply_inv_apply', hv]
  obtain ⟨a₁, ha₁, b₁, hb₁, a₂, ha₂, b₂, hb₂, a₃, ha₃, b₃, hb₃, hprod⟩ :=
    eichler_center_eq_three_commutators h₁₂ h₁₃ h₂₃ hv'
  have hconj : eichler Q u v = g * eichler Q P₁.e (g⁻¹ v) * g⁻¹ := by
    rw [eichler_conj hgO, hgu, LinearEquiv.apply_inv_apply']
  have hc : ∀ x : V ≃ₗ[K] V, x ∈ orthElementaryGroup Q → g * x * g⁻¹ ∈ orthElementaryGroup Q :=
    fun x hx => mul_mem (mul_mem hg hx) (inv_mem hg)
  refine ⟨g * a₁ * g⁻¹, hc _ ha₁, g * b₁ * g⁻¹, hc _ hb₁, g * a₂ * g⁻¹, hc _ ha₂,
    g * b₂ * g⁻¹, hc _ hb₂, g * a₃ * g⁻¹, hc _ ha₃, g * b₃ * g⁻¹, hc _ hb₃, ?_⟩
  rw [hconj, hprod]
  simp only [commutatorElement_def]
  group

end Perfect

theorem orthogonal_elementary_hyperbolic_pair_straightening [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 2 ∧ ∀ x ∈ T, Q x = 0) {e f : V} (he : Q e = 0)
    (hef : polar Q e f = 1) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    ∃ a ∈ orthElementaryGroup Q, (a * g) e = e ∧ (a * g) f = f := by
  have he0 : e ≠ 0 := fun h0 => by rw [h0, polar_zero_left] at hef; exact zero_ne_one hef
  have hge0 : g e ≠ 0 := fun h0 => he0 (g.injective (by rw [h0, map_zero]))
  obtain ⟨b, hb, hbe⟩ := (orthogonal_norm_shell_transitive hQ hT).1 (g e) e hge0 he0
    (by rw [map_of_mem hg])
  have hbO := elementaryGroup_le_orthogonalGroup Q hb
  set f' := b (g f) with hf'
  have hQf' : Q f' = Q f := by rw [hf', map_of_mem hbO, map_of_mem hg]
  have hef' : polar Q e f' = 1 := by
    rw [hf', ← hbe, polar_map_of_mem hbO, polar_map_of_mem hg, hef]
  obtain ⟨hw, hmap⟩ := orthogonal_elementary_fiber_transitive Q he hQf' hef' hef one_ne_zero
  refine ⟨eichler Q e ((1 : K)⁻¹ • (f - f')) * b,
    mul_mem (eichler_mem_elementaryGroup Q _ _) hb, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hbe, eichler_apply_self]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hf', eichler_apply he hw]
    exact hmap

theorem orthogonal_reflections_commute_mod_elementary [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 2 ∧ ∀ x ∈ T, Q x = 0) (u : V) {v : V}
    (hv : Q v ≠ 0) :
    ⁅reflect Q u, reflect Q v⁆ ∈ orthElementaryGroup Q ∧
      letI : ((orthElementaryGroup Q).subgroupOf
          (TauCeti.QuadraticMap.orthogonalGroup Q)).Normal :=
        (orthogonal_elementary_normality Q).2
      ((⟨reflect Q u, reflect_mem_orthogonalGroup Q u⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) :
          TauCeti.QuadraticMap.orthogonalGroup Q ⧸
            (orthElementaryGroup Q).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)) *
        ((⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ :
          TauCeti.QuadraticMap.orthogonalGroup Q) :
          TauCeti.QuadraticMap.orthogonalGroup Q ⧸
            (orthElementaryGroup Q).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)) =
        ((⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ :
          TauCeti.QuadraticMap.orthogonalGroup Q) :
          TauCeti.QuadraticMap.orthogonalGroup Q ⧸
            (orthElementaryGroup Q).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)) *
        ((⟨reflect Q u, reflect_mem_orthogonalGroup Q u⟩ :
          TauCeti.QuadraticMap.orthogonalGroup Q) :
          TauCeti.QuadraticMap.orthogonalGroup Q ⧸
            (orthElementaryGroup Q).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have hsuO := reflect_mem_orthogonalGroup Q u
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0, map_zero])
  have hsv0 : reflect Q u v ≠ 0 := fun h0 => hv0 ((reflect Q u).injective (by rw [h0, map_zero]))
  obtain ⟨e, he, hev⟩ := (orthogonal_norm_shell_transitive hQ hT).1 v (reflect Q u v) hv0 hsv0
    (by rw [map_of_mem hsuO])
  have heO := elementaryGroup_le_orthogonalGroup Q he
  have h1 : reflect Q u * reflect Q v * (reflect Q u)⁻¹ = e * reflect Q v * e⁻¹ := by
    rw [reflect_conj hsuO, ← hev, reflect_conj heO]
  have hmem : ⁅reflect Q u, reflect Q v⁆ ∈ orthElementaryGroup Q := by
    have hc : ⁅reflect Q u, reflect Q v⁆ = e * (reflect Q v * e⁻¹ * (reflect Q v)⁻¹) := by
      rw [commutatorElement_def, h1]
      group
    rw [hc]
    refine mul_mem he ?_
    have hN := (orthogonal_elementary_normality Q).2
    exact hN.conj_mem ⟨e⁻¹, inv_mem heO⟩ (inv_mem he)
      ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩
  refine ⟨hmem, ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  change (reflect Q u * reflect Q v)⁻¹ * (reflect Q v * reflect Q u) ∈ orthElementaryGroup Q
  have hc : (reflect Q u * reflect Q v)⁻¹ * (reflect Q v * reflect Q u) =
      ⁅(reflect Q v)⁻¹, (reflect Q u)⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [hc, reflect_inv, reflect_inv, ← commutatorElement_inv]
  exact inv_mem hmem

end CFSG.LocalAnalysis.ComponentInitial
