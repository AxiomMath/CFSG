module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNotLongRootBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAutUBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_add_smul_left_eq {u w : V} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0) (c : K) : eichler Q (u + c • w) w = eichler Q u w := by
  have h1 : Q (u + c • w) = 0 := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hu, hw, polar_smul_right_eq, huw]
    ring
  have h2 : polar Q (u + c • w) w = 0 := by
    rw [polar_add_left, polar_smul_left_eq, huw, polar_self_eq_zero hw]
    ring
  rw [eichler_eq_eichler_neg h1 hw h2, eichler_eq_eichler_neg hu hw huw, neg_add, ← neg_smul,
    eichler_add_smul_self hw]

section Plane

variable {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂)

include h₁₂

theorem eichler_e_e_apply (y : V) :
    eichler Q P₁.e P₂.e y = y + polar Q y P₁.e • P₂.e - polar Q y P₂.e • P₁.e := by
  rw [eichler_apply P₁.Q_e h₁₂.ee, P₂.Q_e, zero_mul, add_zero]

theorem apply_e_of_commute {g : V ≃ₗ[K] V}
    (hc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g) :
    g P₁.e = polar Q (g P₂.f) P₂.e • P₁.e - polar Q (g P₂.f) P₁.e • P₂.e ∧
      g P₂.e = polar Q (g P₁.f) P₁.e • P₂.e - polar Q (g P₁.f) P₂.e • P₁.e := by
  have hz : ∀ y, g (eichler Q P₁.e P₂.e y) = eichler Q P₁.e P₂.e (g y) := fun y =>
    LinearEquiv.congr_fun hc y
  have hf₂e₁ : polar Q P₂.f P₁.e = 0 := by rw [polar_comm]; exact h₁₂.ef
  have h1 : eichler Q P₁.e P₂.e P₂.f = P₂.f - P₁.e := by
    rw [eichler_e_e_apply h₁₂, hf₂e₁, P₂.polar_fe]
    module
  have h2 : eichler Q P₁.e P₂.e P₁.f = P₁.f + P₂.e := by
    rw [eichler_e_e_apply h₁₂, P₁.polar_fe, h₁₂.fe]
    module
  constructor
  · have e1 : P₁.e = P₂.f - eichler Q P₁.e P₂.e P₂.f := by rw [h1]; abel
    have := hz P₂.f
    rw [eichler_e_e_apply h₁₂ (g P₂.f)] at this
    calc g P₁.e = g P₂.f - g (eichler Q P₁.e P₂.e P₂.f) := by
          conv_lhs => rw [e1]
          rw [map_sub]
      _ = _ := by rw [this]; module
  · have e2 : P₂.e = eichler Q P₁.e P₂.e P₁.f - P₁.f := by rw [h2]; abel
    have := hz P₁.f
    rw [eichler_e_e_apply h₁₂ (g P₁.f)] at this
    calc g P₂.e = g (eichler Q P₁.e P₂.e P₁.f) - g P₁.f := by
          conv_lhs => rw [e2]
          rw [map_sub]
      _ = _ := by rw [this]; module

theorem det_eq_one_of_commute {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g) :
    polar Q (g P₂.f) P₂.e * polar Q (g P₁.f) P₁.e -
      polar Q (g P₁.f) P₂.e * polar Q (g P₂.f) P₁.e = 1 := by
  have h := polar_map_of_mem hg P₁.e P₁.f
  rw [(apply_e_of_commute h₁₂ hc).1, P₁.polar_ef, polar_sub_left, polar_smul_left_eq,
    polar_smul_left_eq, polar_comm Q P₁.e, polar_comm Q P₂.e] at h
  linear_combination h

theorem orth_flipPair_flipPair : (flipPair P₁).Orth (flipPair P₂) :=
  ⟨h₁₂.ff, h₁₂.fe, h₁₂.ef, h₁₂.ee⟩

end Plane

@[expose] def rootRadical (Q : QuadraticForm K V) (P₁ P₂ : HypPair Q) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {g | g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g P₁.e = P₁.e ∧ g P₂.e = P₂.e ∧
    ∀ x, polar Q x P₁.e = 0 → polar Q x P₂.e = 0 → ∃ a b : K, g x = x + a • P₁.e + b • P₂.e}
  mul_mem' := by
    rintro g h ⟨hgO, hg1, hg2, hg⟩ ⟨hhO, hh1, hh2, hh⟩
    refine ⟨mul_mem hgO hhO, by rw [LinearEquiv.mul_apply, hh1, hg1],
      by rw [LinearEquiv.mul_apply, hh2, hg2], fun x hx1 hx2 => ?_⟩
    obtain ⟨a, b, hab⟩ := hh x hx1 hx2
    obtain ⟨a', b', hab'⟩ := hg x hx1 hx2
    refine ⟨a + a', b + b', ?_⟩
    rw [LinearEquiv.mul_apply, hab, map_add, map_add, map_smul, map_smul, hg1, hg2, hab']
    module
  one_mem' := ⟨one_mem _, rfl, rfl, fun x _ _ => ⟨0, 0, by simp⟩⟩
  inv_mem' := by
    rintro g ⟨hgO, hg1, hg2, hg⟩
    have hi1 : g⁻¹ P₁.e = P₁.e := by
      apply g.injective
      rw [LinearEquiv.apply_inv_apply', hg1]
    have hi2 : g⁻¹ P₂.e = P₂.e := by
      apply g.injective
      rw [LinearEquiv.apply_inv_apply', hg2]
    refine ⟨inv_mem hgO, hi1, hi2, fun x hx1 hx2 => ?_⟩
    obtain ⟨a, b, hab⟩ := hg x hx1 hx2
    refine ⟨-a, -b, ?_⟩
    apply g.injective
    rw [LinearEquiv.apply_inv_apply', map_add, map_add, map_smul, map_smul, hg1, hg2, hab]
    module

theorem mem_rootRadical {P₁ P₂ : HypPair Q} {g : V ≃ₗ[K] V} :
    g ∈ rootRadical Q P₁ P₂ ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g P₁.e = P₁.e ∧
      g P₂.e = P₂.e ∧
      ∀ x, polar Q x P₁.e = 0 → polar Q x P₂.e = 0 → ∃ a b : K, g x = x + a • P₁.e + b • P₂.e :=
  Iff.rfl

section Radical

variable {P₁ P₂ : HypPair Q}

theorem pow_four_of_mem_rootRadical [CharP K 2] {g : V ≃ₗ[K] V}
    (hg : g ∈ rootRadical Q P₁ P₂) : g ^ 4 = 1 := by
  obtain ⟨hgO, hg1, hg2, hg⟩ := hg
  have h2v : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]
  have hperp : ∀ x, polar Q (g x - x) P₁.e = 0 ∧ polar Q (g x - x) P₂.e = 0 := by
    intro x
    have h1 := polar_map_of_mem hgO x P₁.e
    have h2 := polar_map_of_mem hgO x P₂.e
    rw [hg1] at h1
    rw [hg2] at h2
    exact ⟨by rw [polar_sub_left, h1, sub_self], by rw [polar_sub_left, h2, sub_self]⟩
  have hsq : ∀ x, ∃ a b : K, g (g x) = -x + (a • P₁.e + b • P₂.e) := by
    intro x
    obtain ⟨a, b, hab⟩ := hg (g x - x) (hperp x).1 (hperp x).2
    refine ⟨a, b, ?_⟩
    rw [map_sub, sub_eq_iff_eq_add] at hab
    have e : g (g x) = (g x + g x) - x + (a • P₁.e + b • P₂.e) := by
      rw [hab]
      abel
    rw [e, h2v, zero_sub]
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨a, b, hab⟩ := hsq x
  have hfix : g (g (a • P₁.e + b • P₂.e)) = a • P₁.e + b • P₂.e := by
    simp only [map_add, map_smul, hg1, hg2]
  have e4 : (g ^ 4) x = g (g (g (g x))) := by
    simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply]
  rw [e4, hab, map_add, map_add, map_neg, map_neg, hab, hfix]
  change _ = x
  abel

theorem isPGroup_rootRadical [CharP K 2] : IsPGroup 2 (rootRadical Q P₁ P₂) := by
  rintro ⟨g, hg⟩
  exact ⟨2, Subtype.ext (by simpa using pow_four_of_mem_rootRadical hg)⟩

theorem eichler_mem_rootRadical_left (h₁₂ : P₁.Orth P₂) {x : V} (hx₁ : polar Q P₁.e x = 0)
    (hx₂ : polar Q P₂.e x = 0) : eichler Q P₁.e x ∈ rootRadical Q P₁ P₂ := by
  refine ⟨eichler_mem_orthogonalGroup Q _ _, eichler_apply_self _ _,
    eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact h₁₂.ee) hx₂, fun y hy1 _ => ?_⟩
  refine ⟨-polar Q y x, 0, ?_⟩
  rw [eichler_apply P₁.Q_e hx₁, hy1]
  module

theorem eichler_mem_rootRadical_right (h₁₂ : P₁.Orth P₂) {x : V} (hx₁ : polar Q P₁.e x = 0)
    (hx₂ : polar Q P₂.e x = 0) : eichler Q P₂.e x ∈ rootRadical Q P₁ P₂ := by
  refine ⟨eichler_mem_orthogonalGroup Q _ _,
    eichler_apply_of_polar_eq_zero h₁₂.ee hx₁, eichler_apply_self _ _, fun y _ hy2 => ?_⟩
  refine ⟨0, -polar Q y x, ?_⟩
  rw [eichler_apply P₂.Q_e hx₂, hy2]
  module

theorem conj_mem_rootRadical (h₁₂ : P₁.Orth P₂) {m g : V ≃ₗ[K] V}
    (hm : m ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hmc : m * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * m) (hg : g ∈ rootRadical Q P₁ P₂) :
    m * g * m⁻¹ ∈ rootRadical Q P₁ P₂ := by
  obtain ⟨hgO, hg1, hg2, hg⟩ := hg
  have hmc' : m⁻¹ * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * m⁻¹ :=
    (show Commute m (eichler Q P₁.e P₂.e) from hmc).inv_left
  obtain ⟨hm1, hm2⟩ := apply_e_of_commute h₁₂ hmc
  obtain ⟨hi1, hi2⟩ := apply_e_of_commute h₁₂ hmc'
  have hgP : ∀ a b : K, g (a • P₁.e - b • P₂.e) = a • P₁.e - b • P₂.e := fun a b => by
    rw [map_sub, map_smul, map_smul, hg1, hg2]
  have hgP' : ∀ a b : K, g (a • P₂.e - b • P₁.e) = a • P₂.e - b • P₁.e := fun a b => by
    rw [map_sub, map_smul, map_smul, hg1, hg2]
  refine ⟨mul_mem (mul_mem hm hgO) (inv_mem hm), ?_, ?_, fun x hx1 hx2 => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hi1, hgP, ← hi1,
      LinearEquiv.apply_inv_apply']
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hi2, hgP', ← hi2,
      LinearEquiv.apply_inv_apply']
  · have hy1 : polar Q (m⁻¹ x) P₁.e = 0 := by
      have h := polar_map_of_mem hm (m⁻¹ x) P₁.e
      rw [LinearEquiv.apply_inv_apply', hm1, polar_sub_right, polar_smul_right_eq,
        polar_smul_right_eq, hx1, hx2] at h
      rw [← h]
      ring
    have hy2 : polar Q (m⁻¹ x) P₂.e = 0 := by
      have h := polar_map_of_mem hm (m⁻¹ x) P₂.e
      rw [LinearEquiv.apply_inv_apply', hm2, polar_sub_right, polar_smul_right_eq,
        polar_smul_right_eq, hx1, hx2] at h
      rw [← h]
      ring
    obtain ⟨a, b, hab⟩ := hg (m⁻¹ x) hy1 hy2
    refine ⟨a * polar Q (m P₂.f) P₂.e - b * polar Q (m P₁.f) P₂.e,
      b * polar Q (m P₁.f) P₁.e - a * polar Q (m P₂.f) P₁.e, ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hab, map_add, map_add,
      LinearEquiv.apply_inv_apply', map_smul, map_smul, hm1, hm2]
    module

theorem commute_of_apply_eq {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {u w : V} (hu : g u = u) (hw : g w = w) : g * eichler Q u w = eichler Q u w * g := by
  have h := eichler_conj hgO u w
  rw [hu, hw] at h
  calc g * eichler Q u w = g * eichler Q u w * g⁻¹ * g := by group
    _ = eichler Q u w * g := by rw [h]

theorem rootRadical_le_centralizer :
    rootRadical Q P₁ P₂ ≤ centralizer {eichler Q P₁.e P₂.e} := by
  rintro g ⟨hgO, hg1, hg2, -⟩
  exact mem_centralizer_singleton_iff.mpr (commute_of_apply_eq hgO hg1 hg2)

end Radical

@[expose] def rootLevi (Q : QuadraticForm K V) (P₁ P₂ : HypPair Q) : Subgroup (V ≃ₗ[K] V) :=
  TauCeti.QuadraticMap.orthogonalGroup Q ⊓ centralizer {eichler Q P₁.e P₂.e} ⊓
    centralizer {eichler Q P₁.f P₂.f}

section Levi

variable {P₁ P₂ : HypPair Q}

theorem rootLevi_le_centralizer :
    rootLevi Q P₁ P₂ ≤ centralizer {eichler Q P₁.e P₂.e} :=
  fun _ hg => hg.1.2

theorem mem_rootLevi_of_fix {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (he₁ : g P₁.e = P₁.e) (hf₁ : g P₁.f = P₁.f) (he₂ : g P₂.e = P₂.e) (hf₂ : g P₂.f = P₂.f) :
    g ∈ rootLevi Q P₁ P₂ :=
  ⟨⟨hgO, mem_centralizer_singleton_iff.mpr (commute_of_apply_eq hgO he₁ he₂)⟩,
    mem_centralizer_singleton_iff.mpr (commute_of_apply_eq hgO hf₁ hf₂)⟩

theorem eichler_smul_f_mem_rootLevi (h₁₂ : P₁.Orth P₂) (t : K) :
    eichler Q P₁.e (t • P₂.f) ∈ rootLevi Q P₁ P₂ := by
  have hO := eichler_mem_orthogonalGroup Q P₁.e (t • P₂.f)
  refine ⟨⟨hO, rootPairSub_le_centralizer P₁.Q_e P₂.Q_e h₁₂.ee
    (rootGroup_le_rootPairSub_left _ _ (eichler_mem_rootGroup (polar_e_smul_f h₁₂ t)))⟩,
    mem_centralizer_singleton_iff.mpr ?_⟩
  have h := eichler_conj hO P₁.f P₂.f
  rw [eichler_smul_f_apply_f h₁₂, eichler_smul_f_apply_f' h₁₂,
    eichler_add_smul_left_eq P₁.Q_f P₂.Q_f h₁₂.ff] at h
  calc eichler Q P₁.e (t • P₂.f) * eichler Q P₁.f P₂.f =
      eichler Q P₁.e (t • P₂.f) * eichler Q P₁.f P₂.f * (eichler Q P₁.e (t • P₂.f))⁻¹ *
        eichler Q P₁.e (t • P₂.f) := by group
    _ = _ := by rw [h]

theorem eichler_smul_f_mem_rootLevi' (h₁₂ : P₁.Orth P₂) (t : K) :
    eichler Q P₂.e (t • P₁.f) ∈ rootLevi Q P₁ P₂ := by
  have h₂₁ := h₁₂.symm
  have hO := eichler_mem_orthogonalGroup Q P₂.e (t • P₁.f)
  refine ⟨⟨hO, rootPairSub_le_centralizer P₁.Q_e P₂.Q_e h₁₂.ee
    (rootGroup_le_rootPairSub_right _ _ (eichler_mem_rootGroup (polar_e_smul_f h₂₁ t)))⟩,
    mem_centralizer_singleton_iff.mpr ?_⟩
  have h := eichler_conj hO P₁.f P₂.f
  rw [eichler_smul_f_apply_f h₂₁, eichler_smul_f_apply_f' h₂₁,
    eichler_add_smul_self P₁.Q_f] at h
  calc eichler Q P₂.e (t • P₁.f) * eichler Q P₁.f P₂.f =
      eichler Q P₂.e (t • P₁.f) * eichler Q P₁.f P₂.f * (eichler Q P₂.e (t • P₁.f))⁻¹ *
        eichler Q P₂.e (t • P₁.f) := by group
    _ = _ := by rw [h]

theorem rootRadical_inf_rootLevi (h₁₂ : P₁.Orth P₂) :
    rootRadical Q P₁ P₂ ⊓ rootLevi Q P₁ P₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨hgO, hg1, hg2, hg⟩, -, hgc'⟩
  rw [mem_bot]
  obtain ⟨hf1, hf2⟩ := apply_e_of_commute (orth_flipPair_flipPair h₁₂)
    (mem_centralizer_singleton_iff.mp hgc')
  simp only [flipPair_e, flipPair_f, hg1, hg2, P₁.polar_ef, P₂.polar_ef, one_smul] at hf1 hf2
  rw [polar_comm Q P₂.e P₁.f, h₁₂.fe, zero_smul, sub_zero] at hf1
  rw [h₁₂.ef, zero_smul, sub_zero] at hf2
  have hw : ∀ w, polar Q P₁.e w = 0 → polar Q P₁.f w = 0 → polar Q P₂.e w = 0 →
      polar Q P₂.f w = 0 → g w = w := by
    intro w h1 h2 h3 h4
    obtain ⟨a, b, hab⟩ := hg w (by rw [polar_comm]; exact h1) (by rw [polar_comm]; exact h3)
    have ha := polar_map_of_mem hgO w P₁.f
    have hb := polar_map_of_mem hgO w P₂.f
    rw [hab, hf1, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
      P₁.polar_ef, polar_comm Q P₂.e P₁.f, h₁₂.fe] at ha
    rw [hab, hf2, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
      P₂.polar_ef, h₁₂.ef] at hb
    have ha0 : a = 0 := by linear_combination ha
    have hb0 : b = 0 := by linear_combination hb
    rw [hab, ha0, hb0, zero_smul, zero_smul, add_zero, add_zero]
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨y, hy⟩ : ∃ y, y = P₁.proj v := ⟨_, rfl⟩
  obtain ⟨w, hw'⟩ : ∃ w, w = P₂.proj y := ⟨_, rfl⟩
  have hy1 : polar Q P₁.e y = 0 := by rw [hy]; exact (HypPair.mem_perp.mp (P₁.proj_mem_perp v)).1
  have hy2 : polar Q P₁.f y = 0 := by rw [hy]; exact (HypPair.mem_perp.mp (P₁.proj_mem_perp v)).2
  have hw1 : polar Q P₂.e w = 0 := by rw [hw']; exact (HypPair.mem_perp.mp (P₂.proj_mem_perp y)).1
  have hw2 : polar Q P₂.f w = 0 := by rw [hw']; exact (HypPair.mem_perp.mp (P₂.proj_mem_perp y)).2
  have hw3 : polar Q P₁.e w = 0 := by
    rw [hw', HypPair.proj, polar_sub_right, polar_sub_right, polar_smul_right_eq,
      polar_smul_right_eq, hy1, h₁₂.ee, h₁₂.ef]
    ring
  have hw4 : polar Q P₁.f w = 0 := by
    rw [hw', HypPair.proj, polar_sub_right, polar_sub_right, polar_smul_right_eq,
      polar_smul_right_eq, hy2, h₁₂.fe, h₁₂.ff]
    ring
  have hv : v = polar Q v P₁.f • P₁.e + polar Q v P₁.e • P₁.f +
      (polar Q y P₂.f • P₂.e + polar Q y P₂.e • P₂.f + w) := by
    rw [hw', ← P₂.eq_add_proj y, hy]
    exact P₁.eq_add_proj v
  change g v = v
  conv_lhs => rw [hv]
  simp only [map_add, map_smul]
  rw [hg1, hf1, hg2, hf2, hw w hw3 hw4 hw1 hw2]
  exact hv.symm

end Levi

section Factor

variable {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂)

include h₁₂

theorem exists_word_of_ne_zero (H : Subgroup (V ≃ₗ[K] V))
    (hx : ∀ t : K, eichler Q P₁.e (t • P₂.f) ∈ H) (hy : ∀ t : K, eichler Q P₂.e (t • P₁.f) ∈ H)
    {a b c d : K} (hdet : a * d - b * c = 1) (hc : c ≠ 0) :
    ∃ m ∈ H, m P₁.e = a • P₁.e + c • P₂.e ∧ m P₂.e = b • P₁.e + d • P₂.e := by
  have h₂₁ := h₁₂.symm
  obtain ⟨α, hα⟩ : ∃ α : K, α = (1 - a) * c⁻¹ := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : K, γ = (1 - d) * c⁻¹ := ⟨_, rfl⟩
  have hαc : α * c = 1 - a := by rw [hα, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hγc : γ * c = 1 - d := by rw [hγ, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hb : α * d + γ = -b := by
    apply mul_right_cancel₀ hc
    linear_combination d * hαc + hγc - hdet
  refine ⟨eichler Q P₁.e (α • P₂.f) * eichler Q P₂.e ((-c) • P₁.f) * eichler Q P₁.e (γ • P₂.f),
    mul_mem (mul_mem (hx α) (hy _)) (hx γ), ?_, ?_⟩
  · simp only [LinearEquiv.mul_apply, eichler_smul_f_apply_e, eichler_smul_f_apply_e' h₂₁,
      map_sub, map_smul, eichler_smul_f_apply_e' h₁₂]
    linear_combination (norm := module) (-(1 : K)) • hαc • P₁.e
  · simp only [LinearEquiv.mul_apply, eichler_smul_f_apply_e, eichler_smul_f_apply_e' h₂₁,
      map_sub, map_smul, eichler_smul_f_apply_e' h₁₂]
    linear_combination (norm := module) (-(1 : K)) • hb • P₁.e + α • hγc • P₁.e - hγc • P₂.e

theorem exists_word (H : Subgroup (V ≃ₗ[K] V))
    (hx : ∀ t : K, eichler Q P₁.e (t • P₂.f) ∈ H) (hy : ∀ t : K, eichler Q P₂.e (t • P₁.f) ∈ H)
    {a b c d : K} (hdet : a * d - b * c = 1) :
    ∃ m ∈ H, m P₁.e = a • P₁.e + c • P₂.e ∧ m P₂.e = b • P₁.e + d • P₂.e := by
  have h₂₁ := h₁₂.symm
  by_cases hc : c = 0
  · subst hc
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hdet
    obtain ⟨m, hm, hm1, hm2⟩ := exists_word_of_ne_zero h₁₂ H hx hy (a := a) (b := b) (c := -a)
      (d := d - b) (by linear_combination hdet) (neg_ne_zero.mpr ha)
    refine ⟨eichler Q P₂.e ((-1 : K) • P₁.f) * m, mul_mem (hy _) hm, ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, hm1, map_add, map_smul, map_smul, eichler_smul_f_apply_e' h₂₁,
        eichler_smul_f_apply_e]
      module
    · rw [LinearEquiv.mul_apply, hm2, map_add, map_smul, map_smul, eichler_smul_f_apply_e' h₂₁,
        eichler_smul_f_apply_e]
      module
  · exact exists_word_of_ne_zero h₁₂ H hx hy hdet hc

theorem exists_eichler_mul_apply_f {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg1 : g P₁.e = P₁.e)
    (hg2 : g P₂.e = P₂.e) :
    ∃ y₁ y₂ : V, polar Q P₁.e y₁ = 0 ∧ polar Q P₂.e y₁ = 0 ∧ polar Q P₁.e y₂ = 0 ∧
      polar Q P₂.e y₂ = 0 ∧
      (eichler Q P₁.e y₁ * eichler Q P₂.e y₂) P₁.f = g P₁.f ∧
      (eichler Q P₁.e y₁ * eichler Q P₂.e y₂) P₂.f = g P₂.f := by
  obtain ⟨u₁, hu₁⟩ : ∃ u, u = g P₁.f := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u, u = g P₂.f := ⟨_, rfl⟩
  rw [← hu₁, ← hu₂]
  have hf₂e₁ : polar Q P₂.f P₁.e = 0 := by rw [polar_comm]; exact h₁₂.ef
  have he₂f₁ : polar Q P₂.e P₁.f = 0 := by rw [polar_comm]; exact h₁₂.fe
  have he₂e₁ : polar Q P₂.e P₁.e = 0 := by rw [polar_comm]; exact h₁₂.ee
  have hf₂f₁ : polar Q P₂.f P₁.f = 0 := by rw [polar_comm]; exact h₁₂.ff
  have hQ1 : Q u₁ = 0 := by rw [hu₁, map_of_mem hgO, P₁.Q_f]
  have hQ2 : Q u₂ = 0 := by rw [hu₂, map_of_mem hgO, P₂.Q_f]
  have h11 : polar Q u₁ P₁.e = 1 := by
    rw [← hg1, hu₁, polar_map_of_mem hgO, P₁.polar_fe]
  have h21 : polar Q u₁ P₂.e = 0 := by
    rw [← hg2, hu₁, polar_map_of_mem hgO, h₁₂.fe]
  have h12 : polar Q u₂ P₁.e = 0 := by
    rw [← hg1, hu₂, polar_map_of_mem hgO, hf₂e₁]
  have h22 : polar Q u₂ P₂.e = 1 := by
    rw [← hg2, hu₂, polar_map_of_mem hgO, P₂.polar_fe]
  have h1u2 : polar Q u₂ u₁ = 0 := by
    rw [hu₁, hu₂, polar_map_of_mem hgO, hf₂f₁]
  obtain ⟨y₁, hy₁⟩ : ∃ y, y = u₁ - P₁.f - polar Q u₁ P₁.f • P₁.e := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y,
      y = u₂ - P₂.f - polar Q u₂ P₂.f • P₂.e - polar Q u₂ P₁.f • P₁.e := ⟨_, rfl⟩
  have hy11 : polar Q P₁.e y₁ = 0 := by
    rw [polar_comm, hy₁]
    simp only [polar_sub_left, polar_smul_left_eq, h11, P₁.polar_fe, P₁.polar_ee]
    ring
  have hy21 : polar Q P₂.e y₁ = 0 := by
    rw [polar_comm, hy₁]
    simp only [polar_sub_left, polar_smul_left_eq, h21, h₁₂.fe, h₁₂.ee]
    ring
  have hy12 : polar Q P₁.e y₂ = 0 := by
    rw [polar_comm, hy₂]
    simp only [polar_sub_left, polar_smul_left_eq, h12, hf₂e₁, he₂e₁, P₁.polar_ee]
    ring
  have hy22 : polar Q P₂.e y₂ = 0 := by
    rw [polar_comm, hy₂]
    simp only [polar_sub_left, polar_smul_left_eq, h22, P₂.polar_fe, P₂.polar_ee, h₁₂.ee]
    ring
  refine ⟨y₁, y₂, hy11, hy21, hy12, hy22, ?_, ?_⟩
  · have hfy₂ : polar Q P₁.f y₂ = 0 := by
      rw [polar_comm, hy₂]
      simp only [polar_sub_left, polar_smul_left_eq, hf₂f₁, he₂f₁, P₁.polar_ef]
      ring
    have hA : eichler Q P₂.e y₂ P₁.f = P₁.f := by
      rw [eichler_apply P₂.Q_e hy22, polar_comm Q P₁.f P₂.e, he₂f₁, hfy₂]
      simp
    have hfy₁ : polar Q P₁.f y₁ = 0 := by
      rw [polar_comm, hy₁]
      simp only [polar_sub_left, polar_smul_left_eq, P₁.polar_ff, P₁.polar_ef]
      rw [polar_comm Q u₁ P₁.f]
      ring
    have hO₁ := eichler_mem_orthogonalGroup Q P₁.e y₁
    have hO₂ := eichler_mem_orthogonalGroup Q P₂.e y₂
    have hE : eichler Q P₁.e y₁ P₁.f = u₁ - (polar Q u₁ P₁.f + Q y₁) • P₁.e := by
      rw [eichler_apply P₁.Q_e hy11, P₁.polar_fe, one_smul, hfy₁, hy₁]
      module
    have hQE : Q (eichler Q P₁.e y₁ P₁.f) = 0 := by rw [map_of_mem hO₁, P₁.Q_f]
    have hs : polar Q u₁ P₁.f + Q y₁ = 0 := by
      rw [hE, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, QuadraticMap.map_smul, P₁.Q_e,
        hQ1, polar_smul_right_eq, h11] at hQE
      linear_combination -hQE
    rw [LinearEquiv.mul_apply, hA, hE, hs, zero_smul, sub_zero]
  · have hf₂y₂ : polar Q P₂.f y₂ = 0 := by
      rw [polar_comm, hy₂]
      simp only [polar_sub_left, polar_smul_left_eq, P₂.polar_ff, P₂.polar_ef, h₁₂.ef]
      rw [polar_comm Q u₂ P₂.f]
      ring
    have hO₁ := eichler_mem_orthogonalGroup Q P₁.e y₁
    have hO₂ := eichler_mem_orthogonalGroup Q P₂.e y₂
    have hB : eichler Q P₂.e y₂ P₂.f = u₂ - polar Q u₂ P₁.f • P₁.e -
        (polar Q u₂ P₂.f + Q y₂) • P₂.e := by
      rw [eichler_apply P₂.Q_e hy22, P₂.polar_fe, one_smul, hf₂y₂, hy₂]
      module
    have hv1 : polar Q (u₂ - polar Q u₂ P₁.f • P₁.e - (polar Q u₂ P₂.f + Q y₂) • P₂.e)
        P₁.e = 0 := by
      simp only [polar_sub_left, polar_smul_left_eq, h12, P₁.polar_ee, he₂e₁]
      ring
    have hvy : polar Q (u₂ - polar Q u₂ P₁.f • P₁.e - (polar Q u₂ P₂.f + Q y₂) • P₂.e) y₁ =
        -polar Q u₂ P₁.f := by
      rw [polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, hy11, hy21,
        hy₁]
      simp only [polar_sub_right, polar_smul_right_eq, h1u2, h12]
      ring
    have hC : eichler Q P₁.e y₁ (eichler Q P₂.e y₂ P₂.f) =
        u₂ - (polar Q u₂ P₂.f + Q y₂) • P₂.e := by
      rw [hB, eichler_apply P₁.Q_e hy11, hv1, hvy]
      module
    have hQC : Q (eichler Q P₁.e y₁ (eichler Q P₂.e y₂ P₂.f)) = 0 := by
      rw [map_of_mem hO₁, map_of_mem hO₂, P₂.Q_f]
    have hs : polar Q u₂ P₂.f + Q y₂ = 0 := by
      rw [hC, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, QuadraticMap.map_smul, P₂.Q_e,
        hQ2, polar_smul_right_eq, h22] at hQC
      linear_combination -hQC
    rw [LinearEquiv.mul_apply, hC, hs, zero_smul, sub_zero]

theorem mem_sup_of_commute (H : Subgroup (V ≃ₗ[K] V))
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hE : ∀ u w, eichler Q u w ∈ H)
    {g : V ≃ₗ[K] V} (hgH : g ∈ H)
    (hgc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g) :
    g ∈ (rootRadical Q P₁ P₂ ⊓ H) ⊔ (rootLevi Q P₁ P₂ ⊓ H) := by
  have hgO := hHO hgH
  obtain ⟨h1, h2⟩ := apply_e_of_commute h₁₂ hgc
  have hdet := det_eq_one_of_commute h₁₂ hgO hgc
  obtain ⟨m, hm, hm1, hm2⟩ := exists_word h₁₂ (rootLevi Q P₁ P₂ ⊓ H)
    (fun t => ⟨eichler_smul_f_mem_rootLevi h₁₂ t, hE _ _⟩)
    (fun t => ⟨eichler_smul_f_mem_rootLevi' h₁₂ t, hE _ _⟩)
    (a := polar Q (g P₂.f) P₂.e) (b := -polar Q (g P₁.f) P₂.e) (c := -polar Q (g P₂.f) P₁.e)
    (d := polar Q (g P₁.f) P₁.e) (by linear_combination hdet)
  have hmO := hHO hm.2
  have hg'1 : (m⁻¹ * g) P₁.e = P₁.e := by
    rw [LinearEquiv.mul_apply, h1]
    apply m.injective
    rw [LinearEquiv.apply_inv_apply', hm1]
    module
  have hg'2 : (m⁻¹ * g) P₂.e = P₂.e := by
    rw [LinearEquiv.mul_apply, h2]
    apply m.injective
    rw [LinearEquiv.apply_inv_apply', hm2]
    module
  have hg'O : m⁻¹ * g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem (inv_mem hmO) hgO
  obtain ⟨y₁, y₂, hy11, hy21, hy12, hy22, hf1, hf2⟩ :=
    exists_eichler_mul_apply_f h₁₂ hg'O hg'1 hg'2
  have hq : eichler Q P₁.e y₁ * eichler Q P₂.e y₂ ∈ rootRadical Q P₁ P₂ ⊓ H :=
    ⟨mul_mem (eichler_mem_rootRadical_left h₁₂ hy11 hy21)
      (eichler_mem_rootRadical_right h₁₂ hy12 hy22), mul_mem (hE _ _) (hE _ _)⟩
  set q := eichler Q P₁.e y₁ * eichler Q P₂.e y₂ with hqdef
  have hqi : ∀ v, q v = v → q⁻¹ v = v := fun v hv => by
    apply q.injective
    rw [LinearEquiv.apply_inv_apply', hv]
  have hqi' : ∀ v, q⁻¹ (q v) = v := fun v => by
    apply q.injective
    rw [LinearEquiv.apply_inv_apply']
  have hqe1 : q P₁.e = P₁.e := hq.1.2.1
  have hqe2 : q P₂.e = P₂.e := hq.1.2.2.1
  have hg''O : q⁻¹ * (m⁻¹ * g) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (inv_mem (hHO hq.2)) hg'O
  have hg'' : q⁻¹ * (m⁻¹ * g) ∈ rootLevi Q P₁ P₂ := by
    refine mem_rootLevi_of_fix hg''O ?_ ?_ ?_ ?_
    · rw [LinearEquiv.mul_apply, hg'1, hqi _ hqe1]
    · rw [LinearEquiv.mul_apply, ← hf1, hqi']
    · rw [LinearEquiv.mul_apply, hg'2, hqi _ hqe2]
    · rw [LinearEquiv.mul_apply, ← hf2, hqi']
  have hg''H : q⁻¹ * (m⁻¹ * g) ∈ H := mul_mem (inv_mem hq.2) (mul_mem (inv_mem hm.2) hgH)
  have e : g = m * (q * (q⁻¹ * (m⁻¹ * g))) := by group
  rw [e]
  exact mul_mem (mem_sup_right hm) (mul_mem (mem_sup_left hq) (mem_sup_right ⟨hg'', hg''H⟩))

end Factor

end CFSG.SeitzReduction.OmegaPilot
