module

public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionElem

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement


section ExistsGen

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_of_mul_self {P C : Subgroup G} (hP : IsSylowOf 2 P C) {s : G}
    (hsC : s ∈ C) (hs2 : s * s = 1) : ∃ y ∈ C, y * s * y⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : IsPGroup 2 ↥(zpowers (⟨s, hsC⟩ : ↥C)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [sq] using hs2))
  obtain ⟨S, hS⟩ := hZ.exists_le_sylow
  have hS' : IsSylowOf 2 ((S : Subgroup ↥C).map C.subtype) C := ⟨S, rfl⟩
  obtain ⟨k, hk, hkconj⟩ := hP.exists_mem_conj hS'
  refine ⟨k⁻¹, C.inv_mem hk, ?_⟩
  have hsS : s ∈ (S : Subgroup ↥C).map C.subtype :=
    ⟨⟨s, hsC⟩, hS (mem_zpowers _), rfl⟩
  have := (hkconj s).mp hsS
  simpa using this

end ExistsGen

namespace Facts

section Exists

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ : Subgroup G}

theorem exists_involution_U (d : Datum A) (hR : Radicals d.V V₁ V₂) :
    ∃ w ∈ d.V ⊓ centralizer (d.V : Set G), orderOf w = 2 ∧ ∀ p ∈ d.P, p * w = w * p := by
  refine exists_involution_normal_center d.hP.isPGroup (fun x hx => hx.1.1) ?_ ?_
  · intro x hx n hn
    refine ⟨d.conj_mem_V hx hn.1, mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : x⁻¹ * v * x⁻¹⁻¹ ∈ d.V := d.conj_mem_V (d.P.inv_mem hx) hv
    have h := mem_centralizer_iff.mp hn.2 _ hv'
    calc v * (x * n * x⁻¹) = x * ((x⁻¹ * v * x) * n) * x⁻¹ := by group
      _ = x * (n * (x⁻¹ * v * x)) * x⁻¹ := by rw [show x⁻¹ * v * x = x⁻¹ * v * x⁻¹⁻¹ by group, h]
      _ = x * n * x⁻¹ * v := by group
  · intro hbot
    have h1 := hR.card_center
    rw [hbot, Subgroup.card_bot] at h1
    omega

theorem alpha_of_exists_mul_t (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) {v : G}
    (hvA : v ∈ A) (hv2 : v * v = 1) (hv1 : v ≠ 1) (hvt : IsConj d.t (v * d.t)) : d.Alpha := by
  obtain ⟨w, hwU, hwo, hwc⟩ := exists_involution_U d hR
  have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  obtain ⟨a, ha, hav⟩ := F.invol_conj v hvA w hwU.1.2 hvo hwo
  have hct : a * d.t * a⁻¹ = d.t := by rw [d.comm_t_of_mem ha, mul_inv_cancel_right]
  have hconj : IsConj d.t (w * d.t) := by
    refine hvt.trans (isConj_iff.mpr ⟨a, ?_⟩)
    calc a * (v * d.t) * a⁻¹ = (a * v * a⁻¹) * (a * d.t * a⁻¹) := by group
      _ = w * d.t := by rw [hav, hct]
  refine ⟨w * d.t, ⟨d.P.mul_mem hwU.1.1 d.t_mem_P, mem_centralizer_iff.mpr fun p hp => ?_⟩,
    hconj, ?_⟩
  · calc p * (w * d.t) = (p * w) * d.t := by group
      _ = (w * p) * d.t := by rw [hwc p hp]
      _ = w * (p * d.t) := by group
      _ = w * (d.t * p) := by rw [d.P_comm_t hp]
      _ = w * d.t * p := by group
  · intro h
    have hwo' : w = 1 := by
      have := congrArg (· * d.t) h
      simpa [mul_assoc, d.t_mul_self] using this
    rw [hwo', orderOf_one] at hwo
    exact absurd hwo (by norm_num)

end Exists

end Facts

namespace Facts

section Exists2

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ : Subgroup G}

theorem eq_of_le_of_not_alpha (d : Datum A) (hα : ¬ d.Alpha) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hPQ : d.P ≤ Q) : Q = d.P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hQT⟩ := hQ.exists_le_sylow
  have hPT : d.P ≤ (T : Subgroup G) := hPQ.trans hQT
  by_cases hne : d.P = (T : Subgroup G)
  · exact le_antisymm (hne ▸ hQT) hPQ
  · obtain ⟨g, -, -, -, hz, hgne⟩ := d.exists_conj_center T hPT hne
    exact (hα ⟨g⁻¹ * d.t * g, hz, isConj_iff.mpr ⟨g⁻¹, by group⟩, hgne⟩).elim

theorem exists_conj_mem_P (d : Datum A)
    (hZ : ∃ g : G, g⁻¹ * d.t * g ≠ d.t ∧ g⁻¹ * d.t * g * d.t = d.t * (g⁻¹ * d.t * g)) :
    ∃ t' ∈ d.P, IsConj d.t t' ∧ t' ≠ d.t := by
  obtain ⟨g, hgne, hgc⟩ := hZ
  have hs2 : (g⁻¹ * d.t * g) * (g⁻¹ * d.t * g) = 1 := by
    calc (g⁻¹ * d.t * g) * (g⁻¹ * d.t * g) = g⁻¹ * (d.t * d.t) * g := by group
      _ = 1 := by rw [d.t_mul_self]; group
  have hsC : g⁻¹ * d.t * g ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact hgc
  obtain ⟨y, hy, hyP⟩ := exists_conj_mem_of_mul_self d.P_isSylow_centralizer hsC hs2
  have hyt : y * d.t = d.t * y := mem_centralizer_singleton_iff.mp hy
  refine ⟨y * (g⁻¹ * d.t * g) * y⁻¹, hyP, isConj_iff.mpr ⟨(g * y⁻¹)⁻¹, by group⟩, ?_⟩
  intro h
  apply hgne
  have : g⁻¹ * d.t * g = y⁻¹ * (y * (g⁻¹ * d.t * g) * y⁻¹) * y := by group
  rw [this, h]
  calc y⁻¹ * d.t * y = y⁻¹ * (d.t * y) := by group
    _ = y⁻¹ * (y * d.t) := by rw [hyt]
    _ = d.t := by group

theorem residual_of_not_alpha (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    (hα : ¬ d.Alpha) {t' : G} (ht'P : t' ∈ d.P) (hc : IsConj d.t t') (hne : t' ≠ d.t) :
    t' ∉ A ⊔ centralizer (A : Set G) ∧ Group.IsSolvable ↥(A ⊓ centralizer ({t'} : Set G)) := by
  have ht'2 := d.mul_self_of_isConj hc
  have ht'N : t' ∈ normalizer (A : Set G) := d.P_le_normalizer ht'P
  have hnot : t' ∉ A ⊔ centralizer (A : Set G) := by
    intro hAK
    obtain ⟨v, hv, r, hr, hvr, hv2, hr2⟩ := F.decomp_of_mul_self d ht'P hAK ht'2
    rcases eq_one_or_eq_t d hr hr2 with rfl | rfl
    · rw [mul_one] at hvr
      exact F.not_isConj_of_mem d hR (hvr ▸ hv.2) hc
    · apply hα
      refine F.alpha_of_exists_mul_t d hR hv.2 hv2 ?_ (hvr ▸ hc)
      rintro rfl
      exact hne (by rw [hvr, one_mul])
  refine ⟨hnot, ?_⟩
  by_contra hns
  obtain ⟨D, hDle, hD, c, hcD, hc2, hc1⟩ := F.outer_core t' ht'N ht'2 hnot hns
  obtain ⟨b, hb, hbt⟩ := F.outer_fuse t' ht'N ht'2 hnot c (hDle hcD) hc2
  obtain ⟨c₀, hc₀⟩ := isConj_iff.mp hc
  obtain ⟨g, hgt⟩ : ∃ g : G, g * t' * g⁻¹ = d.t := ⟨c₀⁻¹, by rw [← hc₀]; group⟩
  let D₁ : Subgroup G := D.map (MulAut.conj g).toMonoidHom
  have hD₁N : D₁ ≤ normalizer (A : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyc : y ∈ centralizer ({t'} : Set G) := (hDle hy).2
    have hy' : y * t' = t' * y := mem_centralizer_singleton_iff.mp hyc
    have : g * y * g⁻¹ ∈ centralizer ({d.t} : Set G) := by
      rw [mem_centralizer_singleton_iff, ← hgt]
      calc g * y * g⁻¹ * (g * t' * g⁻¹) = g * (y * t') * g⁻¹ := by group
        _ = g * (t' * y) * g⁻¹ := by rw [hy']
        _ = g * t' * g⁻¹ * (g * y * g⁻¹) := by group
    exact (centralizer_t_facts d.sector).1 this
  have hD₁ : ⁅D₁, D₁⁆ = D₁ := by
    rw [← Subgroup.map_commutator, hD]
  have hc₁ : g * c * g⁻¹ ∈ D₁ := ⟨c, hcD, by simp [MulAut.conj_apply]⟩
  have hc₁2 : (g * c * g⁻¹) * (g * c * g⁻¹) = 1 := by
    calc g * c * g⁻¹ * (g * c * g⁻¹) = g * (c * c) * g⁻¹ := by group
      _ = 1 := by rw [hc2]; group
  have hc₁A : g * c * g⁻¹ ∈ A := F.perfect_inv D₁ hD₁N hD₁ _ hc₁ hc₁2
  have hc₁1 : g * c * g⁻¹ ≠ 1 := by
    intro h
    apply hc1
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hcomm : c * t' = t' * c := mem_centralizer_singleton_iff.mp (hDle hcD).2
  have hconj : IsConj d.t (g * c * g⁻¹ * d.t) := by
    have h1 : IsConj d.t (t' * c) := by
      refine hc.trans (isConj_iff.mpr ⟨b, ?_⟩)
      exact hbt
    refine h1.trans (isConj_iff.mpr ⟨g, ?_⟩)
    calc g * (t' * c) * g⁻¹ = g * (c * t') * g⁻¹ := by rw [hcomm]
      _ = g * c * g⁻¹ * d.t := by rw [← hgt]; group
  exact hα (F.alpha_of_exists_mul_t d hR hc₁A hc₁2 hc₁1 hconj)

theorem residual_conf_of_not_alpha (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    (hZ : ∃ g : G, g⁻¹ * d.t * g ≠ d.t ∧ g⁻¹ * d.t * g * d.t = d.t * (g⁻¹ * d.t * g))
    (hα : ¬ d.Alpha) :
    (∀ Q : Subgroup G, IsPGroup 2 Q → d.P ≤ Q → Q = d.P) ∧
      (∃ t' ∈ d.P, IsConj d.t t' ∧ t' ≠ d.t) ∧
      ∀ t' ∈ d.P, IsConj d.t t' → t' ≠ d.t →
        t' ∉ A ⊔ centralizer (A : Set G) ∧ Group.IsSolvable ↥(A ⊓ centralizer ({t'} : Set G)) :=
  ⟨fun _ hQ hPQ => eq_of_le_of_not_alpha d hα hQ hPQ, exists_conj_mem_P d hZ,
    fun _ ht'P hc hne => F.residual_of_not_alpha d hR hα ht'P hc hne⟩

end Exists2

end Facts

end CFSG.OddStandard.Seitz77
