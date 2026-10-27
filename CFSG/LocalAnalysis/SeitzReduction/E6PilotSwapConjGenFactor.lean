module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverUnique

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.Outer)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open CFSG.Quasithin (perfectCore)

theorem card_eq_card_map_mul_card_inf_ker {A B : Type*} [Group A] [Group B] (φ : A →* B)
    (S : Subgroup A) :
    Nat.card S = Nat.card (S.map φ) * Nat.card (S ⊓ φ.ker : Subgroup A) := by
  set φ' : S →* S.map φ := (φ.comp S.subtype).codRestrict (S.map φ) fun x => ⟨x, x.2, rfl⟩
    with hφ'
  have hsurj : Function.Surjective φ' := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : φ'.ker = φ.ker.subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ'.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ' hsurj).toEquiv, hker]
  congr 1
  rw [← card_map_of_injective S.subtype_injective, subgroupOf_map_subtype, inf_comm]

section Factor


variable {G : Type} [Group G] [Finite G]

theorem exists_le_inf_centralizer_of_inner_quot_E6 {M : Subgroup G} (hMp : ⁅M, M⁆ = M)
    (hZ : Odd (Nat.card (center M))) {f : ℕ} {k : Type} [Field k] (hk : Nat.card k = 2 ^ f)
    (eM : M ⧸ center M ≃* adjointGroup .E6 k) {t : G} (ht : orderOf t = 2)
    (htM : t ∈ normalizer (M : Set G))
    (hin : normalizerQuotMulAut eM ⟨t, htM⟩ ∈
      (MulAut.conj : adjointGroup .E6 k →* MulAut (adjointGroup .E6 k)).range) :
    ∃ X : Subgroup G, X ≤ M ⊓ centralizer ({t} : Set G) ∧ 2 ^ (26 * f) ∣ Nat.card X := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hk
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hk
  obtain ⟨c, hc⟩ := hin
  set β := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  have hβ : ∀ m : M, ((β m : M) : G) = t * m * t⁻¹ := fun m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨t, htM⟩ m
  obtain ⟨q₀, hq₀⟩ := eM.surjective c
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q₀
  have : Group.IsPerfect M := Subgroup.isPerfect_iff.2 hMp
  have hkey : ∀ x : M,
      (QuotientGroup.mk (β x) : M ⧸ center M) = QuotientGroup.mk (m * x * m⁻¹) := by
    intro x
    apply eM.injective
    have h1 := normalizerQuotMulAut_apply eM ⟨t, htM⟩ x
    rw [← hc, MulAut.conj_apply, ← hq₀] at h1
    simp only [QuotientGroup.mk'_apply] at h1
    rw [← h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv]
  have hβm := eq_conj_of_mk_eq β m hkey
  have hm2 : m ^ 2 ∈ center M := by
    rw [mem_center_iff]
    intro g
    have h := normalizerMonoidHom_apply_apply_of_orderOf ht htM g
    rw [← hβdef, hβm (β g), hβm g] at h
    calc g * m ^ 2 = (m * (m * g * m⁻¹) * m⁻¹) * m ^ 2 := by rw [h]
      _ = m ^ 2 * g := by rw [sq]; group
  obtain ⟨w, hw2, hwm⟩ := exists_sq_eq_one_mul_inv_mem_center hZ hm2
  have hβw : ∀ x, β x = w * x * w⁻¹ := by
    intro x
    rw [hβm]
    have hz := mem_center_iff.1 hwm (m * x * m⁻¹)
    calc m * x * m⁻¹ = (m * x * m⁻¹) * (w * m⁻¹) * (w * m⁻¹)⁻¹ := by group
      _ = (w * m⁻¹) * (m * x * m⁻¹) * (w * m⁻¹)⁻¹ := by rw [hz]
      _ = w * x * w⁻¹ := by group
  obtain ⟨w', hw'2, hw'C⟩ : ∃ w' : M, w' ^ 2 = 1 ∧ w' ∉ center M ∧
      ∀ x : M, w' * x = x * w' → t * (x : G) * t⁻¹ = x := by
    by_cases hw1 : w = 1
    · have hcentral : ∀ x : M, t * (x : G) * t⁻¹ = x := fun x => by
        have h1 : β x = x := by rw [hβw, hw1, one_mul, inv_one, mul_one]
        rw [← hβ, h1]
      obtain ⟨u, hu⟩ : ∃ u : adjointGroup .E6 k, orderOf u = 2 :=
        ⟨_, orderOf_pinnedX_one_adjointGroup (τ := .E6) (Pi.single (0 : Fin 6) 1)⟩
      obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (eM.symm u)
      have hm₀2 : m₀ ^ 2 ∈ center M := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hm₀, ← map_pow, ← hu,
          pow_orderOf_eq_one, map_one]
      obtain ⟨w₀, hw₀2, hw₀m⟩ := exists_sq_eq_one_mul_inv_mem_center hZ hm₀2
      refine ⟨w₀, hw₀2, fun hw₀Z => ?_, fun x _ => hcentral x⟩
      have h1 : (QuotientGroup.mk w₀ : M ⧸ center M) = 1 := (QuotientGroup.eq_one_iff _).2 hw₀Z
      rw [mk_eq_of_mul_inv_mem_center hw₀m, hm₀] at h1
      have hu1 : u = 1 := by rw [← eM.apply_symm_apply u, h1, map_one]
      rw [hu1, orderOf_one] at hu
      exact absurd hu (by norm_num)
    · refine ⟨w, hw2, fun hwZ => ?_, fun x hx => ?_⟩
      · have h := odd_orderOf_of_mem_center hZ hwZ
        rw [orderOf_eq_prime hw2 hw1] at h
        exact absurd h (by decide)
      · have h1 : β x = x := by rw [hβw, hx, mul_inv_cancel_right]
        rw [← hβ, h1]
  set ŵ : adjointGroup .E6 k := eM (QuotientGroup.mk w') with hŵdef
  have hŵ : orderOf ŵ = 2 := by
    refine orderOf_eq_prime ?_ fun h => hw'C.1 ?_
    · rw [hŵdef, ← map_pow, ← QuotientGroup.mk_pow, hw'2, QuotientGroup.mk_one, map_one]
    · rw [← QuotientGroup.eq_one_iff]
      apply eM.injective
      rw [map_one]
      exact h
  have hle : centralizer ({ŵ} : Set (adjointGroup .E6 k)) ≤
      (centralizer ({w'} : Set M)).map (eM.toMonoidHom.comp (QuotientGroup.mk' (center M))) := by
    intro c hc
    obtain ⟨q₁, hq₁⟩ := eM.surjective c
    obtain ⟨m₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    have hcom : (QuotientGroup.mk (w' * m₁) : M ⧸ center M) = QuotientGroup.mk (m₁ * w') := by
      apply eM.injective
      have h := mem_centralizer_singleton_iff.1 hc
      rw [← hq₁] at h
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul]
      exact h.symm
    obtain ⟨m', hm'w, hm'm⟩ := exists_commute_of_mk_commute hZ hw'2 hcom
    refine ⟨m', mem_centralizer_singleton_iff.2 hm'w.symm, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom]
    rw [mk_eq_of_mul_inv_mem_center hm'm, hq₁]
  have hleG : (centralizer ({w'} : Set M)).map M.subtype ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxw := mem_centralizer_singleton_iff.1 hx
    have h := hw'C.2 x hxw.symm
    rw [mem_centralizer_singleton_iff]
    change (x : G) * t = t * x
    calc (x : G) * t = t * (x : G) * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  refine ⟨(centralizer ({w'} : Set M)).map M.subtype, le_inf (map_subtype_le _) hleG, ?_⟩
  rw [card_map_of_injective M.subtype_injective]
  exact (two_pow_dvd_card_centralizer_E6 hk hŵ).trans
    ((card_dvd_of_le hle).trans (Subgroup.card_map_dvd _ _))

theorem dvd_card_inf_centralizer_of_outer_quot_E6 {M : Subgroup G}
    (hZ : Odd (Nat.card (center M))) {f : ℕ} (hf : 2 ≤ f) {k : Type} [Field k]
    (hk : Nat.card k = 2 ^ f) (eM : M ⧸ center M ≃* adjointGroup .E6 k) {t : G}
    (ht : orderOf t = 2) (htM : t ∈ normalizer (M : Set G))
    (hout : normalizerQuotMulAut eM ⟨t, htM⟩ ∉
      (MulAut.conj : adjointGroup .E6 k →* MulAut (adjointGroup .E6 k)).range) :
    2 ^ (20 * f) ∣ Nat.card (M ⊓ centralizer ({t} : Set G) : Subgroup G) ∨
      ∃ e' : ℕ, 1 ≤ e' ∧ f = 2 * e' ∧ ∃ D : ℕ, (D = ordE6 (2 ^ e') ∨ D = ordTwistedE6 (2 ^ e')) ∧
        D * Nat.card (perfectCore (M ⊓ centralizer ({t} : Set G)) ⊓
            (center M).map M.subtype : Subgroup G) ∣
          Nat.card (perfectCore (M ⊓ centralizer ({t} : Set G))) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hk
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hk
  have : Finite (adjointGroup .E6 k) := by
    have : Finite (ModGL Tag.E6 k) := finite_modGL
    infer_instance
  have hq : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set C := adjointGroup TwistTag.E6.tag k with hCdef
  set α : MulAut C := normalizerQuotMulAut eM ⟨t, htM⟩ with hαdef
  have hα2 : α ^ 2 = 1 := normalizerQuotMulAut_sq_eq_one eM ht htM
  set π₀ : M →* C := eM.toMonoidHom.comp (QuotientGroup.mk' (center M)) with hπ₀
  set Xm : Subgroup M := (centralizer ({t} : Set G)).subgroupOf M with hXm
  set X : Subgroup G := M ⊓ centralizer ({t} : Set G) with hXdef
  have hXmX : Xm.map M.subtype = X := by
    rw [hXm, subgroupOf_map_subtype, inf_comm]
  have hcardX : Nat.card Xm = Nat.card X := by
    rw [← hXmX, card_map_of_injective M.subtype_injective]
  have hfix : Xm.map π₀ = fixSubgroup α := map_subgroupOf_centralizer_eq_fixSubgroup hZ eM ht htM
  have hcardfix : Nat.card (fixSubgroup α) ∣ Nat.card X := by
    rw [← hfix, ← hcardX]
    exact Subgroup.card_map_dvd _ _
  have hPX : (perfectCore Xm).map M.subtype = perfectCore X := by
    rw [CFSG.Quasithin.map_perfectCore, hXmX]
  have hPfix : (perfectCore Xm).map π₀ = perfectCore (fixSubgroup α) := by
    rw [CFSG.Quasithin.map_perfectCore, hfix]
  have hkerπ : π₀.ker = center M := by
    ext x
    rw [MonoidHom.mem_ker]
    change eM (QuotientGroup.mk' (center M) x) = 1 ↔ x ∈ center M
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hPZ : Nat.card (perfectCore X) = Nat.card (perfectCore (fixSubgroup α)) *
      Nat.card (perfectCore X ⊓ (center M).map M.subtype : Subgroup G) := by
    rw [← hPX, card_map_of_injective M.subtype_injective, card_eq_card_map_mul_card_inf_ker π₀,
      hPfix, hkerπ, ← map_inf_eq _ _ _ M.subtype_injective,
      card_map_of_injective M.subtype_injective]
  have hDL : ∀ β₀ : MulAut C, ∀ φ, φ * α * φ⁻¹ = β₀ →
      (⁅⁅fixSubgroup β₀, fixSubgroup β₀⁆, ⁅fixSubgroup β₀, fixSubgroup β₀⁆⁆ : Subgroup C) =
        ⁅fixSubgroup β₀, fixSubgroup β₀⁆ →
      Nat.card (⁅fixSubgroup β₀, fixSubgroup β₀⁆ : Subgroup C) ∣
        Nat.card (perfectCore (fixSubgroup α)) := by
    rintro β₀ φ rfl hperf
    set D : Subgroup C := ⁅fixSubgroup α, fixSubgroup α⁆ with hD
    have hDφ : D.map φ.toMonoidHom = ⁅fixSubgroup (φ * α * φ⁻¹), fixSubgroup (φ * α * φ⁻¹)⁆ :=
      map_commutator_fixSubgroup_conj φ α
    have hDD : ⁅D, D⁆ = D := by
      apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      rw [map_commutator, hDφ, hperf]
    rw [← hDφ, card_map_of_injective φ.injective]
    exact card_dvd_of_le (CFSG.Quasithin.le_perfectCore_of_perfect
      (Subgroup.commutator_le_self _) hDD)
  have hgraph : ∀ β₀ : MulAut C, (∃ φ, φ * α * φ⁻¹ = β₀) →
      Nat.card k ^ 20 ∣ Nat.card (fixSubgroup β₀) →
      2 ^ (20 * f) ∣ Nat.card (M ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    rintro β₀ ⟨φ, rfl⟩ hdvd
    rw [card_fixSubgroup_conj, hk, ← pow_mul, mul_comm f 20] at hdvd
    exact hdvd.trans hcardfix
  have hfeven : ∀ σ : k ≃+* k, σ ^ 2 = 1 → σ ≠ 1 → ∃ e', 1 ≤ e' ∧ f = 2 * e' := by
    intro σ hσ2 hσ1
    obtain ⟨-, -, -, -, -, hfield⟩ :=
      ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) k
    obtain ⟨⟨r, hr⟩, -, -⟩ := hfield 2 f Nat.prime_two (by omega) hk σ hσ2 hσ1
    exact ⟨r, by omega, by omega⟩
  rcases outer_involution_cases_E6 (by omega : 1 ≤ f) k hk α hα2 hout with
    ⟨η, hη, ⟨φ, hφ⟩ | ⟨ht', φ, hφ⟩⟩ | ⟨σ, hσ2, hσ1, ⟨φ, hφ⟩ | ⟨φ, hφ⟩⟩
  · exact Or.inl (hgraph η ⟨φ, hφ⟩ (card_pow_twenty_dvd_card_fixSubgroup_graph_E6 hq η hη).1)
  · exact Or.inl (hgraph _ ⟨φ, hφ⟩ ((card_pow_twenty_dvd_card_fixSubgroup_graph_E6 hq η hη).2 ht'))
  · obtain ⟨e', he', hfe⟩ := hfeven σ hσ2 hσ1
    have hk' : Nat.card k = 2 ^ (2 * e') := by rw [hk, hfe]
    obtain ⟨hD, hperf, hcard⟩ := commutator_fixSubgroup_field_E6 he' hk' σ hσ2 hσ1
    have hdvd := hDL _ φ hφ (by rw [hD]; exact hperf)
    rw [hD, hcard] at hdvd
    refine Or.inr ⟨e', he', hfe, _, Or.inl rfl, ?_⟩
    rw [hPZ]
    exact mul_dvd_mul_right hdvd _
  · obtain ⟨e', he', hfe⟩ := hfeven σ hσ2 hσ1
    have hk' : Nat.card k = 2 ^ (2 * e') := by rw [hk, hfe]
    obtain ⟨hD, hperf, hcard⟩ := commutator_fixSubgroup_graphField_E6 he' hk' σ hσ2 hσ1
    have hdvd := hDL _ φ hφ (by rw [hD]; exact hperf)
    rw [hD, hcard] at hdvd
    refine Or.inr ⟨e', he', hfe, _, Or.inr rfl, ?_⟩
    rw [hPZ]
    exact mul_dvd_mul_right hdvd _

theorem exists_le_inf_centralizer_E6_factor {M : Subgroup G} (hMp : ⁅M, M⁆ = M)
    (hZ : Odd (Nat.card (center M))) {f : ℕ} (hf : 2 ≤ f) {k : Type} [Field k]
    (hk : Nat.card k = 2 ^ f) (eM : M ⧸ center M ≃* adjointGroup .E6 k) {t : G}
    (ht : orderOf t = 2) (htM : t ∈ normalizer (M : Set G)) :
    ∃ X : Subgroup G, X ≤ M ⊓ centralizer ({t} : Set G) ∧
      (2 ^ (20 * f) ∣ Nat.card X ∨
        ∃ e' : ℕ, 1 ≤ e' ∧ f = 2 * e' ∧ ⁅X, X⁆ = X ∧
          ∃ D : ℕ, (D = ordE6 (2 ^ e') ∨ D = ordTwistedE6 (2 ^ e')) ∧
            D * Nat.card (X ⊓ (center M).map M.subtype : Subgroup G) ∣ Nat.card X) := by
  by_cases hin : normalizerQuotMulAut eM ⟨t, htM⟩ ∈
      (MulAut.conj : adjointGroup .E6 k →* MulAut (adjointGroup .E6 k)).range
  · obtain ⟨X, hX, hXc⟩ := exists_le_inf_centralizer_of_inner_quot_E6 hMp hZ hk eM ht htM hin
    exact ⟨X, hX, Or.inl ((pow_dvd_pow 2 (by omega)).trans hXc)⟩
  · rcases dvd_card_inf_centralizer_of_outer_quot_E6 hZ hf hk eM ht htM hin with h | h
    · exact ⟨_, le_rfl, Or.inl h⟩
    · obtain ⟨e', he', hfe, D, hD, hdvd⟩ := h
      have := F4Pilot.finite_of_natCard_eq_two_pow hk
      exact ⟨_, CFSG.Quasithin.perfectCore_le _, Or.inr ⟨e', he', hfe,
        CFSG.Quasithin.perfectCore_perfect _, D, hD, hdvd⟩⟩

end Factor

end CFSG.SeitzReduction.E6Pilot
