module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionFusion
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionC1
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionOrder

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms

section Index

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem natCard_sup_zpowers_le {t : G} (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G)) :
    Nat.card (L ⊔ zpowers t : Subgroup G) ≤ 2 * Nat.card L := by
  classical
  have hmem : ∀ x : (L ⊔ zpowers t : Subgroup G), (x : G) ∉ L → t⁻¹ * (x : G) ∈ L := by
    intro x hx
    obtain ⟨y, hyL, hy⟩ := F4Pilot.exists_eq_or_eq_mul_of_mem_sup_zpowers ht htC x.2
    rcases hy with hy | hy
    · exact absurd (hy ▸ hyL) hx
    · rw [hy, inv_mul_cancel_left]
      exact hyL
  let φ : (L ⊔ zpowers t : Subgroup G) → L × Bool := fun x =>
    if hx : (x : G) ∈ L then (⟨x, hx⟩, false) else (⟨t⁻¹ * x, hmem x hx⟩, true)
  have hφ : Function.Injective φ := by
    intro x y hxy
    by_cases hx : (x : G) ∈ L <;> by_cases hy : (y : G) ∈ L <;>
      simp only [φ, hx, hy, dite_true, dite_false, Prod.mk.injEq, Bool.false_eq_true,
        Bool.true_eq_false, and_false, and_true, Subtype.mk.injEq] at hxy
    · exact Subtype.ext hxy
    · exact Subtype.ext (mul_left_cancel hxy)
  have h := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
  linarith

theorem natCard_le_two_mul_card_outer_mul_card_inf {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ≤ centralizer ({t} : Set G)) :
    Nat.card H ≤ 2 * Nat.card (Outer L) * Nat.card (H ⊓ L : Subgroup G) := by
  classical
  have htC : t ∈ centralizer (L : Set G) :=
    (hKt ▸ mem_zpowers t : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).1
  set π : H →* Outer L :=
    (QuotientGroup.mk' (inner L)).comp (L.normalizerMonoidHom.comp (inclusion (hH.trans hCN)))
    with hπ
  have hker : ∀ d : H, π d = 1 → (d : G) ∈ L ⊔ zpowers t := by
    intro d hd
    rw [hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hd
    obtain ⟨l, hl⟩ := hd
    refine F4Pilot.mem_sup_zpowers_of_conj_eq htC ht hKt (hH d.2) l.2 fun y hy => ?_
    have := congrArg (fun σ : MulAut L => ((σ ⟨y, hy⟩ : L) : G)) hl
    simpa [MulAut.conj_apply] using this.symm
  set N : Subgroup G := π.ker.map H.subtype with hNdef
  have hNM : N ≤ L ⊔ zpowers t := by
    rintro _ ⟨d, hd, rfl⟩
    exact hker d hd
  have hNH : N ≤ H := map_subtype_le _
  have hcardN : Nat.card N = Nat.card π.ker := card_map_of_injective H.subtype_injective
  have hrange : Nat.card π.range ≤ Nat.card (Outer L) := Subgroup.card_le_card_group _
  have hM := natCard_sup_zpowers_le ht htC
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := L ⊔ zpowers t)
  rw [inf_eq_left.2 le_sup_left] at h1
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have hLM : L.relIndex (L ⊔ zpowers t) ≤ 2 := by nlinarith
  have hLM0 : L.relIndex (L ⊔ zpowers t) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact (Nat.card_pos (α := (L ⊔ zpowers t : Subgroup G))).ne' h1.symm
  have hLN : L.relIndex N ≤ 2 := (Subgroup.relIndex_le_of_le_right hNM hLM0).trans hLM
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := N)
  have h3 : Nat.card (L ⊓ N : Subgroup G) ≤ Nat.card (H ⊓ L : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf (inf_le_right.trans hNH) inf_le_left)
  have h4 := card_ker_mul_card_range π
  have hN2 : Nat.card N ≤ 2 * Nat.card (H ⊓ L : Subgroup G) := by
    rw [← h2]
    exact Nat.mul_le_mul hLN h3
  calc Nat.card H = Nat.card π.ker * Nat.card π.range := h4.symm
    _ ≤ (2 * Nat.card (H ⊓ L : Subgroup G)) * Nat.card (Outer L) :=
        Nat.mul_le_mul (hcardN ▸ hN2) hrange
    _ = 2 * Nat.card (Outer L) * Nat.card (H ⊓ L : Subgroup G) := by ring

end Index


section Field

variable {K : Type} [Field K]

theorem natCard_outer_adjointGroup_E7 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    Nat.card (Outer (adjointGroup .E7 K)) = f := by
  obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK .E7 (Or.inl rfl)
  have hinner : inner (adjointGroup .E7 K) = Θ.ker := hker.symm
  let φ : Outer (adjointGroup .E7 K) ≃* (K ≃+* K) :=
    (QuotientGroup.quotientMulEquivOfEq hinner).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  rw [Nat.card_congr φ.toEquiv, hcard]

theorem natCard_le_of_isPGroup_of_forall_fixed_E7 {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    {P : Subgroup (adjointGroup .E7 K)} (hP : IsPGroup 2 P)
    (hPfix : ∀ p ∈ P, entrywiseAdjointAut .E7 σ p = p) : Nat.card P ≤ 2 ^ (63 * e) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  obtain ⟨-, hk, -, hfix, -⟩ :=
    even_E7_E8_canonical_field_full_centralizer .E7 (Or.inl rfl) he K hK σ hσ
  have hrange : P ≤ (fixedFieldInclusion (τ := .E7) σ).range := by
    intro p hp
    have h1 : (p : ModGL .E7 K) ∈ ((entrywiseAdjointAut .E7 σ).toMonoidHom.eqLocus
        (MonoidHom.id _)).map (adjointGroup .E7 K).subtype := ⟨p, hPfix p hp, rfl⟩
    rw [hfix] at h1
    obtain ⟨g, hg⟩ := (mem_fixedFieldImage_iff_exists σ p).1 h1
    exact ⟨g, hg⟩
  set Q := P.comap (fixedFieldInclusion (τ := .E7) σ) with hQdef
  have hQ : Q.map (fixedFieldInclusion (τ := .E7) σ) = P := map_comap_eq_self hrange
  have hcard : Nat.card Q = Nat.card P := by
    rw [← hQ, card_map_of_injective (fixedFieldInclusion_injective σ)]
  have hQp : IsPGroup 2 Q := hP.comap_of_injective _ (fixedFieldInclusion_injective σ)
  have h := natCard_le_of_isPGroup_E7 hQp
  rw [hcard, hk, ← pow_mul, mul_comm] at h
  exact h

end Field

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem two_mul_two_mul_two_pow_lt {e : ℕ} (he : 1 ≤ e) :
    2 * (2 * e) * 2 ^ (63 * e) < 2 ^ (66 * e) := by
  have h1 : e < 2 ^ e := Nat.lt_two_pow_self
  have h2 : 4 * 2 ^ e ≤ 2 ^ (3 * e) := by
    calc 4 * 2 ^ e = 2 ^ (e + 2) := by rw [pow_add]; ring
      _ ≤ 2 ^ (3 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < 2 ^ (63 * e) := by positivity
  calc 2 * (2 * e) * 2 ^ (63 * e) = 4 * e * 2 ^ (63 * e) := by ring
    _ < 4 * 2 ^ e * 2 ^ (63 * e) := by
        apply Nat.mul_lt_mul_of_pos_right _ hpos
        omega
    _ ≤ 2 ^ (3 * e) * 2 ^ (63 * e) := Nat.mul_le_mul_right _ h2
    _ = 2 ^ (66 * e) := by rw [← pow_add]; ring_nf

theorem conj_inv_not_mem_sup_zpowers_E7 (hset : StandardSetting G L) {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ (2 * e)) (eL : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {g : G}
    (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) (hsL : g⁻¹ * t * g ∉ L ⊔ zpowers t) :
    g * t * g⁻¹ ∉ L ⊔ zpowers t := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  obtain ⟨σ, hσ⟩ := EPilot.exists_ringEquiv_apply_eq_pow_two_pow he hK
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht
  have hss : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt, mul_one, inv_mul_cancel]
  have ht'C : g * t * g⁻¹ ∈ centralizer ({t} : Set G) :=
    F4Pilot.conj_inv_mem_centralizer_singleton hsC
  have ht't : g * t * g⁻¹ * t = t * (g * t * g⁻¹) := mem_centralizer_singleton_iff.1 ht'C
  have ht't' : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  intro hmem
  obtain ⟨w, hwL, hw⟩ := F4Pilot.exists_eq_or_eq_mul_of_mem_sup_zpowers ht htC hmem
  have hw2 : orderOf w = 2 := by
    rcases hw with hw | hw
    · rw [← hw]
      have e1 : g * t * g⁻¹ = MulAut.conj g t := rfl
      rw [e1, MulEquiv.orderOf_eq, ht]
    · have hw' : w = t * (g * t * g⁻¹) := by rw [hw, ← mul_assoc, htt, one_mul]
      have hw1 : w ≠ 1 := by
        intro h1
        apply hsL
        have h2 : g * t * g⁻¹ = t := by rw [hw, h1, mul_one]
        have hs : g⁻¹ * t * g = t := by
          calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h2]
            _ = t := by group
        rw [hs]
        exact mem_sup_right (mem_zpowers t)
      have hsq : w ^ 2 = 1 := by
        rw [sq, hw']
        calc t * (g * t * g⁻¹) * (t * (g * t * g⁻¹)) =
              t * ((g * t * g⁻¹) * t) * (g * t * g⁻¹) := by group
          _ = t * (t * (g * t * g⁻¹)) * (g * t * g⁻¹) := by rw [ht't]
          _ = (t * t) * ((g * t * g⁻¹) * (g * t * g⁻¹)) := by group
          _ = 1 := by rw [htt, ht't', one_mul]
      exact orderOf_eq_prime hsq hw1
  have hw2C : orderOf (eL ⟨w, hwL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hw2]
  obtain ⟨P₀, hP₀2, hP₀c, hP₀card⟩ := exists_isPGroup_le_centralizer_E7 hw2C
  set P : Subgroup G := (P₀.map eL.symm.toMonoidHom).map L.subtype with hPdef
  set P₁ : Subgroup G := P.map (MulAut.conj g⁻¹).toMonoidHom with hP₁def
  have hPL : P ≤ L := map_subtype_le _
  have hPw : ∀ p ∈ P, p * w = w * p := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have hc : a * eL ⟨w, hwL⟩ = eL ⟨w, hwL⟩ * a := mem_centralizer_singleton_iff.1 (hP₀c ha)
    have h1 : eL.symm a * ⟨w, hwL⟩ = ⟨w, hwL⟩ * eL.symm a := by
      apply eL.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hc
    exact congrArg Subtype.val h1
  have hPt : ∀ p ∈ P, p * t = t * p := fun p hp => mem_centralizer_iff.1 htC p (hPL hp)
  have hPt' : ∀ p ∈ P, p * (g * t * g⁻¹) = (g * t * g⁻¹) * p := by
    intro p hp
    rcases hw with hw | hw
    · rw [hw]
      exact hPw p hp
    · rw [hw]
      calc p * (t * w) = (p * t) * w := by group
        _ = (t * p) * w := by rw [hPt p hp]
        _ = t * (p * w) := by group
        _ = t * (w * p) := by rw [hPw p hp]
        _ = t * w * p := by group
  have hP₁t : P₁ ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h := hPt' p hp
    calc g⁻¹ * p * g * t = g⁻¹ * (p * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * p) * g := by rw [h]
      _ = t * (g⁻¹ * p * g) := by group
  have hP₁s : P₁ ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h := hPt p hp
    calc g⁻¹ * p * g * (g⁻¹ * t * g) = g⁻¹ * (p * t) * g := by group
      _ = g⁻¹ * (t * p) * g := by rw [h]
      _ = g⁻¹ * t * g * (g⁻¹ * p * g) := by group
  have hP₁card : Nat.card K ^ 33 ≤ Nat.card P₁ := by
    rw [hP₁def, card_map_of_injective (MulAut.conj g⁻¹).injective, hPdef,
      card_map_of_injective L.subtype_injective, card_map_of_injective eL.symm.injective]
    exact hP₀card
  have hP₁2 : IsPGroup 2 P₁ := ((hP₀2.map _).map _).map _
  have hidx := natCard_le_two_mul_card_outer_mul_card_inf ht hKt hCN hP₁t
  have hout : Nat.card (Outer L) = 2 * e := by
    rw [Nat.card_congr (equivalence eL).toEquiv, natCard_outer_adjointGroup_E7 (by omega) hK]
  obtain ⟨ε, hε⟩ := F4Pilot.exists_mulEquiv_conj_eq hset eL
    (fun α hα hαo => E8Pilot.exists_conj_eq_entrywise_of_outer_E7_E8 (Or.inl rfl) he K hK σ hσ
      hα hαo) ht hKt hsC hss hsL
  set R : Subgroup (adjointGroup .E7 K) := ((P₁ ⊓ L).subgroupOf L).map ε.toMonoidHom with hRdef
  have hRcard : Nat.card R = Nat.card (P₁ ⊓ L : Subgroup G) := by
    rw [hRdef, card_map_of_injective ε.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have hR2 : IsPGroup 2 R :=
    ((hP₁2.to_le inf_le_left).comap_of_injective L.subtype L.subtype_injective).map _
  have hRfix : ∀ r ∈ R, entrywiseAdjointAut .E7 σ r = r := by
    rintro _ ⟨a, ha, rfl⟩
    have haP : (a : G) ∈ P₁ := (mem_subgroupOf.1 ha).1
    have hsa : (a : G) = g⁻¹ * t * g * a * (g⁻¹ * t * g)⁻¹ := by
      have h := mem_centralizer_singleton_iff.1 (hP₁s haP)
      calc (a : G) = a * (g⁻¹ * t * g) * (g⁻¹ * t * g)⁻¹ := by group
        _ = g⁻¹ * t * g * a * (g⁻¹ * t * g)⁻¹ := by rw [h]
    exact (hε a a hsa).symm
  have hRle := natCard_le_of_isPGroup_of_forall_fixed_E7 he hK σ hσ hR2 hRfix
  rw [hRcard] at hRle
  rw [hout] at hidx
  have hq : Nat.card K ^ 33 = 2 ^ (66 * e) := by
    rw [hK, ← pow_mul]
    ring_nf
  have hle : 2 ^ (66 * e) ≤ 2 * (2 * e) * 2 ^ (63 * e) :=
    calc 2 ^ (66 * e) = Nat.card K ^ 33 := hq.symm
      _ ≤ Nat.card P₁ := hP₁card
      _ ≤ 2 * (2 * e) * Nat.card (P₁ ⊓ L : Subgroup G) := hidx
      _ ≤ 2 * (2 * e) * 2 ^ (63 * e) := Nat.mul_le_mul_left _ hRle
  exact absurd hle (not_le.2 (two_mul_two_mul_two_pow_lt he))

end Standard

section Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem outerFusionTwoCentral_of_even_E7 (hset : StandardSetting G L) {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ (2 * e)) (eL : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    F4Pilot.OuterFusionTwoCentral L t := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  obtain ⟨σ, hσ⟩ := EPilot.exists_ringEquiv_apply_eq_pow_two_pow he hK
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨2, derivedSeries_outer_eq_bot_of_mulEquiv eL (exceptional_E_pinned_model_Schreier K).2.1⟩⟩
  exact outerFusionTwoCentral_of_twoCentralTwistedFusion_of_outer hset hOut eL
    (fun α hα hαo => E8Pilot.exists_conj_eq_entrywise_of_outer_E7_E8 (Or.inl rfl) he K hK σ hσ
      hα hαo)
    (twoCentralTwistedFusion_field_E7 he hK σ hσ) ht hKt
    (fun _ hsC hsL => conj_inv_not_mem_sup_zpowers_E7 hset he hK eL ht hKt hsC hsL)

theorem outerFusionTwoCentral_E7 (hset : StandardSetting G L) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (eL : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    F4Pilot.OuterFusionTwoCentral L t := by
  rcases Nat.even_or_odd' f with ⟨e, rfl | rfl⟩
  · exact outerFusionTwoCentral_of_even_E7 hset (by omega) hK eL ht hKt
  · exact outerFusionTwoCentral_of_odd_E7 hset hf ⟨e, rfl⟩ hK eL ht hKt

theorem exists_conj_eq_mul_twoCentral_E7 (hset : StandardSetting G L) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (eL : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ g : G, g⁻¹ * t * g ∉ L) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u :=
  exists_conj_eq_mul_twoCentral_E7_of_outerFusion hset hf hK eL ht hKt hnot
    (outerFusionTwoCentral_E7 hset hf hK eL ht hKt)

end Assembly

end CFSG.SeitzReduction.E7Pilot
