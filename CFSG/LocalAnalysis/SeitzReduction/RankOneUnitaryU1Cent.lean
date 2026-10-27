module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section General

theorem exists_commutator_eq_of_regular {Ω : Type*} [Finite Ω] {E : Subgroup (Equiv.Perm Ω)}
    (hreg : ∀ a b : Ω, ∃! x : E, (x : Equiv.Perm Ω) a = b) {c : Equiv.Perm Ω}
    (hcE : c ∈ normalizer (E : Set (Equiv.Perm Ω))) {ω₀ : Ω} (hc0 : c ω₀ = ω₀)
    (hcfix : ∀ ω, c ω = ω → ω = ω₀) {e : Equiv.Perm Ω} (he : e ∈ E) :
    ∃ e' ∈ E, e = c * e' * c⁻¹ * e'⁻¹ := by
  have hconj : ∀ x ∈ E, c * x * c⁻¹ ∈ E := fun x hx => (mem_normalizer_iff.mp hcE x).mp hx
  let ψ : E → E := fun x => ⟨c * x * c⁻¹ * (x : Equiv.Perm Ω)⁻¹,
    mul_mem (hconj x x.2) (inv_mem x.2)⟩
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : c * (x : Equiv.Perm Ω) * c⁻¹ * (x : Equiv.Perm Ω)⁻¹ =
        c * (y : Equiv.Perm Ω) * c⁻¹ * (y : Equiv.Perm Ω)⁻¹ := congrArg Subtype.val hxy
    set g : Equiv.Perm Ω := (y : Equiv.Perm Ω)⁻¹ * x with hg
    have hgE : g ∈ E := mul_mem (inv_mem y.2) x.2
    have hgc : c * g = g * c := by
      have h3 : g * c⁻¹ = c⁻¹ * g := by
        rw [hg]
        calc (y : Equiv.Perm Ω)⁻¹ * x * c⁻¹ = (y : Equiv.Perm Ω)⁻¹ * c⁻¹ *
              (c * (x : Equiv.Perm Ω) * c⁻¹ * (x : Equiv.Perm Ω)⁻¹) * x := by group
          _ = (y : Equiv.Perm Ω)⁻¹ * c⁻¹ *
              (c * (y : Equiv.Perm Ω) * c⁻¹ * (y : Equiv.Perm Ω)⁻¹) * x := by rw [h1]
          _ = c⁻¹ * ((y : Equiv.Perm Ω)⁻¹ * x) := by group
      calc c * g = c * (g * c⁻¹) * c := by group
        _ = c * (c⁻¹ * g) * c := by rw [h3]
        _ = g * c := by group
    have hfix : g ω₀ = ω₀ := by
      apply hcfix
      rw [← Equiv.Perm.mul_apply, hgc, Equiv.Perm.mul_apply, hc0]
    obtain ⟨z, -, hz⟩ := hreg ω₀ ω₀
    have hg1 : (⟨g, hgE⟩ : E) = 1 := by
      rw [hz ⟨g, hgE⟩ hfix, hz 1 rfl]
    have hg1' : g = 1 := congrArg Subtype.val hg1
    apply Subtype.ext
    have : (y : Equiv.Perm Ω) * ((y : Equiv.Perm Ω)⁻¹ * x) = y := by rw [← hg, hg1', mul_one]
    simpa using this
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨e, he⟩
  exact ⟨x, x.2, (congrArg Subtype.val hx).symm⟩

theorem conj_pow_eq_mul_pow_of_conj {G : Type*} [Group G] {k r a : G} (hkr : k * r * k⁻¹ = r * a)
    (hka : k * a * k⁻¹ = a) (n : ℕ) : k ^ n * r * (k ^ n)⁻¹ = r * a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hkan : k * a ^ n * k⁻¹ = a ^ n := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hka]
    calc k ^ (n + 1) * r * (k ^ (n + 1))⁻¹ = k * (k ^ n * r * (k ^ n)⁻¹) * k⁻¹ := by
          rw [pow_succ']; group
      _ = (k * r * k⁻¹) * (k * a ^ n * k⁻¹) := by rw [ih]; group
      _ = r * a ^ (n + 1) := by rw [hkr, hkan, pow_succ']; group

end General

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_odd_torus_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ k ∈ L, k ∈ centralizer (szA₁ (szT₁ L T) : Set G) ∧ (∃ b : ℕ, Odd b ∧ k ^ b = 1) ∧
      ∀ x ∈ szT₁ L T, k * x * k⁻¹ * x⁻¹ ∈ szA₁ (szT₁ L T) → x ∈ szA₁ (szT₁ L T) := by
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hcore⟩ := hB.exists_benderCore Q
  have he2 : 2 ≤ e := by
    have := h.two_le
    cases hB with
    | unitary n hn e' => exact two_le_unitary_e hn
  obtain ⟨d, hd, hd1⟩ : ∃ d ∈ fixCartan (Q : Subgroup L) t₀, d ≠ 1 := by
    by_contra hall
    push Not at hall
    have : fixCartan (Q : Subgroup L) t₀ = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (hall x hx)
    have h1 := hcore.card_fixCartan
    rw [this, card_bot] at h1
    omega
  have hdD : d ∈ cartan (Q : Subgroup L) t₀ := fixCartan_le_cartan _ _ hd
  have hA₁L : ∀ x ∈ szA₁ (szT₁ L T), x ∈ L := fun x hx => szT₁_le_right L T (szA₁_le _ hx)
  have hdC : (d : G) ∈ centralizer (szA₁ (szT₁ L T) : Set G) := by
    refine mem_centralizer_iff.mpr fun z hz => ?_
    by_cases hz1 : z = 1
    · rw [hz1, one_mul, mul_one]
    have hzZ : (⟨z, hA₁L z hz⟩ : L) ∈ rootCenter (Q : Subgroup L) := (hmemZ _).mpr hz
    have hz1' : (⟨z, hA₁L z hz⟩ : L) ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
    rw [← hcore.cartan_inf_centralizer_eq hzZ hz1'] at hd
    have := mem_centralizer_singleton_iff.mp (mem_inf.mp hd).2
    exact (congrArg Subtype.val this).symm
  refine ⟨d, d.2, hdC, ⟨Nat.card (cartan (Q : Subgroup L) t₀), hcore.odd_card_cartan, ?_⟩, ?_⟩
  · have h1 : d ^ Nat.card (cartan (Q : Subgroup L) t₀) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hdD)
    have h2 := congrArg Subtype.val h1
    simpa using h2
  · intro x hx hdx
    have hxL : x ∈ L := szT₁_le_right L T hx
    have hfpf := hB.fixedPointFree_unitary Q hcore.sq_eq_one hcore.not_mem hdD hd1
      ((hmemQ ⟨x, hxL⟩).mpr hx) ((hmemZ _).mpr (by simpa using hdx))
    exact (hmemZ _).mp hfpf

section Certificates

theorem torus_facts_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {k : G} (hkL : k ∈ L)
    (hkC : k ∈ centralizer (szA₁ (szT₁ L T) : Set G)) (hkodd : ∃ b : ℕ, Odd b ∧ k ^ b = 1) :
    k ∈ normalizer (szR (szT₁ L T) R₂ t : Set G) ∧ k ∈ normalizer (szT₁ L T : Set G) ∧
      k * t = t * k ∧ k ∈ centralizer (R₂ : Set G) ∧
      (R₂ ⊔ zpowers t).map (MulAut.conj k).toMonoidHom = R₂ ⊔ zpowers t := by
  obtain ⟨-, -, -, hNR₁, hNR₂, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hkA : k ∈ centralizer (szA L T t : Set G) :=
    h.mem_centralizer_szA_of_mem_centralizer_szA₁ hkL hkC
  have hkN : k ∈ normalizer (szA L T t : Set G) := centralizer_le_normalizer _ hkA
  have hkt : k * t = t * k := mem_centralizer_iff.mp h.mem k hkL
  have hkR₂ : k ∈ normalizer (R₂ : Set G) := hNR₂ hkN
  refine ⟨hNR₁ hkN, h.normalizer_szA_le_of_card_sylow hS2 hkN, hkt, ?_, ?_⟩
  · obtain ⟨b, hb, hkb⟩ := hkodd
    refine mem_centralizer_iff.mpr fun r hr => ?_
    have hr' : k * r * k⁻¹ ∈ R₂ := (mem_normalizer_iff.mp hkR₂ r).mp hr
    have hkt' : k⁻¹ * t = t * k⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hkt, mul_inv_cancel_right]
    have hρk : (r * t * r⁻¹ * t) * k = k * (r * t * r⁻¹ * t) :=
      mem_centralizer_iff.mp hkC _ (hR.rho_mem r hr)
    have hρ : (k * r * k⁻¹) * t * (k * r * k⁻¹)⁻¹ * t = r * t * r⁻¹ * t := by
      have h1 := U3R2.rho_conj (t := t) (D := k⁻¹) (u := r) hkt'
      simp only [inv_inv] at h1
      rw [h1, ← hρk, mul_inv_cancel_right]
    have h1 : r * t * r⁻¹ = (k * r * k⁻¹) * t * (k * r * k⁻¹)⁻¹ := by
      rw [hR.conj_t_eq r, hR.conj_t_eq (k * r * k⁻¹), hρ]
    have ha : r⁻¹ * (k * r * k⁻¹) ∈ szA₁ (szT₁ L T) := by
      refine hR.rho_ker _ (mul_mem (inv_mem hr) hr') ?_
      calc r⁻¹ * (k * r * k⁻¹) * t =
          r⁻¹ * ((k * r * k⁻¹) * t * (k * r * k⁻¹)⁻¹) * (k * r * k⁻¹) := by group
        _ = r⁻¹ * (r * t * r⁻¹) * (k * r * k⁻¹) := by rw [← h1]
        _ = t * (r⁻¹ * (k * r * k⁻¹)) := by group
    set a := r⁻¹ * (k * r * k⁻¹) with ha_def
    have hkr : k * r * k⁻¹ = r * a := by rw [ha_def]; group
    have hka : k * a * k⁻¹ = a := by
      rw [← mem_centralizer_iff.mp hkC a ha, mul_inv_cancel_right]
    have hpow := conj_pow_eq_mul_pow_of_conj hkr hka b
    rw [hkb, one_mul, inv_one, mul_one] at hpow
    have hab : a ^ b = 1 := by
      have h2 := congrArg (fun x => r⁻¹ * x) hpow
      simp only [inv_mul_cancel, inv_mul_cancel_left] at h2
      exact h2.symm
    have ha1 : a = 1 := by
      obtain ⟨j, rfl⟩ := hb
      rw [pow_succ, pow_mul, hR.sq_A₁ a ha, one_pow, one_mul] at hab
      exact hab
    have h3 : k * r * k⁻¹ = r := by rw [hkr, ha1, mul_one]
    calc r * k = k * r * k⁻¹ * k := by rw [h3]
      _ = k * r := by group
  · rw [map_conj_sup_zpowers hkR₂, hkt, mul_inv_cancel_right]

theorem eq_of_map_conj_torus_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {k : G} (hkL : k ∈ L)
    (hkC : k ∈ centralizer (szA₁ (szT₁ L T) : Set G))
    (hkfpf : ∀ x ∈ szT₁ L T, k * x * k⁻¹ * x⁻¹ ∈ szA₁ (szT₁ L T) → x ∈ szA₁ (szT₁ L T))
    {X : Subgroup G} (hX : X ∈ u3Omega L T R₂ t)
    (hkX : X.map (MulAut.conj k).toMonoidHom = X) : X = R₂ ⊔ zpowers t := by
  obtain ⟨-, -, -, -, hNR₂, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hkA : k ∈ centralizer (szA L T t : Set G) :=
    h.mem_centralizer_szA_of_mem_centralizer_szA₁ hkL hkC
  have hkN : k ∈ normalizer (szA L T t : Set G) := centralizer_le_normalizer _ hkA
  have hkT : k ∈ normalizer (szT₁ L T : Set G) := h.normalizer_szA_le_of_card_sylow hS2 hkN
  have hkt : k * t = t * k := mem_centralizer_iff.mp h.mem k hkL
  obtain ⟨q, rfl⟩ := h.u3Omega_subset_range_of_card_sylow hS2 hR hX
  induction q using QuotientGroup.induction_on with | H w => ?_
  rw [u3OmegaPoint_mk] at hkX ⊢
  rw [map_conj_sup_zpowers (hNR₂ hkN)] at hkX
  have hkwT : k * w * k⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hkT w).mp w.2
  have h4 : u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁
        (QuotientGroup.mk ⟨k * w * k⁻¹, hkwT⟩) =
      u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁ (QuotientGroup.mk w) := by
    rw [u3OmegaPoint_mk, u3OmegaPoint_mk]
    change R₂ ⊔ zpowers (k * w * k⁻¹ * t) = R₂ ⊔ zpowers ((w : G) * t)
    rw [← hkX, show k * (w : G) * k⁻¹ * t = k * ((w : G) * t) * k⁻¹ by
      calc k * (w : G) * k⁻¹ * t = k * (w : G) * k⁻¹ * (k * t * k⁻¹) := by
            rw [hkt, mul_inv_cancel_right]
        _ = k * ((w : G) * t) * k⁻¹ := by group]
  have h5 := h.u3OmegaPoint_injective_of_card_sylow hS2 hR h4
  rw [QuotientGroup.eq, mem_subgroupOf] at h5
  have hb : (w : G)⁻¹ * (k * w * k⁻¹) ∈ szA₁ (szT₁ L T) := by
    have := inv_mem h5
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] using this
  have hwb : (w : G) * ((w : G)⁻¹ * (k * w * k⁻¹)) = ((w : G)⁻¹ * (k * w * k⁻¹)) * w :=
    mem_centralizer_iff.mp (mem_szA₁.mp hb).2 w w.2
  have h6 : k * w * k⁻¹ * (w : G)⁻¹ ∈ szA₁ (szT₁ L T) := by
    have e : k * w * k⁻¹ * (w : G)⁻¹ = (w : G)⁻¹ * (k * w * k⁻¹) := by
      calc k * w * k⁻¹ * (w : G)⁻¹ =
          (w : G) * ((w : G)⁻¹ * (k * w * k⁻¹)) * (w : G)⁻¹ := by group
        _ = ((w : G)⁻¹ * (k * w * k⁻¹)) * w * (w : G)⁻¹ := by rw [hwb]
        _ = (w : G)⁻¹ * (k * w * k⁻¹) := by group
    rw [e]
    exact hb
  have hwA := hkfpf w w.2 h6
  rw [hR.t_comm w w.2, sup_zpowers_mul_eq (hR.le hwA)]

theorem u3U₁_facts_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b) :
    normalizer (szR (szT₁ L T) R₂ t : Set G) ≤
        normalizer ((u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) : Subgroup G) : Set G) ∧
      szT₁ L T ⊔ R₂ ≤ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) ∧
      t ∉ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) ∧
      u3U L T R₂ t E = (u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)) ⊔ zpowers t ∧
      (u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)) ⊓ szR (szT₁ L T) R₂ t = szT₁ L T ⊔ R₂ ∧
      ∀ w ∈ szT₁ L T, ∃ u ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), ∃ r ∈ R₂,
        u * t * u⁻¹ = r * w * t := by
  obtain ⟨-, -, -, hNR₁'⟩ := h.char_of_card_sylow hS2 hR
  set Y := normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) with hY
  set U := u3U L T R₂ t E with hU
  set U₁ := U ⊓ centralizer (R₂ : Set G) with hU₁
  have hYR₂ : Y ≤ normalizer (R₂ : Set G) := fun y hy => (mem_inf.mp (hNR₁' hy)).2
  have hUY : U ≤ Y := u3U_le_normalizer L T R₂ t E
  have hYU : Y ≤ normalizer (U : Set G) := le_normalizer_u3U hEn
  have hR₁U : szR (szT₁ L T) R₂ t ≤ U := h.szR_le_u3U_of_card_sylow hS2 hR E
  have hHR₁ : szT₁ L T ⊔ R₂ ≤ szR (szT₁ L T) R₂ t := sup_le (le_szR_left _ _ _) (le_szR_mid _ _ _)
  have hHC : szT₁ L T ⊔ R₂ ≤ centralizer (R₂ : Set G) := by
    refine sup_le (fun y hy => mem_centralizer_iff.mpr fun r hr => (hR.commT₁ y hy r hr).symm) ?_
    exact fun r hr => mem_centralizer_iff.mpr fun r' hr' => hR.comm r' hr' r hr
  have hHU₁ : szT₁ L T ⊔ R₂ ≤ U₁ := le_inf (hHR₁.trans hR₁U) hHC
  have htC : t ∉ centralizer (R₂ : Set G) := by
    intro htC
    obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
    obtain ⟨b, hb, hb1⟩ : ∃ b ∈ szA₁ (szT₁ L T), b ≠ 1 := by
      by_contra hall
      push Not at hall
      have : szA₁ (szT₁ L T) = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (hall x hx)
      rw [this, card_bot] at hA₁card
      have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.two_le; omega)
      omega
    obtain ⟨r, hr, hrb⟩ := hR.rho_onto b hb
    apply hb1
    rw [← hrb, mem_centralizer_iff.mp htC r hr, mul_inv_cancel_right, ← sq, hR.t_sq]
  obtain ⟨k, hkL, hkC, hkodd, hkfpf⟩ := h.exists_odd_torus_of_card_sylow hS2
  obtain ⟨hkY, -, -, hkR₂, hk0⟩ := h.torus_facts_of_card_sylow hS2 hR hkL hkC hkodd
  set c := u3OmegaAction L T R₂ t ⟨k, hkY⟩ with hcdef
  have hcE : c ∈ normalizer (E : Set (Equiv.Perm (u3Omega L T R₂ t))) := by
    refine mem_normalizer_iff.mpr fun e => ⟨fun he => ?_, fun he => ?_⟩
    · have hn := hEn.conj_mem ⟨e, hE he⟩ (mem_subgroupOf.mpr he)
        ⟨c, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
      rw [mem_subgroupOf] at hn
      simpa using hn
    · have hn := hEn.conj_mem ⟨c * e * c⁻¹, hE he⟩ (mem_subgroupOf.mpr he)
        ⟨c⁻¹, inv_mem (MonoidHom.mem_range.mpr ⟨_, rfl⟩)⟩
      rw [mem_subgroupOf] at hn
      simpa [mul_assoc] using hn
  have hc0 : c ⟨R₂ ⊔ zpowers t, sup_zpowers_mem_u3Omega L T R₂ t⟩ =
      ⟨R₂ ⊔ zpowers t, sup_zpowers_mem_u3Omega L T R₂ t⟩ :=
    Subtype.ext (by rw [hcdef, u3OmegaAction_apply]; exact hk0)
  have hcfix : ∀ ω, c ω = ω → ω = ⟨R₂ ⊔ zpowers t, sup_zpowers_mem_u3Omega L T R₂ t⟩ := by
    intro ω hω
    apply Subtype.ext
    refine h.eq_of_map_conj_torus_of_card_sylow hS2 hR hkL hkC hkfpf ω.2 ?_
    have := congrArg Subtype.val hω
    rwa [hcdef, u3OmegaAction_apply] at this
  have hdecomp : ∀ u ∈ U, ∃ u₁ ∈ U₁, ∃ z ∈ zpowers t, u = u₁ * z := by
    intro u hu
    obtain ⟨huY, huE⟩ := mem_u3U.mp hu
    obtain ⟨e', he'E, he'⟩ := exists_commutator_eq_of_regular hEreg hcE hc0 hcfix huE
    obtain ⟨⟨u', hu'Y⟩, rfl⟩ := hE he'E
    have hu'U : u' ∈ U := mem_u3U.mpr ⟨hu'Y, he'E⟩
    obtain ⟨v, hv⟩ : ∃ v : G, v = k * u' * k⁻¹ * u'⁻¹ := ⟨_, rfl⟩
    have hvU : v ∈ U := by
      rw [hv]
      exact mul_mem ((mem_normalizer_iff.mp (hYU hkY) u').mp hu'U) (inv_mem hu'U)
    have hvY : v ∈ Y := hUY hvU
    have hvC : v ∈ centralizer (R₂ : Set G) := by
      refine mem_centralizer_iff.mpr fun r hr => ?_
      have hr₁ : u'⁻¹ * r * u' ∈ R₂ := (mem_normalizer_iff''.mp (hYR₂ hu'Y) r).mp hr
      have hk1 : (u'⁻¹ * r * u') * k = k * (u'⁻¹ * r * u') := mem_centralizer_iff.mp hkR₂ _ hr₁
      have hk2 : r * k = k * r := mem_centralizer_iff.mp hkR₂ r hr
      have hk1' : (u'⁻¹ * r * u') * k⁻¹ = k⁻¹ * (u'⁻¹ * r * u') := by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hk1, mul_inv_cancel_right]
      rw [hv]
      calc r * (k * u' * k⁻¹ * u'⁻¹) = (r * k) * u' * k⁻¹ * u'⁻¹ := by group
        _ = k * u' * ((u'⁻¹ * r * u') * k⁻¹) * u'⁻¹ := by rw [hk2]; group
        _ = k * u' * (k⁻¹ * (u'⁻¹ * r * u')) * u'⁻¹ := by rw [hk1']
        _ = (k * u' * k⁻¹ * u'⁻¹) * r := by group
    have hact : u3OmegaAction L T R₂ t ⟨v, hvY⟩ = u3OmegaAction L T R₂ t ⟨u, huY⟩ := by
      have e : (⟨v, hvY⟩ : Y) =
          ⟨k, hkY⟩ * ⟨u', hu'Y⟩ * (⟨k, hkY⟩ : Y)⁻¹ * (⟨u', hu'Y⟩ : Y)⁻¹ := Subtype.ext hv
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact he'.symm
    have hvuY : v⁻¹ * u ∈ Y := mul_mem (inv_mem hvY) huY
    have hvu : v⁻¹ * u ∈ szR (szT₁ L T) R₂ t := by
      refine h.mem_szR_of_forall_map_conj_eq_of_card_sylow hS2 hR hc hΩ hvuY fun X hX => ?_
      have h1 : u3OmegaAction L T R₂ t ⟨v⁻¹ * u, hvuY⟩ = 1 := by
        have e : (⟨v⁻¹ * u, hvuY⟩ : Y) = (⟨v, hvY⟩ : Y)⁻¹ * ⟨u, huY⟩ := rfl
        rw [e, map_mul, map_inv, hact, inv_mul_cancel]
      have h3 := congrArg (fun σ : Equiv.Perm (u3Omega L T R₂ t) =>
        ((σ ⟨X, hX⟩ : u3Omega L T R₂ t) : Subgroup G)) h1
      simpa [u3OmegaAction_apply] using h3
    obtain ⟨w, hw, z, hz, hwz⟩ := exists_mul_of_mem_szR hR hvu
    refine ⟨v * w, ⟨mul_mem hvU (hR₁U (hHR₁ hw)), mul_mem hvC (hHC hw)⟩, z, hz, ?_⟩
    calc u = v * (v⁻¹ * u) := by group
      _ = v * w * z := by rw [← hwz, ← mul_assoc]
  have hUeq : U = U₁ ⊔ zpowers t := by
    refine le_antisymm (fun u hu => ?_) (sup_le inf_le_left
      (zpowers_le.mpr (hR₁U (mem_szR_right _ _ _))))
    obtain ⟨u₁, hu₁, z, hz, rfl⟩ := hdecomp u hu
    exact mul_mem (mem_sup_left hu₁) (mem_sup_right hz)
  refine ⟨?_, hHU₁, fun ht => htC (mem_inf.mp ht).2, hUeq, ?_, ?_⟩
  ·
    intro y hy
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ⟨?_, ?_⟩
    · exact (mem_normalizer_iff''.mp (hYU hy) x).mp (mem_inf.mp hx).1
    · refine mem_centralizer_iff.mpr fun r hr => ?_
      have hyr : y * r * y⁻¹ ∈ R₂ := (mem_normalizer_iff.mp (hYR₂ hy) r).mp hr
      have h1 := mem_centralizer_iff.mp (mem_inf.mp hx).2 _ hyr
      calc r * (y⁻¹ * x * y) = y⁻¹ * ((y * r * y⁻¹) * x) * y := by group
        _ = y⁻¹ * (x * (y * r * y⁻¹)) * y := by rw [h1]
        _ = y⁻¹ * x * y * r := by group
  ·
    refine le_antisymm (fun x hx => ?_) (le_inf hHU₁ hHR₁)
    obtain ⟨hxU₁, hxR₁⟩ := mem_inf.mp hx
    obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_szR hR hxR₁
    rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
    · rw [hz1, mul_one]
      exact hw
    · exfalso
      rw [hz1] at hxU₁
      apply htC
      have := mul_mem (inv_mem (hHC hw)) (mem_inf.mp hxU₁).2
      rwa [inv_mul_cancel_left] at this
  ·
    intro w hw
    obtain ⟨u, hu, r, hr, hut⟩ := h.exists_mem_u3U_conj_eq_of_card_sylow hS2 hR hΩ hE hEreg hw
    obtain ⟨u₁, hu₁, z, hz, rfl⟩ := hdecomp u hu
    refine ⟨u₁, hu₁, r, hr, ?_⟩
    have hzt : z * t * z⁻¹ = t := by
      rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
      · rw [hz1]; group
      · rw [hz1]; group
    rw [← hut]
    calc u₁ * t * u₁⁻¹ = u₁ * (z * t * z⁻¹) * u₁⁻¹ := by rw [hzt]
      _ = u₁ * z * t * (u₁ * z)⁻¹ := by group

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
