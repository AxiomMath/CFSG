module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Tight

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

structure IsTight {G : Type} [Group G] (L : Subgroup G) (s : G) : Prop where
  order : orderOf s = 4
  mem : s ∈ normalizer (L : Set G)
  inter : ∀ y ∈ zpowers s, y ∈ centralizer (L : Set G) → y = 1
  cent : ∀ x : G, x * s ^ 2 = s ^ 2 * x → x * s * x⁻¹ ∈ zpowers s

structure FourHyp (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : G) : Prop where
  std : StdHyp G L
  card_center : Nat.card (center L) = 2
  out : (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index ∣ 2
  centerless : center (L ⧸ center L) = ⊥
  facts : TightCoverFacts L
  order : orderOf f = 4
  cent : centralizer (L : Set G) = zpowers f
  zent : (center L).map L.subtype = zpowers (f ^ 2)
  norm : centralizer ({f ^ 2} : Set G) = normalizer (L : Set G)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : G}

namespace FourHyp

theorem sq_center (H : FourHyp G L f) : ∀ z ∈ center L, z ^ 2 = 1 := by
  intro c hc
  have h2 : orderOf (⟨c, hc⟩ : center L) ∣ 2 := H.card_center ▸ orderOf_dvd_natCard _
  simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 h2)

theorem exists_center_gen (H : FourHyp G L f) :
    ∃ τ : L, τ ∈ center L ∧ (τ : G) = f ^ 2 := by
  have hf2 : f ^ 2 ∈ (center L).map L.subtype := H.zent ▸ mem_zpowers _
  obtain ⟨τ, hτZ, hτ⟩ := hf2
  exact ⟨τ, hτZ, hτ⟩

theorem eq_one_or_eq_sq (H : FourHyp G L f) {c : G} (hc : c ∈ centralizer (L : Set G))
    (hcc : c * c = 1) : c = 1 ∨ c = f ^ 2 :=
  eq_one_or_eq_sq_of_mem_zpowers H.order (H.cent ▸ hc) hcc

theorem tight_u (H : FourHyp G L f) {s : G} (hs : IsTight L s) :
    ∃ u : L, (u : G) = s ^ 2 ∧ u * u = 1 ∧ u ∉ center L ∧
      orderOf (u : L ⧸ center L) = 2 ∧
      normalizerAction L ⟨s, hs.mem⟩ * normalizerAction L ⟨s, hs.mem⟩ =
        MulAut.conj (u : L ⧸ center L) ∧
      ∀ q ∈ centralizer ({(u : L ⧸ center L)} : Set (L ⧸ center L)), Odd (orderOf q) →
        normalizerAction L ⟨s, hs.mem⟩ q = q := by
  have hs44 : s ^ 4 = 1 := by rw [← hs.order]; exact pow_orderOf_eq_one s
  have hs2s2 : s ^ 2 * s ^ 2 = 1 := by rw [← pow_add]; exact hs44
  obtain ⟨zL, c, hcC, hzc, hcomm, hzz, hzcen, hzbar, hφ2, hφfix⟩ :=
    H.std.tight_phi H.sq_center H.out hs.order hs.mem hs.inter hs.cent
  obtain ⟨hlift, -⟩ := H.facts _ hzbar ⟨_, hφ2, hφfix⟩
  have hzL1 : (zL : G) * (zL : G) = 1 := by
    have := congrArg Subtype.val (hlift zL rfl)
    simpa using this
  have hcc : c * c = 1 := by
    have h1 : (zL : G) * c * ((zL : G) * c) = 1 := by rw [hzc]; exact hs2s2
    calc c * c = ((zL : G) * (zL : G)) * (c * c) := by rw [hzL1, one_mul]
      _ = (zL : G) * ((zL : G) * c) * c := by group
      _ = (zL : G) * (c * (zL : G)) * c := by rw [hcomm.eq]
      _ = (zL : G) * c * ((zL : G) * c) := by group
      _ = 1 := h1
  obtain ⟨τ, hτZ, hτ⟩ := H.exists_center_gen
  obtain ⟨u, hu, hu'⟩ : ∃ u : L, (u : G) = s ^ 2 ∧
      (u : L ⧸ center L) = (zL : L ⧸ center L) := by
    rcases H.eq_one_or_eq_sq hcC hcc with h1 | h1
    · exact ⟨zL, by rw [← hzc, h1, mul_one], rfl⟩
    · refine ⟨zL * τ, ?_, ?_⟩
      · show (zL : G) * (τ : G) = s ^ 2
        rw [← hzc, h1, hτ]
      · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff τ).2 hτZ, mul_one]
  have huu : u * u = 1 := hlift u hu'
  refine ⟨u, hu, huu, ?_, by rw [hu']; exact hzbar, by rw [hu']; exact hφ2,
    by rw [hu']; exact hφfix⟩
  intro hucen
  have h1 : (u : L ⧸ center L) = 1 := (QuotientGroup.eq_one_iff u).2 hucen
  rw [hu', ← orderOf_eq_one_iff] at h1
  rw [hzbar] at h1
  omega

omit [Finite G] in
theorem mul_inv_mem_centralizer_of_action_eq (hL : commutator L = ⊤) {a b : G}
    (ha : a ∈ normalizer (L : Set G)) (hb : b ∈ normalizer (L : Set G))
    (h : normalizerAction L ⟨a, ha⟩ = normalizerAction L ⟨b, hb⟩) :
    a * b⁻¹ ∈ centralizer (L : Set G) := by
  have h1 : normalizerAction L ((⟨a, ha⟩ : normalizer (L : Set G)) * ⟨b, hb⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  exact (normalizerAction_eq_one_iff hL _).1 h1

omit [Finite G] in
theorem mul_mem_centralizer_of_action_eq_inv (hL : commutator L = ⊤) {a b : G}
    (ha : a ∈ normalizer (L : Set G)) (hb : b ∈ normalizer (L : Set G))
    (h : normalizerAction L ⟨a, ha⟩ = (normalizerAction L ⟨b, hb⟩)⁻¹) :
    a * b ∈ centralizer (L : Set G) := by
  have h1 : normalizerAction L ((⟨a, ha⟩ : normalizer (L : Set G)) * ⟨b, hb⟩) = 1 := by
    rw [map_mul, h, inv_mul_cancel]
  exact (normalizerAction_eq_one_iff hL _).1 h1

theorem tight_comparison (H : FourHyp G L f) {s s' : G} (hs : IsTight L s) (hs' : IsTight L s')
    (hss' : s' ^ 2 = s ^ 2 ∨ s' ^ 2 = s ^ 2 * f ^ 2) :
    ∃ c ∈ centralizer (L : Set G), s' = c * s ∨ s' = c * s⁻¹ := by
  have hL : commutator L = ⊤ := H.std.standard.1.1
  obtain ⟨u, hu, -, -, hubar, hφ2, hφfix⟩ := H.tight_u hs
  obtain ⟨u', hu', -, -, -, hφ2', hφfix'⟩ := H.tight_u hs'
  obtain ⟨τ, hτZ, hτ⟩ := H.exists_center_gen
  have hbar : (u' : L ⧸ center L) = (u : L ⧸ center L) := by
    rcases hss' with h1 | h1
    · have : u' = u := Subtype.ext (by rw [hu, hu', h1])
      rw [this]
    · have : u' = u * τ := Subtype.ext (by
        show (u' : G) = (u : G) * (τ : G)
        rw [hu, hu', h1, hτ])
      rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff τ).2 hτZ, mul_one]
  obtain ⟨-, w, -, huniq, -⟩ := H.facts _ hubar ⟨_, hφ2, hφfix⟩
  have h1 := huniq _ hφ2 hφfix
  have h2 := huniq _ (by rw [← hbar]; exact hφ2') (by rw [← hbar]; exact hφfix')
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact ⟨s' * s⁻¹, mul_inv_mem_centralizer_of_action_eq hL hs'.mem hs.mem (h2.trans h1.symm),
      Or.inl (by group)⟩
  · refine ⟨s' * s, mul_mem_centralizer_of_action_eq_inv hL hs'.mem hs.mem ?_, Or.inr (by group)⟩
    rw [h2, h1, map_inv]
  · refine ⟨s' * s, mul_mem_centralizer_of_action_eq_inv hL hs'.mem hs.mem ?_, Or.inr (by group)⟩
    rw [h2, h1, map_inv, inv_inv]
  · exact ⟨s' * s⁻¹, mul_inv_mem_centralizer_of_action_eq hL hs'.mem hs.mem (h2.trans h1.symm),
      Or.inl (by group)⟩

theorem commute_of_mem_centralizer_of_mem_sup (H : FourHyp G L f) {c : G}
    (hc : c ∈ centralizer (L : Set G)) {s : G} (hs : s ∈ L ⊔ centralizer (L : Set G)) :
    c * s = s * c := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer le_rfl hs
  have hca : c * a = a * c := (mem_centralizer_iff.1 hc a ha).symm
  have hcb : c * b = b * c := by
    rw [H.cent] at hc hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hc
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
    exact ((Commute.zpow_zpow_self f i j).eq)
  calc c * (a * b) = (c * a) * b := by group
    _ = a * (c * b) := by rw [hca]; group
    _ = a * (b * c) := by rw [hcb]
    _ = a * b * c := by group

theorem tight_core (H : FourHyp G L f) {s : G} (hs : IsTight L s) :
    ∃ (u x p ŵ : L) (c : G), (u : G) = s ^ 2 ∧ u * u = 1 ∧ u ∉ center L ∧
      c ∈ centralizer (L : Set G) ∧ c * c = f ^ 2 ∧ s = (ŵ : G) * c ∧
      x = p * u * p⁻¹ ∧ x * x = 1 ∧ (x : G) * s * (x : G)⁻¹ = s⁻¹ := by
  have hL : commutator L = ⊤ := H.std.standard.1.1
  obtain ⟨u, hu, huu, hucen, hubar, hφ2, hφfix⟩ := H.tight_u hs
  obtain ⟨hlift, w, hww, huniq, x0, p, hx0x0, hx0comm, hx0w, hx0p, hx0wl⟩ :=
    H.facts _ hubar ⟨_, hφ2, hφfix⟩
  set φ : MulAut (L ⧸ center L) := normalizerAction L ⟨s, hs.mem⟩ with hφdef
  have hφw := huniq φ hφ2 hφfix
  have hsLC : s ∈ L ⊔ centralizer (L : Set G) := by
    refine (normalizerAction_mem_range_conj_iff hL ⟨s, hs.mem⟩).1 ?_
    rcases hφw with h | h
    · exact ⟨w, h.symm⟩
    · exact ⟨w⁻¹, h.symm⟩
  obtain ⟨a, haL, c, hcC, hsac⟩ := exists_mul_of_mem_sup_of_le_centralizer le_rfl hsLC
  set ŵ : L := ⟨a, haL⟩ with hŵdef
  have hŵc : (ŵ : G) * c = c * (ŵ : G) := mem_centralizer_iff.1 hcC ŵ ŵ.2
  have hφŵ : φ = MulAut.conj (ŵ : L ⧸ center L) := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | _ y =>
      have hcy : (y : G) * c = c * (y : G) := mem_centralizer_iff.1 hcC y y.2
      have hy : ((ŵ * y * ŵ⁻¹ : L) : G) = s * (y : G) * s⁻¹ := by
        rw [hsac]
        show a * (y : G) * a⁻¹ = a * c * (y : G) * (a * c)⁻¹
        calc a * (y : G) * a⁻¹ = a * (c * (y : G)) * c⁻¹ * a⁻¹ := by
              rw [← hcy]; group
          _ = a * c * (y : G) * (a * c)⁻¹ := by group
      rw [hφdef, normalizerAction_apply ⟨s, hs.mem⟩ y (ŵ * y * ŵ⁻¹) hy]
      simp [MulAut.conj_apply]
  have hinj := HypOne.conj_injective_of_center_eq_bot H.centerless
  have hŵw : (ŵ : L ⧸ center L) = w ∨ (ŵ : L ⧸ center L) = w⁻¹ := by
    rcases hφw with h | h
    · left; exact hinj (hφŵ.symm.trans h)
    · right; exact hinj (hφŵ.symm.trans h)

  have hx1 : x0⁻¹ = x0 := inv_eq_of_mul_eq_one_right hx0x0
  have hw2 : w ≠ w⁻¹ := by
    intro hwinv
    have h1 : (u : L ⧸ center L) = 1 := by
      rw [← hww]
      calc w * w = w * w⁻¹ := by rw [← hwinv]
        _ = 1 := mul_inv_cancel w
    rw [h1, orderOf_one] at hubar
    omega
  have hx0w' : (x0 : L ⧸ center L) * w⁻¹ * (x0 : L ⧸ center L)⁻¹ = w := by
    calc (x0 : L ⧸ center L) * w⁻¹ * (x0 : L ⧸ center L)⁻¹
        = ((x0 : L ⧸ center L) * w * (x0 : L ⧸ center L)⁻¹)⁻¹ := by group
      _ = w := by rw [hx0w, inv_inv]
  have hx0wl' : ∀ l : L, (l : L ⧸ center L) = w⁻¹ → x0 * l * (x0 * l) ≠ 1 := by
    intro l hl hcon
    apply hx0wl l⁻¹ (by rw [QuotientGroup.mk_inv, hl, inv_inv])
    have e1 : l * x0 * l = x0 := by
      calc l * x0 * l = x0⁻¹ * (x0 * l * (x0 * l)) := by group
        _ = x0⁻¹ := by rw [hcon, mul_one]
        _ = x0 := hx1
    have e2 : l⁻¹ * x0 * l⁻¹ = x0 := by
      calc l⁻¹ * x0 * l⁻¹ = l⁻¹ * (l * x0 * l) * l⁻¹ := by rw [e1]
        _ = x0 := by group
    calc x0 * l⁻¹ * (x0 * l⁻¹) = x0 * (l⁻¹ * x0 * l⁻¹) := by group
      _ = x0 * x0 := by rw [e2]
      _ = 1 := hx0x0
  have hx0ŵ : x0 * ŵ * (x0 * ŵ) ≠ 1 := by
    rcases hŵw with h | h
    · exact hx0wl ŵ h
    · exact hx0wl' ŵ h
  have hŵ2 : (ŵ : L ⧸ center L) ≠ (ŵ : L ⧸ center L)⁻¹ := by
    rcases hŵw with h | h
    · rw [h]; exact hw2
    · rw [h, inv_inv]; exact fun h' => hw2 h'.symm
  set x : L := p * u * p⁻¹ with hxdef
  have hxx : x * x = 1 := by
    calc x * x = p * (u * u) * p⁻¹ := by rw [hxdef]; group
      _ = 1 := by rw [huu]; group
  have hxbar : (x : L ⧸ center L) = (x0 : L ⧸ center L) := by
    rw [hx0p, hxdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  obtain ⟨k, hk, hxk⟩ : ∃ k ∈ center L, x = x0 * k := by
    refine ⟨x0⁻¹ * x, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxbar,
      inv_mul_cancel]
  have hk2 : k * k = 1 := by
    have := H.sq_center k hk
    rwa [sq] at this
  have hkc : ∀ l : L, l * k = k * l := fun l => mem_center_iff.1 hk l
  have hxu : x * u = u * x := by
    rw [hxk]
    calc x0 * k * u = x0 * (k * u) := by group
      _ = x0 * (u * k) := by rw [← hkc u]
      _ = (x0 * u) * k := by group
      _ = (u * x0) * k := by rw [hx0comm u rfl]
      _ = u * (x0 * k) := by group
  have hxs2 : (x : G) * s ^ 2 = s ^ 2 * (x : G) := by
    rw [← hu]; exact congrArg Subtype.val hxu
  have hxxG : (x : G) * (x : G) = 1 := by
    have := congrArg Subtype.val hxx
    simpa using this
  have hxinv : (x : G)⁻¹ = (x : G) := inv_eq_of_mul_eq_one_right hxxG
  have hxc : (x : G) * c = c * (x : G) := mem_centralizer_iff.1 hcC x x.2
  have hsŵ : s = (ŵ : G) * c := hsac
  have hconj : (x : G) * s * (x : G)⁻¹ = ((x : G) * (ŵ : G) * (x : G)⁻¹) * c := by
    rw [hsŵ, hxinv]
    calc (x : G) * ((ŵ : G) * c) * (x : G) = (x : G) * (ŵ : G) * (c * (x : G)) := by group
      _ = (x : G) * (ŵ : G) * ((x : G) * c) := by rw [← hxc]
      _ = ((x : G) * (ŵ : G) * (x : G)) * c := by group
  have hmem := hs.cent (x : G) hxs2
  have hs2ne : s ^ 2 ≠ 1 := fun h2 => by
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hs.order] at this
    omega
  have hsq : ((x : G) * s * (x : G)⁻¹) * ((x : G) * s * (x : G)⁻¹) = s ^ 2 := by
    calc ((x : G) * s * (x : G)⁻¹) * ((x : G) * s * (x : G)⁻¹) = (x : G) * (s * s) * (x : G)⁻¹ := by
          group
      _ = s ^ 2 := by rw [← sq, hxs2]; group
  have hxŵ : (x : L ⧸ center L) * (ŵ : L ⧸ center L) * (x : L ⧸ center L)⁻¹ =
      (ŵ : L ⧸ center L)⁻¹ := by
    rw [hxbar]
    rcases hŵw with h | h
    · rw [h]; exact hx0w
    · rw [h, inv_inv]; exact hx0w'
  have hcm : Commute (ŵ : G) c := hŵc
  rcases eq_or_eq_inv_of_mem_zpowers_of_sq_ne_one hs.order hmem
      (by rw [hsq]; exact hs2ne) with h1 | h1
  · exfalso
    have h2 : (x : G) * (ŵ : G) * (x : G)⁻¹ = (ŵ : G) := by
      apply mul_right_cancel (b := c)
      rw [← hconj, h1, ← hsŵ]
    have h3 : x * ŵ * x⁻¹ = ŵ := Subtype.ext (by simpa using h2)
    have h4 : (x : L ⧸ center L) * (ŵ : L ⧸ center L) * (x : L ⧸ center L)⁻¹ =
        (ŵ : L ⧸ center L) := by
      have := congrArg (fun y : L => (y : L ⧸ center L)) h3
      simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using this
    exact hŵ2 (h4.symm.trans hxŵ)
  · refine ⟨u, x, p, ŵ, c, hu, huu, hucen, hcC, ?_, hsac, hxdef, hxx, h1⟩
    have h2 : (x : G) * (ŵ : G) * (x : G)⁻¹ = (ŵ : G)⁻¹ * (c⁻¹ * c⁻¹) := by
      have h3 : ((x : G) * (ŵ : G) * (x : G)⁻¹) * c = (ŵ : G)⁻¹ * c⁻¹ * c⁻¹ * c := by
        rw [← hconj, h1, hsŵ, mul_inv_rev, ← hcm.inv_inv.eq]
        group
      exact mul_right_cancel (by rw [h3]; group)
    have h5 : ((x * ŵ : L) : G) * ((x * ŵ : L) : G) = c⁻¹ * c⁻¹ := by
      show (x : G) * (ŵ : G) * ((x : G) * (ŵ : G)) = c⁻¹ * c⁻¹
      have hcm2 : Commute (ŵ : G) (c⁻¹ * c⁻¹) := (hcm.inv_right).mul_right (hcm.inv_right)
      calc (x : G) * (ŵ : G) * ((x : G) * (ŵ : G))
          = ((x : G) * (ŵ : G) * (x : G)⁻¹) * (ŵ : G) := by rw [hxinv]; group
        _ = (ŵ : G)⁻¹ * (c⁻¹ * c⁻¹) * (ŵ : G) := by rw [h2]
        _ = (ŵ : G)⁻¹ * ((c⁻¹ * c⁻¹) * (ŵ : G)) := by group
        _ = (ŵ : G)⁻¹ * ((ŵ : G) * (c⁻¹ * c⁻¹)) := by rw [← hcm2.eq]
        _ = c⁻¹ * c⁻¹ := by group
    have hne : x * ŵ * (x * ŵ) ≠ 1 := by
      have e1 : k * ŵ = ŵ * k := (hkc ŵ).symm
      have e2 : k * x0 = x0 * k := (hkc x0).symm
      have : x * ŵ * (x * ŵ) = (x0 * ŵ * (x0 * ŵ)) * (k * k) := by
        rw [hxk]
        calc x0 * k * ŵ * (x0 * k * ŵ) = x0 * (k * ŵ) * (x0 * (k * ŵ)) := by group
          _ = x0 * (ŵ * k) * (x0 * (ŵ * k)) := by rw [e1]
          _ = x0 * ŵ * (k * x0) * (ŵ * k) := by group
          _ = x0 * ŵ * (x0 * k) * (ŵ * k) := by rw [e2]
          _ = x0 * ŵ * x0 * (k * ŵ) * k := by group
          _ = x0 * ŵ * x0 * (ŵ * k) * k := by rw [e1]
          _ = (x0 * ŵ * (x0 * ŵ)) * (k * k) := by group
      rw [this, hk2, mul_one]
      exact hx0ŵ
    have hcc1 : c * c ≠ 1 := by
      intro hcc1
      apply hne
      apply Subtype.ext
      have h6 : (((x * ŵ * (x * ŵ) : L)) : G) = c⁻¹ * c⁻¹ := by
        rw [Subgroup.coe_mul]; exact h5
      rw [h6, ← mul_inv_rev, hcc1, inv_one]
      rfl
    have hc4 : c ^ 4 = 1 := by
      have h6 : orderOf c ∣ 4 := H.order ▸ orderOf_dvd_of_mem_zpowers (H.cent ▸ hcC)
      exact orderOf_dvd_iff_pow_eq_one.1 h6
    have hcc4 : c * c * (c * c) = 1 := by
      rw [← hc4, show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    exact (H.eq_one_or_eq_sq (mul_mem hcC hcC) hcc4).resolve_left hcc1

end FourHyp

end CFSG.EvenSporadicStandard.TwoHS
