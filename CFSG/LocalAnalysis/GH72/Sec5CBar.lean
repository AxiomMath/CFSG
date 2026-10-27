module

public import CFSG.LocalAnalysis.GH72.Sec5CTools

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] {H : Subgroup G}

theorem mk_eq_one_iff (x : H) : (QuotientGroup.mk x : Bar H) = 1 ↔ (x : G) ∈ O H := by
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]

theorem bar_eq_bot_iff {L : Subgroup G} : bar H L = ⊥ ↔ L ⊓ H ≤ O H := by
  rw [bar, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  constructor
  · rintro h x ⟨hxL, hxH⟩
    exact ⟨⟨x, hxH⟩, h hxL, rfl⟩
  · intro h x hx
    obtain ⟨y, hy, hyx⟩ := h ⟨hx, x.2⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]

theorem bar_inf_left (L : Subgroup G) : bar H (H ⊓ L) = bar H L := by
  rw [bar, inf_subgroupOf_left]
  rfl

theorem isPGroup_bar_of_isPGroup {p : ℕ} {L : Subgroup G} (hL : IsPGroup p L) :
    IsPGroup p (bar H L) :=
  (hL.comap_subtype (K := H)).map _

theorem card_subgroupOf_dvd (L : Subgroup G) : Nat.card (L.subgroupOf H) ∣ Nat.card L := by
  have h1 : Nat.card (L.subgroupOf H) = Nat.card (L ⊓ H : Subgroup G) := by
    rw [← subgroupOf_map_subtype, card_map_of_injective H.subtype_injective]
  rw [h1]
  exact card_dvd_of_le inf_le_left

theorem odd_card_bar {L : Subgroup G} (hL : Odd (Nat.card L)) : Odd (Nat.card (bar H L)) :=
  hL.of_dvd_nat ((card_map_dvd _ _).trans (card_subgroupOf_dvd L))

theorem bar_mulEquiv {L : Subgroup G} (hL : L ≤ H) (hLO : L ⊓ O H = ⊥) :
    Nonempty (bar H L ≃* L) := by
  set K : Subgroup H := L.subgroupOf H with hKdef
  set φ : K →* Bar H := (QuotientGroup.mk' (CFSG.oddCore H)).comp K.subtype with hφdef
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hxL⟩ hx
    have hx' : (QuotientGroup.mk x : Bar H) = 1 := hx
    rw [mk_eq_one_iff] at hx'
    have : (x : G) ∈ L ⊓ O H := ⟨hxL, hx'⟩
    rw [hLO, mem_bot] at this
    exact (mem_bot).mpr (Subtype.ext (Subtype.ext this))
  have hrange : φ.range = bar H L := by
    rw [hφdef, MonoidHom.range_comp, range_subtype]
    rfl
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((MonoidHom.ofInjective hinj).symm.trans (subgroupOfEquivOfLe hL))⟩

theorem card_bar_of_inf_eq_bot {L : Subgroup G} (hL : L ≤ H) (hLO : L ⊓ O H = ⊥) :
    Nat.card (bar H L) = Nat.card L := by
  obtain ⟨e⟩ := bar_mulEquiv hL hLO
  exact Nat.card_congr e.toEquiv

theorem nonempty_bar_mulEquiv {L : Type*} [Group L] {N₀ ON : Subgroup G} (f : N₀ →* L)
    (hf : Function.Surjective f) (hker : f.ker = ON.subgroupOf N₀) (hcov : Covers H N₀ ON)
    (hONn : N₀ ≤ normalizer (ON : Set G)) (hOH : O H ⊓ N₀ = H ⊓ N₀ ⊓ ON) :
    Nonempty (bar H N₀ ≃* L) := by
  set B : Subgroup G := H ⊓ N₀ with hBdef
  set g : B →* L := f.comp (inclusion (inf_le_right : B ≤ N₀)) with hgdef
  set h : B →* Bar H :=
    (QuotientGroup.mk' (CFSG.oddCore H)).comp (inclusion (inf_le_left : B ≤ H)) with hhdef
  have hgs : Function.Surjective g := by
    intro l
    obtain ⟨⟨n, hn⟩, rfl⟩ := hf l
    obtain ⟨x, hx, o, ho, rfl⟩ := hcov.exists_mul hONn hn
    have hxN : x ∈ N₀ := hx.2
    have hoN : o ∈ N₀ := by
      have := N₀.mul_mem (N₀.inv_mem hxN) hn
      simpa using this
    refine ⟨⟨x, hx.1, hxN⟩, ?_⟩
    have hok : (⟨o, hoN⟩ : N₀) ∈ f.ker := by rw [hker]; exact ho
    have e : (⟨x * o, hn⟩ : N₀) = ⟨x, hxN⟩ * ⟨o, hoN⟩ := rfl
    rw [e, map_mul, (MonoidHom.mem_ker).mp hok, mul_one]
    rfl
  have hker' : h.ker = g.ker := by
    ext ⟨b, hbH, hbN⟩
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have h1 : h ⟨b, hbH, hbN⟩ = 1 ↔ b ∈ O H := mk_eq_one_iff ⟨b, hbH⟩
    have h2 : g ⟨b, hbH, hbN⟩ = 1 ↔ b ∈ ON := by
      change f ⟨b, hbN⟩ = 1 ↔ b ∈ ON
      rw [← MonoidHom.mem_ker, hker]
      rfl
    rw [h1, h2]
    constructor
    · intro hb
      have : b ∈ O H ⊓ N₀ := ⟨hb, hbN⟩
      rw [hOH] at this
      exact this.2
    · intro hb
      have : b ∈ H ⊓ N₀ ⊓ ON := ⟨⟨hbH, hbN⟩, hb⟩
      rw [← hOH] at this
      exact this.1
  have hrange : h.range = bar H N₀ := by
    rw [hhdef, MonoidHom.range_comp, inclusion_range, hBdef, inf_subgroupOf_left]
    rfl
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange h).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker').trans
      (QuotientGroup.quotientKerEquivOfSurjective g hgs)))⟩

theorem nonempty_bar_mulEquiv_of_covers {L : Type*} [Group L] {K W N₀ ON : Subgroup G}
    (f : N₀ →* L) (hf : Function.Surjective f) (hker : f.ker = ON.subgroupOf N₀) (hWK : W ≤ K)
    (hWN₀ : W ≤ N₀) (hWcov : Covers W N₀ ON) (hONn : N₀ ≤ normalizer (ON : Set G))
    (hWO : O K ⊓ W = W ⊓ ON) : Nonempty (bar K W ≃* L) := by
  set g : W →* L := f.comp (inclusion hWN₀) with hgdef
  have hgs : Function.Surjective g := by
    intro l
    obtain ⟨⟨n, hn⟩, rfl⟩ := hf l
    obtain ⟨w, hw, o, ho, rfl⟩ := hWcov.exists_mul hONn hn
    have hwN : w ∈ N₀ := hw.2
    have hoN : o ∈ N₀ := by
      have := N₀.mul_mem (N₀.inv_mem hwN) hn
      simpa using this
    refine ⟨⟨w, hw.1⟩, ?_⟩
    have hok : (⟨o, hoN⟩ : N₀) ∈ f.ker := by rw [hker]; exact ho
    have e : (⟨w * o, hn⟩ : N₀) = ⟨w, hwN⟩ * ⟨o, hoN⟩ := rfl
    rw [e, map_mul, (MonoidHom.mem_ker).mp hok, mul_one]
    rfl
  have hgker : g.ker = ON.subgroupOf W := by
    ext ⟨w, hw⟩
    rw [MonoidHom.mem_ker]
    change f ⟨w, hWN₀ hw⟩ = 1 ↔ w ∈ ON
    rw [← MonoidHom.mem_ker, hker]
    rfl
  refine nonempty_bar_mulEquiv g hgs hgker (fun w hw => mem_sup_left ⟨hWK hw, hw⟩)
    (hWN₀.trans hONn) ?_
  rw [hWO, inf_eq_right.mpr hWK]

variable [Finite G]

theorem isKleinFour_bar_of_le {L : Subgroup G} (hL : L ≤ H) (hV : IsKleinFour L) :
    IsKleinFour (bar H L) := by
  have hLO : L ⊓ O H = ⊥ := inf_eq_bot_of_isKleinFour hV (card_O_odd H)
  obtain ⟨e⟩ := bar_mulEquiv hL hLO
  exact IsKleinFour.mk (by rw [Nat.card_congr e.toEquiv, hV.card_four])
    (by rw [Monoid.exponent_eq_of_mulEquiv e, hV.exponent_two])

theorem bar_ne_bot_of_isKleinFour {L : Subgroup G} (hL : L ≤ H) (hV : IsKleinFour L) :
    bar H L ≠ ⊥ := by
  intro h
  have h4 := (isKleinFour_bar_of_le hL hV).card_four
  rw [h, card_bot] at h4
  exact absurd h4 (by norm_num)

theorem isMaxInvIn_bar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A P : Subgroup G}
    (hA : IsPGroup 2 A) (hAH : A ≤ H) (hP : IsMaxInvIn p A H P) :
    IsMaxInvIn p (bar H A) ⊤ (bar H P) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPH, hPp, hAP, hmax⟩ := hP
  refine ⟨le_top, isPGroup_bar_of_isPGroup hPp, bar_le_normalizer hAP, ?_⟩
  intro Rb _ hRb hARb hPRb
  set π := QuotientGroup.mk' (CFSG.oddCore H) with hπdef
  set Rt : Subgroup H := Rb.comap π with hRtdef
  set R : Subgroup G := Rt.map H.subtype with hRdef
  have hRH : R ≤ H := map_subtype_le _
  have hPR : P ≤ R := fun x hx => ⟨⟨x, hPH hx⟩, hPRb ⟨⟨x, hPH hx⟩, hx, rfl⟩, rfl⟩
  have hAR : A ≤ normalizer (R : Set G) := by
    intro a ha
    apply mem_normalizer_of_forall_conj_mem
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨⟨a, hAH ha⟩ * r * (⟨a, hAH ha⟩ : H)⁻¹, ?_, rfl⟩
    have hab : π ⟨a, hAH ha⟩ ∈ bar H A := ⟨⟨a, hAH ha⟩, ha, rfl⟩
    show π (⟨a, hAH ha⟩ * r * (⟨a, hAH ha⟩ : H)⁻¹) ∈ Rb
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hARb hab) (π r)).mp hr
  have hRodd : Odd (Nat.card R) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2
    have hx2 : (x : G) * x = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx, pow_two] at this
      exact congrArg Subtype.val this
    obtain ⟨y, hy, hyx⟩ := x.2
    have hyx' : (y : G) = x := hyx
    have hy2 : y * y = 1 := Subtype.ext (by
      show (y : G) * y = 1
      rw [hyx']
      exact hx2)
    have hπy : π y = 1 := by
      have hRbodd : Odd (Nat.card Rb) := odd_card_of_isPGroup hp hp2 hRb
      exact eq_one_of_mul_self_of_odd hRbodd hy (by rw [← map_mul, hy2, map_one])
    have hyO : (y : G) ∈ O H := (mk_eq_one_iff y).mp hπy
    have hy1 : (y : G) = 1 := eq_one_of_mul_self_of_odd (card_O_odd H) hyO
      (congrArg Subtype.val hy2)
    have : x = 1 := Subtype.ext (by rw [← hyx]; exact hy1)
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  obtain ⟨R₀, hR₀, hPR₀, hAR₀⟩ :=
    CFSG.ABGTheoremB.exists_isSylowOf_normalized_ge_of_odd hp hA hAR hRodd hPR hPp hAP
  have hR₀P : R₀ = P := hmax R₀ (hR₀.le.trans hRH) hR₀.isPGroup hAR₀ hPR₀
  rw [hR₀P] at hR₀
  have hPeq : (P.subgroupOf H).map H.subtype = P := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hPH]
  have hsyl : IsSylowOf p (P.subgroupOf H) Rt :=
    (isSylowOf_map_subtype_iff H).mp (by rw [hPeq]; exact hR₀)
  have hsyl' := isSylowOf_map_hom hsyl π
  rw [hRtdef, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hsyl'
  exact hsyl'.eq_of_le hPRb le_rfl hRb

end CFSG.GH72
