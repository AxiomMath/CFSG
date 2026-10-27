module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NcycBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Outer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

theorem ncyc_pow_four_mul {G : Type*} [Group G] {p q : G} (hpq : Commute p q) (hp : p ^ 4 = 1) :
    (p * q) ^ 4 = q ^ 4 := by
  rw [hpq.mul_pow, hp, one_mul]

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_gen_of_outer_involution (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) :
    ∃ b ∈ T, (∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T ⊔ zpowers t) ∧
      t ∉ szT₁ L T ⊔ zpowers b := by
  obtain ⟨htT, -, -, hTN₁, -, hMn, -⟩ := h.start_of_card_sylow hS2
  have hcycM := h.isCyclic_quotient_of_card_sylow hS2
  obtain ⟨g₀, hg₀⟩ := hcycM.exists_zpow_surjective
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g₀
  have hbgen : ∀ s ∈ T, ∃ k : ℤ, ((b : G) ^ k)⁻¹ * s ∈ szT₁ L T ⊔ zpowers t := by
    intro s hs
    obtain ⟨k, hk⟩ := hg₀ (QuotientGroup.mk ⟨s, hs⟩)
    refine ⟨k, ?_⟩
    simp only at hk
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_subgroupOf] at hk
    simpa using hk
  refine ⟨b, b.2, hbgen, fun htb => ?_⟩
  obtain ⟨v, hvT, hv2, hvS⟩ := hv
  apply hvS
  have hbN : (b : G) ∈ normalizer (szT₁ L T : Set G) := hTN₁ b.2
  have hzbN : zpowers (b : G) ≤ normalizer (szT₁ L T : Set G) := zpowers_le.mpr hbN
  rw [sup_comm] at htb
  obtain ⟨bj, hbj, y₀, hy₀, hbt⟩ := ncyc_exists_mul_of_mem_sup hzbN htb
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hbj
  have hcyc : ∃ b' ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b' ^ k)⁻¹ * s ∈ szT₁ L T := by
    refine ⟨b, b.2, fun s hs => ?_⟩
    obtain ⟨k, hk⟩ := hbgen s hs
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hk
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
    · exact ⟨k, by rw [← hyz, mul_one]; exact hy⟩
    · refine ⟨k + j, ?_⟩
      have hs' : s = (b : G) ^ k * (y * ((b : G) ^ j * y₀)) := by
        rw [hbt, hyz]; group
      have e : ((b : G) ^ (k + j))⁻¹ * s = ((b : G) ^ j)⁻¹ * y * (b : G) ^ j * y₀ := by
        rw [hs', zpow_add]; group
      rw [e]
      exact mul_mem ((mem_normalizer_iff''.mp (zpow_mem hbN j) y).mp hy) hy₀
  exact h.mem_sup_zpowers_of_sq_mem_of_card_sylow hS2 hcyc hvT (by rw [hv2]; exact one_mem _)

theorem card_le_of_isExtremalIn (h : U3Start G L f t T) {P : Subgroup G} {g : G}
    (hext : CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 P (g⁻¹ * t * g)) :
    Nat.card T ≤ Nat.card (P ⊓ centralizer ({g⁻¹ * t * g} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ centralizer ({g⁻¹ * t * g} : Set G))
      (centralizer ({g⁻¹ * t * g} : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr hext
  set Tg := T.map (MulAut.conj g⁻¹).toMonoidHom with hTg
  have hTgC : Tg ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hyt := mem_centralizer_singleton_iff.mp (h.le hy)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * y * g * (g⁻¹ * t * g) = g⁻¹ * (y * t) * g := by group
      _ = g⁻¹ * (t * y) * g := by rw [hyt]
      _ = g⁻¹ * t * g * (g⁻¹ * y * g) := by group
  have hTgp : IsPGroup 2 Tg := h.isPGroup.map _
  obtain ⟨c, -, hc⟩ := exists_conj_mem_of_isSylowOf hsyl hTgC hTgp
  have hle : T.map (MulAut.conj (g * c)⁻¹).toMonoidHom ≤
      P ⊓ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have := hc _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this ⊢
    convert this using 1
    group
  calc Nat.card T = Nat.card (T.map (MulAut.conj (g * c)⁻¹).toMonoidHom) :=
        (card_map_of_injective (MulAut.conj _).injective).symm
    _ ≤ _ := card_le_of_le hle

end U3Start

theorem ncyc_conj_of_sign_pos {G : Type*} [Group G] {T₁ U W : Subgroup G} {w y u₁ u yh : G}
    (hUc : ∀ y ∈ T₁, ∀ u ∈ U, y * u = u * y) (hUab : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u)
    (hWT : W ≤ T₁) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hyW : y ∈ W) (hu₁ : u₁ ∈ U)
    (hu : u ∈ U) (hyh : yh ∈ W) (hwyh : w * yh * w⁻¹ = yh⁻¹)
    (hyh2 : yh * yh = u⁻¹ * (w * u * w⁻¹)) :
    (y * u₁ * w) * (yh * u) = (yh * u) * (y * u₁ * w) := by
  have hyhT : yh ∈ T₁ := hWT hyh
  have hwu : w * u * w⁻¹ = u * (yh * yh) := by rw [hyh2]; group
  have hE : w * (yh * u) * w⁻¹ = yh⁻¹ * (u * (yh * yh)) := by
    rw [show w * (yh * u) * w⁻¹ = (w * yh * w⁻¹) * (w * u * w⁻¹) by group, hwyh, hwu]
  have hcu₁ : Commute u₁ (yh⁻¹ * (u * (yh * yh))) := by
    have h1 : Commute u₁ yh := (show Commute yh u₁ from hUc yh hyhT u₁ hu₁).symm
    have h2 : Commute u₁ u := hUab u₁ hu₁ u hu
    exact h1.inv_right.mul_right (h2.mul_right (h1.mul_right h1))
  have hcy : Commute y (yh⁻¹ * (u * (yh * yh))) := by
    have h1 : Commute y yh := hWc y hyW yh hyh
    have h2 : Commute y u := hUc y (hWT hyW) u hu
    exact h1.inv_right.mul_right (h2.mul_right (h1.mul_right h1))
  have hEq : yh⁻¹ * (u * (yh * yh)) = yh * u := by
    have h2 : Commute yh u := hUc yh hyhT u hu
    calc yh⁻¹ * (u * (yh * yh)) = yh⁻¹ * ((u * yh) * yh) := by group
      _ = yh⁻¹ * ((yh * u) * yh) := by rw [h2.eq]
      _ = u * yh := by group
      _ = yh * u := h2.eq.symm
  have hconj : (y * u₁ * w) * (yh * u) * (y * u₁ * w)⁻¹ = yh * u := by
    calc (y * u₁ * w) * (yh * u) * (y * u₁ * w)⁻¹
        = y * (u₁ * (w * (yh * u) * w⁻¹) * u₁⁻¹) * y⁻¹ := by group
      _ = y * (u₁ * (yh⁻¹ * (u * (yh * yh))) * u₁⁻¹) * y⁻¹ := by rw [hE]
      _ = y * (yh⁻¹ * (u * (yh * yh))) * y⁻¹ := by rw [hcu₁.eq, mul_inv_cancel_right]
      _ = yh⁻¹ * (u * (yh * yh)) := by rw [hcy.eq, mul_inv_cancel_right]
      _ = yh * u := hEq
  calc (y * u₁ * w) * (yh * u) = (y * u₁ * w) * (yh * u) * (y * u₁ * w)⁻¹ * (y * u₁ * w) := by
        group
    _ = (yh * u) * (y * u₁ * w) := by rw [hconj]

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem pow_four_of_mem_mul (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {U : Subgroup G}
    (hUc : ∀ y ∈ szT₁ L T, ∀ u ∈ U, y * u = u * y) {p₁ p₂ q₁ q₂ : G} (hp₁ : p₁ ∈ szT₁ L T)
    (hp₂ : p₂ ∈ szT₁ L T) (hq₁ : q₁ ∈ U) (hq₂ : q₂ ∈ U) (k : ℤ) :
    ((p₁ * q₁) ^ k * (p₂ * q₂)) ^ 4 = (q₁ ^ k * q₂) ^ 4 := by
  have c11 : Commute p₁ q₁ := hUc p₁ hp₁ q₁ hq₁
  have e1 : (p₁ * q₁) ^ k = p₁ ^ k * q₁ ^ k := c11.mul_zpow k
  have c2 : Commute (q₁ ^ k) p₂ :=
    (show Commute p₂ (q₁ ^ k) from hUc p₂ hp₂ _ (zpow_mem hq₁ k)).symm
  have e2 : p₁ ^ k * q₁ ^ k * (p₂ * q₂) = (p₁ ^ k * p₂) * (q₁ ^ k * q₂) := by
    rw [show p₁ ^ k * q₁ ^ k * (p₂ * q₂) = p₁ ^ k * (q₁ ^ k * p₂) * q₂ by group, c2.eq]
    group
  rw [e1, e2]
  have hpT : p₁ ^ k * p₂ ∈ szT₁ L T := mul_mem (zpow_mem hp₁ k) hp₂
  have hqU : q₁ ^ k * q₂ ∈ U := mul_mem (zpow_mem hq₁ k) hq₂
  exact ncyc_pow_four_mul (hUc _ hpT _ hqU) (h.pow_four_eq_one_of_mem_sup hS2 (mem_sup_left hpT))

theorem sup_le_normalizer_sup_szT₁ (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {U : Subgroup G}
    (hUc : ∀ y ∈ szT₁ L T, ∀ u ∈ U, y * u = u * y) (hUT : T ≤ normalizer (U : Set G)) :
    T ⊔ U ≤ normalizer ((szT₁ L T ⊔ U : Subgroup G) : Set G) := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  have hT₁N : szT₁ L T ≤ normalizer (U : Set G) := (szT₁_le_left L T).trans hUT
  have hPN : T ⊔ U ≤ normalizer (U : Set G) := sup_le hUT Subgroup.le_normalizer
  have key : ∀ p ∈ T ⊔ U, ∀ z ∈ szT₁ L T ⊔ U, p * z * p⁻¹ ∈ szT₁ L T ⊔ U := by
    intro p hp z hz
    obtain ⟨s, hs, u₀, hu₀, rfl⟩ := ncyc_exists_mul_of_mem_sup hUT hp
    obtain ⟨y, hy, u, hu, rfl⟩ := ncyc_exists_mul_of_mem_sup hT₁N hz
    have h1 : u₀ * y * u₀⁻¹ = y := by rw [← hUc y hy u₀ hu₀, mul_inv_cancel_right]
    have e : s * u₀ * (y * u) * (s * u₀)⁻¹ =
        (s * (u₀ * y * u₀⁻¹) * s⁻¹) * (s * u₀ * u * (s * u₀)⁻¹) := by group
    rw [e, h1]
    refine mul_mem (mem_sup_left ((mem_normalizer_iff.mp (hTN₁ hs) y).mp hy)) (mem_sup_right ?_)
    exact (mem_normalizer_iff.mp (hPN (mul_mem (mem_sup_left hs) (mem_sup_right hu₀))) u).mp hu
  intro p hp
  exact mem_normalizer_of_forall_inv_mul_mul_mem fun z hz => by
    simpa using key p⁻¹ (inv_mem hp) z hz

end U3Start

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem false_of_extremal_neg (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {U W : Subgroup G}
    (hUc : ∀ y ∈ szT₁ L T, ∀ u ∈ U, y * u = u * y) (hUab : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u)
    (hUA : szA₁ (szT₁ L T) ≤ U)
    (hUT : T ≤ normalizer (U : Set G)) (hTUeq : T ⊓ U = szA₁ (szT₁ L T))
    (hT₁Ueq : szT₁ L T ⊓ U = szA₁ (szT₁ L T)) (hPN : T ⊔ U ≤ normalizer (U : Set G))
    (hWT : W ≤ szT₁ L T) (hAW : szA₁ (szT₁ L T) ≤ W) (hWcard : Nat.card W = (2 ^ f) ^ 2)
    {w : G} (hwT : w ∈ T)
    (hWiff : ∀ y ∈ szT₁ L T, (y⁻¹ * (w * y * w⁻¹) ∈ szA₁ (szT₁ L T) ↔ y ∈ W))
    (hneg : ∀ u ∈ U, w * u * w⁻¹ = u → u ∈ szA₁ (szT₁ L T)) {y u₁ g : G} (hu₁ : u₁ ∈ U)
    (hy : y ∈ szT₁ L T) (hx_eq : g⁻¹ * t * g = y * u₁ * w) (hxP : g⁻¹ * t * g ∈ T ⊔ U)
    (hgext : CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 (T ⊔ U) (g⁻¹ * t * g)) : False := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, hA₁comm, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hT₁T : szT₁ L T ≤ T := szT₁_le_left L T
  have hT₁N : szT₁ L T ≤ normalizer (U : Set G) := hT₁T.trans hUT
  have hTle := h.card_le_of_isExtremalIn hgext
  set x := g⁻¹ * t * g with hxdef
  have hconjU : ∀ u' ∈ U, x * u' * x⁻¹ = w * u' * w⁻¹ := by
    intro u' hu'
    have hc : w * u' * w⁻¹ ∈ U := (mem_normalizer_iff.mp (hUT hwT) u').mp hu'
    have h2 : y * (w * u' * w⁻¹) = (w * u' * w⁻¹) * y := hUc y hy _ hc
    have h1 : u₁ * (w * u' * w⁻¹) = (w * u' * w⁻¹) * u₁ := hUab _ hu₁ _ hc
    rw [hx_eq]
    calc y * u₁ * w * u' * (y * u₁ * w)⁻¹ = y * (u₁ * (w * u' * w⁻¹)) * u₁⁻¹ * y⁻¹ := by group
      _ = y * ((w * u' * w⁻¹) * u₁) * u₁⁻¹ * y⁻¹ := by rw [h1]
      _ = (y * (w * u' * w⁻¹)) * y⁻¹ := by group
      _ = ((w * u' * w⁻¹) * y) * y⁻¹ := by rw [h2]
      _ = w * u' * w⁻¹ := by group
  have hconjT : ∀ y' ∈ szT₁ L T, x * y' * x⁻¹ = y * (w * y' * w⁻¹) * y⁻¹ := by
    intro y' hy'
    have hc : w * y' * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) y').mp hy'
    have h1 : u₁ * (w * y' * w⁻¹) = (w * y' * w⁻¹) * u₁ := (hUc _ hc u₁ hu₁).symm
    rw [hx_eq]
    calc y * u₁ * w * y' * (y * u₁ * w)⁻¹ = y * (u₁ * (w * y' * w⁻¹)) * u₁⁻¹ * y⁻¹ := by group
      _ = y * ((w * y' * w⁻¹) * u₁) * u₁⁻¹ * y⁻¹ := by rw [h1]
      _ = y * (w * y' * w⁻¹) * y⁻¹ := by group
  have hxT₁ : ∀ y' ∈ szT₁ L T, x * y' * x⁻¹ ∈ szT₁ L T := by
    intro y' hy'
    rw [hconjT y' hy']
    exact mul_mem (mul_mem hy ((mem_normalizer_iff.mp (hTN₁ hwT) y').mp hy')) (inv_mem hy)
  have hxU : ∀ u' ∈ U, x * u' * x⁻¹ ∈ U := fun u' hu' =>
    (mem_normalizer_iff.mp (hPN hxP) u').mp hu'
  have hWx : ∀ y' ∈ szT₁ L T, y'⁻¹ * (x * y' * x⁻¹) ∈ szA₁ (szT₁ L T) → y' ∈ W := by
    intro y' hy' hm
    have hc : w * y' * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) y').mp hy'
    have hcomm' : y * (w * y' * w⁻¹)⁻¹ * y⁻¹ * (w * y' * w⁻¹) ∈ szA₁ (szT₁ L T) := by
      rw [hA₁comm]
      have := commutator_mem_commutator hy (inv_mem hc)
      rwa [commutatorElement_def, inv_inv] at this
    refine (hWiff y' hy').mp ?_
    have e : y'⁻¹ * (w * y' * w⁻¹) = (y'⁻¹ * (x * y' * x⁻¹)) *
        (y * (w * y' * w⁻¹)⁻¹ * y⁻¹ * (w * y' * w⁻¹)) := by
      rw [hconjT y' hy']; group
    rw [e]
    exact mul_mem hm hcomm'
  have hC := ncyc_card_inf_centralizer_mul_le hUc (le_of_eq hT₁Ueq) hAW hWT hUA hxT₁ hxU hWx
  have hCU : Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 2 ^ f := by
    rw [← hA₁card]
    apply card_le_of_le
    intro u' hu'
    obtain ⟨hu'U, hu'C⟩ := mem_inf.mp hu'
    apply hneg u' hu'U
    rw [← hconjU u' hu'U]
    have := mem_centralizer_singleton_iff.mp hu'C
    rw [← this, mul_inv_cancel_right]
  have hBN : (T ⊔ U) ⊓ centralizer ({x} : Set G) ≤
      normalizer ((szT₁ L T ⊔ U : Subgroup G) : Set G) :=
    inf_le_left.trans (h.sup_le_normalizer_sup_szT₁ hS2 hUc hUT)
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hBN
  have hBP : szT₁ L T ⊔ U ≤ T ⊔ U := sup_le (hT₁T.trans le_sup_left) le_sup_right
  have hCB : (T ⊔ U) ⊓ centralizer ({x} : Set G) ⊓ (szT₁ L T ⊔ U) =
      (szT₁ L T ⊔ U) ⊓ centralizer ({x} : Set G) := by
    ext z
    simp only [mem_inf]
    constructor
    · rintro ⟨⟨-, hzc⟩, hzB⟩
      exact ⟨hzB, hzc⟩
    · rintro ⟨hzB, hzc⟩
      exact ⟨⟨hBP hzB, hzc⟩, hzB⟩
  rw [hCB] at hprod
  have hsupP : Nat.card (((T ⊔ U) ⊓ centralizer ({x} : Set G)) ⊔ (szT₁ L T ⊔ U) : Subgroup G) ≤
      Nat.card (T ⊔ U : Subgroup G) := card_le_of_le (sup_le inf_le_left hBP)
  have hP := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hUT
  have hB := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hT₁N
  rw [hTUeq, hA₁card] at hP
  rw [hT₁Ueq, hA₁card, hT₁card] at hB
  rw [hA₁card, hWcard] at hC
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  set q := 2 ^ f with hqdef
  set c := Nat.card ((T ⊔ U) ⊓ centralizer ({x} : Set G) : Subgroup G)
  set bb := Nat.card (szT₁ L T ⊔ U : Subgroup G)
  set bc := Nat.card ((szT₁ L T ⊔ U) ⊓ centralizer ({x} : Set G) : Subgroup G)
  set pp := Nat.card (T ⊔ U : Subgroup G)
  set nu := Nat.card U
  set nt := Nat.card T
  set cu := Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G)
  have hnu : 0 < nu := Nat.card_pos
  have hcpos : 0 < c := Nat.card_pos
  have hqpos : 0 < q := by omega
  have h1 : c * bb ≤ pp * bc := by
    rw [← hprod]
    exact Nat.mul_le_mul_right _ hsupP
  have h3 : bc ≤ q ^ 2 := by
    have : bc * q ≤ q ^ 2 * q := hC.trans (Nat.mul_le_mul_left _ hCU)
    exact Nat.le_of_mul_le_mul_right this hqpos
  have h2 : c * (q ^ 3 * nu) ≤ nt * nu * q ^ 2 := by
    calc c * (q ^ 3 * nu) = c * (bb * q) := by rw [hB]
      _ = (c * bb) * q := by ring
      _ ≤ (pp * bc) * q := Nat.mul_le_mul_right _ h1
      _ = (pp * q) * bc := by ring
      _ = nt * nu * bc := by rw [hP]
      _ ≤ nt * nu * q ^ 2 := Nat.mul_le_mul_left _ h3
  have h4 : c * nu * q ^ 3 ≤ c * nu * q ^ 2 := by
    calc c * nu * q ^ 3 = c * (q ^ 3 * nu) := by ring
      _ ≤ nt * nu * q ^ 2 := h2
      _ ≤ c * nu * q ^ 2 := by
        have := Nat.mul_le_mul_right (nu * q ^ 2) hTle
        calc nt * nu * q ^ 2 = nt * (nu * q ^ 2) := by ring
          _ ≤ c * (nu * q ^ 2) := this
          _ = c * nu * q ^ 2 := by ring
  have h5 : q ^ 3 ≤ q ^ 2 := Nat.le_of_mul_le_mul_left h4 (Nat.mul_pos hcpos hnu)
  have h6 : q ^ 3 = q * q ^ 2 := by ring
  have h7 : 0 < q ^ 2 := by positivity
  rw [h6] at h5
  have : q ≤ 1 := by
    by_contra hq
    push Not at hq
    have : 2 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq
    omega
  omega

theorem false_of_extremal_ncyc (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {U : Subgroup G}
    (hUc : ∀ y ∈ szT₁ L T, ∀ u ∈ U, y * u = u * y)
    (hUab : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u)
    (hUA : szA₁ (szT₁ L T) ≤ U) (hUT : T ≤ normalizer (U : Set G))
    (hU8 : ∃ a ∈ U, ∃ b ∈ U, ∀ k : ℤ, (a ^ k * b) ^ 4 ≠ 1 ∧ (b ^ k * a) ^ 4 ≠ 1)
    (hsign : ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t →
      (∀ u ∈ U, w * u * w⁻¹ = u → u ∈ szA₁ (szT₁ L T)) ∨
        ∀ u ∈ U, u⁻¹ * (w * u * w⁻¹) ∈ szA₁ (szT₁ L T))
    (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t)
    (hTU : ∀ x ∈ T, x ∈ U → x ∈ szA₁ (szT₁ L T)) (hTUeq : T ⊓ U = szA₁ (szT₁ L T))
    (hT₁Ueq : szT₁ L T ⊓ U = szA₁ (szT₁ L T)) (hP2 : IsPGroup 2 (T ⊔ U : Subgroup G))
    (hPN : T ⊔ U ≤ normalizer (U : Set G)) {M : Subgroup G} (htM : t ∉ M)
    (hT₁M : szT₁ L T ≤ M) (hUM : U ≤ M) (hMP : M ≤ T ⊔ U) {g : G} (hgM : g⁻¹ * t * g ∈ M)
    (hgext : CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 (T ⊔ U) (g⁻¹ * t * g)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨htT, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, hA₁comm, hsq, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hT₁T : szT₁ L T ≤ T := szT₁_le_left L T
  have hT₁N : szT₁ L T ≤ normalizer (U : Set G) := hT₁T.trans hUT
  obtain ⟨a, ha, a', ha', hab⟩ := hU8
  set x := g⁻¹ * t * g with hxdef
  have hxP : x ∈ T ⊔ U := hMP hgM
  have hCp : IsPGroup 2 ((T ⊔ U) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    hP2.to_le inf_le_left
  have hx2 : x ^ 2 = 1 := by
    rw [hxdef, sq, show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ← sq,
      h.sq_eq_one]
    group
  obtain ⟨s, hs, u, hu, hsu⟩ := ncyc_exists_mul_of_mem_sup hUT hxP
  have hs2 : s ^ 2 ∈ szT₁ L T := by
    have e : s ^ 2 = (s * u) ^ 2 * (u⁻¹ * (s⁻¹ * u⁻¹ * s)) := by rw [sq, sq]; group
    have hU' : u⁻¹ * (s⁻¹ * u⁻¹ * s) ∈ U :=
      mul_mem (inv_mem hu) ((mem_normalizer_iff''.mp (hUT hs) _).mp (inv_mem hu))
    have hsU : s ^ 2 ∈ U := by rw [e, hsu, hx2, one_mul]; exact hU'
    exact szA₁_le _ (hTU _ (pow_mem hs 2) hsU)
  have hZ8 : ∀ b₁ ∈ T ⊔ U, ∀ b₂ ∈ T ⊔ U, x * b₁ = b₁ * x → x * b₂ = b₂ * x →
      (∀ k : ℤ, (b₁ ^ k * b₂) ^ 4 ≠ 1 ∧ (b₂ ^ k * b₁) ^ 4 ≠ 1) → False := by
    intro b₁ hb₁ b₂ hb₂ hc₁ hc₂ hk
    exact h.false_of_conj_of_pow_four hS2 hCp inf_le_right
      (mem_inf.mpr ⟨hb₁, mem_centralizer_singleton_iff.mpr hc₁.symm⟩)
      (mem_inf.mpr ⟨hb₂, mem_centralizer_singleton_iff.mpr hc₂.symm⟩) hk
  by_cases hsS : s ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hsS
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    ·
      rw [hz1, mul_one] at hyz
      have hcx : ∀ u' ∈ U, x * u' = u' * x := by
        intro u' hu'
        rw [← hsu, ← hyz]
        calc y * u * u' = y * (u * u') := by group
          _ = y * (u' * u) := by rw [hUab u hu u' hu']
          _ = (y * u') * u := by group
          _ = (u' * y) * u := by rw [hUc y hy u' hu']
          _ = u' * (y * u) := by group
      exact hZ8 a (mem_sup_right ha) a' (mem_sup_right ha') (hcx a ha) (hcx a' ha') hab
    ·
      rw [hz1] at hyz
      apply htM
      have htu : t * u * t⁻¹ ∈ U := (mem_normalizer_iff.mp (hUT htT) u).mp hu
      have e : t = (y * (t * u * t⁻¹))⁻¹ * x := by rw [← hsu, ← hyz]; group
      rw [e]
      exact mul_mem (inv_mem (mul_mem (hT₁M hy) (hUM htu))) hgM
  ·
    obtain ⟨v, hvT, hv2, hvS⟩ := hv
    have hsv := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hs hvT (mem_sup_left hs2)
      (by rw [hv2]; exact one_mem _) hsS hvS
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hsv
    have hzT : z ∈ T := zpowers_le.mpr htT hz
    have hzv : z * v = v * z := (commute_of_mem_zpowers hz
      (mem_centralizer_singleton_iff.mp (h.le hvT))).symm
    set w := z * v with hwdef
    have hwT : w ∈ T := mul_mem hzT hvT
    have hw2 : w ^ 2 = 1 := by
      have hz2 : z ^ 2 = 1 := by
        rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
        · exact one_pow 2
        · exact h.sq_eq_one
      rw [hwdef, (show Commute z v from hzv).mul_pow, hz2, hv2, one_mul]
    have hwS : w ∉ szT₁ L T ⊔ zpowers t := by
      intro hwS'
      apply hvS
      rw [show v = z⁻¹ * w by rw [hwdef]; group]
      exact mul_mem (mem_sup_right (inv_mem hz)) hwS'
    have hs_eq : s = y * w := by rw [hwdef, ← mul_assoc, hyz]; group
    set u₁ := w * u * w⁻¹ with hu₁def
    have hu₁ : u₁ ∈ U := (mem_normalizer_iff.mp (hUT hwT) u).mp hu
    have hx_eq : x = y * u₁ * w := by rw [← hsu, hs_eq, hu₁def]; group
    obtain ⟨W, hWT, hAW, hWcard, hWc, hWinv, hWsq, hWiff⟩ :=
      h.exists_W_of_card_sylow hS2 hwT hw2 hwS
    rcases hsign w hwT hw2 hwS with hneg | hpos
    · exact h.false_of_extremal_neg hS2 hUc hUab hUA hUT hTUeq hT₁Ueq hPN hWT hAW hWcard hwT
        hWiff hneg hu₁ hy hx_eq hxP hgext
    ·
      have hyW : y ∈ W := by
        have hc : w * y * w⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp (hTN₁ hwT) y).mp hy
        have hu₁' : w * u₁ * w⁻¹ ∈ U := (mem_normalizer_iff.mp (hUT hwT) u₁).mp hu₁
        have hww : w * w = 1 := by rw [← sq, hw2]
        have h1 : u₁ * (w * y * w⁻¹) = (w * y * w⁻¹) * u₁ := (hUc _ hc u₁ hu₁).symm
        have hxx : x * x = (y * (w * y * w⁻¹)) * (u₁ * (w * u₁ * w⁻¹)) := by
          rw [hx_eq]
          calc y * u₁ * w * (y * u₁ * w) =
              y * (u₁ * (w * y * w⁻¹)) * (w * u₁ * w⁻¹) * (w * w) := by group
            _ = y * ((w * y * w⁻¹) * u₁) * (w * u₁ * w⁻¹) * (w * w) := by rw [h1]
            _ = (y * (w * y * w⁻¹)) * (u₁ * (w * u₁ * w⁻¹)) := by rw [hww]; group
        have hx1 : x * x = 1 := by rw [← sq]; exact hx2
        have hyc : y * (w * y * w⁻¹) ∈ szA₁ (szT₁ L T) := by
          have e : y * (w * y * w⁻¹) = (u₁ * (w * u₁ * w⁻¹))⁻¹ := by
            rw [eq_inv_iff_mul_eq_one, ← hxx, hx1]
          apply hTU _ (hT₁T (mul_mem hy hc))
          rw [e]
          exact inv_mem (mul_mem hu₁ hu₁')
        refine (hWiff y hy).mp ?_
        rw [show y⁻¹ * (w * y * w⁻¹) = (y ^ 2)⁻¹ * (y * (w * y * w⁻¹)) by group]
        exact mul_mem (inv_mem (hsq y hy)) hyc
      have hcent : ∀ u ∈ U, ∃ yh ∈ W, x * (yh * u) = (yh * u) * x := by
        intro u' hu'
        obtain ⟨yh, hyh, hyh2⟩ := hWsq _ (hpos u' hu')
        refine ⟨yh, hyh, ?_⟩
        rw [hx_eq]
        exact ncyc_conj_of_sign_pos hUc hUab hWT hWc hyW hu₁ hu' hyh (hWinv yh hyh) hyh2
      obtain ⟨y₁, hy₁, hc₁⟩ := hcent a ha
      obtain ⟨y₂, hy₂, hc₂⟩ := hcent a' ha'
      refine hZ8 (y₁ * a) (mul_mem (mem_sup_left (hT₁T (hWT hy₁))) (mem_sup_right ha))
        (y₂ * a') (mul_mem (mem_sup_left (hT₁T (hWT hy₂))) (mem_sup_right ha')) hc₁ hc₂
        fun k => ?_
      rw [h.pow_four_of_mem_mul hS2 hUc (hWT hy₁) (hWT hy₂) ha ha' k,
        h.pow_four_of_mem_mul hS2 hUc (hWT hy₂) (hWT hy₁) ha' ha k]
      exact hab k

theorem false_of_ncyc_sylow_stage (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {U : Subgroup G}
    (hUc : ∀ y ∈ szT₁ L T, ∀ u ∈ U, y * u = u * y)
    (hUab : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u)
    (hUA : szA₁ (szT₁ L T) ≤ U) (hUt : ∀ u ∈ U, t * u * t⁻¹ = u → u ∈ szA₁ (szT₁ L T))
    (hUT : T ≤ normalizer (U : Set G))
    (hU8 : ∃ a ∈ U, ∃ b ∈ U, ∀ k : ℤ, (a ^ k * b) ^ 4 ≠ 1 ∧ (b ^ k * a) ^ 4 ≠ 1)
    (hsign : ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t →
      (∀ u ∈ U, w * u * w⁻¹ = u → u ∈ szA₁ (szT₁ L T)) ∨
        ∀ u ∈ U, u⁻¹ * (w * u * w⁻¹) ∈ szA₁ (szT₁ L T))
    (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t)
    (hsyl : ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ U) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨htT, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, hA₁comm, hsq, -, -, -⟩ := h.facts_of_card_sylow hS2
  have hT₁T : szT₁ L T ≤ T := szT₁_le_left L T
  have hA₁T : szA₁ (szT₁ L T) ≤ T := (szA₁_le _).trans hT₁T
  have hTU : ∀ x ∈ T, x ∈ U → x ∈ szA₁ (szT₁ L T) := by
    intro x hxT hxU
    refine hUt x hxU ?_
    rw [← mem_centralizer_singleton_iff.mp (h.le hxT), mul_inv_cancel_right]
  have hTUeq : T ⊓ U = szA₁ (szT₁ L T) :=
    le_antisymm (fun z hz => hTU z (mem_inf.mp hz).1 (mem_inf.mp hz).2) (le_inf hA₁T hUA)
  have hT₁Ueq : szT₁ L T ⊓ U = szA₁ (szT₁ L T) :=
    le_antisymm (fun z hz => hTU z (hT₁T (mem_inf.mp hz).1) (mem_inf.mp hz).2)
      (le_inf (szA₁_le _) hUA)
  obtain ⟨b, hbT, hbgen, htb⟩ := h.exists_gen_of_outer_involution hS2 hv
  have hM₀T : szT₁ L T ⊔ zpowers b ≤ T := sup_le hT₁T (zpowers_le.mpr hbT)
  have hM₀N : szT₁ L T ⊔ zpowers b ≤ normalizer (U : Set G) := hM₀T.trans hUT
  have hT₁N : szT₁ L T ≤ normalizer (U : Set G) := hT₁T.trans hUT
  have hPN : T ⊔ U ≤ normalizer (U : Set G) := sup_le hUT Subgroup.le_normalizer
  have hMP : (szT₁ L T ⊔ zpowers b) ⊔ U ≤ T ⊔ U := sup_le (hM₀T.trans le_sup_left) le_sup_right
  have hcommT := h.commutator_le_szT₁_of_card_sylow hS2
  have hM₀n : ∀ s ∈ T, ∀ m ∈ szT₁ L T ⊔ zpowers b, s * m * s⁻¹ ∈ szT₁ L T ⊔ zpowers b := by
    intro s hs m hm
    have hc : s * m * s⁻¹ * m⁻¹ ∈ szT₁ L T := by
      have := hcommT (commutator_mem_commutator hs (hM₀T hm))
      rwa [commutatorElement_def] at this
    rw [show s * m * s⁻¹ = (s * m * s⁻¹ * m⁻¹) * m by group]
    exact mul_mem (mem_sup_left hc) hm
  have hMn : ∀ s ∈ T ⊔ U, ∀ m ∈ (szT₁ L T ⊔ zpowers b) ⊔ U,
      s * m * s⁻¹ ∈ (szT₁ L T ⊔ zpowers b) ⊔ U := by
    intro s hs m hm
    obtain ⟨s₀, hs₀, u₀, hu₀, rfl⟩ := ncyc_exists_mul_of_mem_sup hUT hs
    obtain ⟨m₀, hm₀, u₁, hu₁, rfl⟩ := ncyc_exists_mul_of_mem_sup hM₀N hm
    have e : s₀ * u₀ * (m₀ * u₁) * (s₀ * u₀)⁻¹ =
        (s₀ * m₀ * s₀⁻¹) * (s₀ * ((m₀⁻¹ * u₀ * m₀) * u₁ * u₀⁻¹) * s₀⁻¹) := by group
    rw [e]
    refine mul_mem (mem_sup_left (hM₀n s₀ hs₀ m₀ hm₀)) (mem_sup_right ?_)
    have h1 : m₀⁻¹ * u₀ * m₀ ∈ U := (mem_normalizer_iff''.mp (hM₀N hm₀) u₀).mp hu₀
    exact (mem_normalizer_iff.mp (hUT hs₀) _).mp (mul_mem (mul_mem h1 hu₁) (inv_mem hu₀))
  have htM : t ∉ (szT₁ L T ⊔ zpowers b) ⊔ U := by
    intro htM
    obtain ⟨m₀, hm₀, u, hu, hmu⟩ := ncyc_exists_mul_of_mem_sup hM₀N htM
    have huT : u ∈ T := by
      rw [show u = m₀⁻¹ * t by rw [← hmu]; group]
      exact mul_mem (inv_mem (hM₀T hm₀)) htT
    apply htb
    rw [← hmu]
    exact mul_mem hm₀ (mem_sup_left (szA₁_le _ (hTU u huT hu)))
  have hcov : ∀ s ∈ T ⊔ U, s ∈ (szT₁ L T ⊔ zpowers b) ⊔ U ∨
      t⁻¹ * s ∈ (szT₁ L T ⊔ zpowers b) ⊔ U := by
    intro s hs
    obtain ⟨s₀, hs₀, u, hu, rfl⟩ := ncyc_exists_mul_of_mem_sup hUT hs
    obtain ⟨k, hk⟩ := hbgen s₀ hs₀
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hk
    have hs₀' : s₀ = b ^ k * y * z := by rw [mul_assoc, hyz]; group
    have hby : b ^ k * y * u ∈ (szT₁ L T ⊔ zpowers b) ⊔ U :=
      mul_mem (mem_sup_left (mul_mem (mem_sup_right (zpow_mem (mem_zpowers b) k))
        (mem_sup_left hy))) (mem_sup_right hu)
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    · left
      rw [hs₀', hz1, mul_one]
      exact hby
    · right
      rw [hz1] at hs₀'
      have hbt : b ^ k * t = t * b ^ k :=
        (Commute.zpow_left (mem_centralizer_singleton_iff.mp (h.le hbT)) k).eq
      have hyt : y * t = t * y := mem_centralizer_singleton_iff.mp (h.le (hT₁T hy))
      have e : t⁻¹ * (b ^ k * y * t * u) = b ^ k * y * u := by
        calc t⁻¹ * (b ^ k * y * t * u) = t⁻¹ * (b ^ k * (y * t)) * u := by group
          _ = t⁻¹ * (b ^ k * (t * y)) * u := by rw [hyt]
          _ = t⁻¹ * ((b ^ k * t) * y) * u := by group
          _ = t⁻¹ * ((t * b ^ k) * y) * u := by rw [hbt]
          _ = b ^ k * y * u := by group
      rw [hs₀', e]
      exact hby
  obtain ⟨S, hSeq⟩ := hsyl
  have hP2 : IsPGroup 2 (T ⊔ U : Subgroup G) := hSeq ▸ S.isPGroup'
  have hPidx : ¬ 2 ∣ (T ⊔ U).index := hSeq ▸ S.not_dvd_index
  have hG : IsSimpleGroup G := h.setting.1
  obtain ⟨a₀, b₀, hab⟩ : ∃ a b : G, a * b ≠ b * a := h.setting.2.1
  rcases CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) (P := T ⊔ U)
      (Q := (szT₁ L T ⊔ zpowers b) ⊔ U) (u := t) hP2 hPidx hMn
      ⟨t, mem_sup_left htT, fun s hs => by
        rcases hcov s hs with h1 | h1
        · exact ⟨0, by simpa using h1⟩
        · exact ⟨1, by simpa using h1⟩⟩
      (mem_sup_left htT) htM
      (fun g k _ => by
        rw [pow_mul, h.sq_eq_one, one_pow, mul_one, inv_mul_cancel]
        exact one_mem _)
      (fun g hgP _ => hcov _ hgP)
    with ⟨N, hN, hNcyc, -, htN⟩ | ⟨g, hgM, hgext, -⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := N) with hN1 | hN1
    · apply hab
      have : IsCyclic (G ⧸ N) := hNcyc
      have hcomm := (QuotientGroup.mk' N).isMulCommutative_of_isCyclic_of_ker_le_center (by
        rw [QuotientGroup.ker_mk', hN1]
        exact bot_le)
      exact hcomm.is_comm.comm a₀ b₀
    · exact htN (hN1 ▸ mem_top t)
  · exact h.false_of_extremal_ncyc hS2 hUc hUab hUA hUT hU8 hsign hv hTU hTUeq hT₁Ueq hP2
      hPN htM (le_sup_left.trans le_sup_left) le_sup_right hMP hgM hgext

end U3Start

@[expose] def U3C1NcycSylowStageInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → (∃ r ∈ R₂, r ^ 2 ≠ 1) →
    (∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) →
    (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂) →
    ∃ U : Subgroup G, R₂ ≤ U ∧ (∀ y ∈ szT₁ L T, ∀ u ∈ U, y * u = u * y) ∧
      (∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u) ∧ szA₁ (szT₁ L T) ≤ U ∧
      (∀ u ∈ U, t * u * t⁻¹ = u → u ∈ szA₁ (szT₁ L T)) ∧ T ≤ normalizer (U : Set G) ∧
      (∃ a ∈ U, ∃ b ∈ U, ∀ k : ℤ, (a ^ k * b) ^ 4 ≠ 1 ∧ (b ^ k * a) ^ 4 ≠ 1) ∧
      (∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t →
        (∀ u ∈ U, w * u * w⁻¹ = u → u ∈ szA₁ (szT₁ L T)) ∨
          ∀ u ∈ U, u⁻¹ * (w * u * w⁻¹) ∈ szA₁ (szT₁ L T)) ∧
      ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ U

theorem u3C1OuterNcycInput_of_sylowStage
    (hS : U3C1NcycSylowStageInput) (hnc : U3NotSylowNcycInput) : U3C1OuterNcycInput := by
  intro G _ _ L f t T R₂ h hS2 hR hinv hne hv
  have hncyc : ¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T := by
    intro hcyc
    obtain ⟨v, hvT, hv2, hvS⟩ := hv
    exact hvS (h.mem_sup_zpowers_of_sq_mem_of_card_sylow hS2 hcyc hvT
      (by rw [hv2]; exact one_mem _))
  obtain ⟨U, -, hUc, hUab, hUA, hUt, hUT, hU8, hsign, hsyl⟩ :=
    hS G L f t T R₂ h hS2 hR hinv hne hv (hnc G L f t T R₂ h hS2 hR hncyc)
  exact h.false_of_ncyc_sylow_stage hS2 hUc hUab hUA hUt hUT hU8 hsign hv hsyl

end CFSG.SeitzReduction.RankOne
