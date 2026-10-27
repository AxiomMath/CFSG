module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineData

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def U3SixNineInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → U3U1Data G L f t T R₂ U₁ →
    (¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) →
    (∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T) →
    (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁ →
    ∃ v ∈ T, v ^ 2 ∈ szT₁ L T ∧ v ∉ szT₁ L T ⊔ zpowers t ∧
      ∀ g : G, ∀ u ∈ U₁, g * t * g⁻¹ ≠ u * v

theorem exists_pow_not_mem_sq_mem_of_two_pow {G : Type*} [Group G] {N : Subgroup G} {s : G} {k : ℕ}
    (hk : s ^ 2 ^ k = 1) (hs : s ∉ N) : ∃ n : ℕ, s ^ n ∉ N ∧ (s ^ n) ^ 2 ∈ N := by
  induction k generalizing s with
  | zero =>
    rw [pow_zero, pow_one] at hk
    exact absurd (by rw [hk]; exact N.one_mem) hs
  | succ k ih =>
    by_cases hs2 : s ^ 2 ∈ N
    · exact ⟨1, by rwa [pow_one], by rwa [pow_one]⟩
    · obtain ⟨n, hn, hn2⟩ := ih (s := s ^ 2) (by rw [← pow_mul, ← pow_succ']; exact hk) hs2
      exact ⟨2 * n, by rwa [pow_mul], by rwa [pow_mul]⟩

theorem mem_or_mul_inv_mem_of_mem_sup_zpowers {G : Type*} [Group G] {U : Subgroup G} {w : G}
    (hwN : w ∈ normalizer (U : Set G)) (hw2 : w ^ 2 ∈ U) {x : G} (hx : x ∈ U ⊔ zpowers w) :
    x ∈ U ∨ x * w⁻¹ ∈ U := by
  obtain ⟨u, hu, z, hz, rfl⟩ :=
    exists_mul_eq_of_mem_sup_of_le_normalizer (zpowers_le.mpr hwN) hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  have hw2' : w ^ (2 : ℤ) ∈ U := by rw [zpow_two, ← sq]; exact hw2
  rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
  · left
    rw [zpow_mul]
    exact mul_mem hu (zpow_mem hw2' j)
  · right
    rw [zpow_add_one, ← mul_assoc, mul_inv_cancel_right, zpow_mul]
    exact mul_mem hu (zpow_mem hw2' j)

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem t_not_mem_centralizer_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) : t ∉ centralizer (R₂ : Set G) := by
  intro htC
  obtain ⟨-, hA₁card, -, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨b, hb, hb1⟩ : ∃ b ∈ szA₁ (szT₁ L T), b ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : szA₁ (szT₁ L T) = ⊥ := eq_bot_iff.mpr fun b hb => mem_bot.mpr (hno b hb)
    rw [hbot, card_bot] at hA₁card
    have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.two_le; omega)
    omega
  obtain ⟨r, hr, hrb⟩ := hR.rho_onto b hb
  apply hb1
  rw [← hrb]
  have hrt : r * t = t * r := mem_centralizer_iff.mp htC r hr
  rw [hrt, mul_inv_cancel_right, ← sq, hR.t_sq]

end U3Start

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

section Certificates

theorem exists_eq_of_sq_eq_one (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {w : G} (hwT : w ∈ T) (hw2 : w ^ 2 ∈ szT₁ L T)
    (hwS : w ∉ szT₁ L T ⊔ zpowers t) {x : G} (hx : x ∈ U₁ ⊔ T) (hx2 : x ^ 2 = 1) :
    ∃ u ∈ U₁, x = u ∨ x = u * t ∨ x = u * w ∨ x = u * t * w := by
  have hTU := hU.le_normalizer h hS2 hR
  obtain ⟨u, hu, s, hs, rfl⟩ := exists_mul_eq_of_mem_sup_of_le_normalizer hTU hx
  have hs2 : s ^ 2 ∈ szT₁ L T := by
    have h1 : s ^ 2 ∈ U₁ := by
      have e : s ^ 2 = (s * u⁻¹ * s⁻¹) * u⁻¹ * (u * s) ^ 2 := by rw [sq, sq]; group
      rw [e, hx2, mul_one]
      exact mul_mem ((mem_normalizer_iff.mp (hTU hs) _).mp (inv_mem hu)) (inv_mem hu)
    rw [← hU.inf_eq h hR]
    exact mem_inf.mpr ⟨h1, pow_mem hs 2⟩
  have hsub : szT₁ L T ≤ szT₁ L T ⊔ zpowers t := le_sup_left
  by_cases hsS : s ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hsS
    refine ⟨u * y, mul_mem hu (hU.le (mem_sup_left hy)), ?_⟩
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    · left
      rw [← hyz, hz1]
      group
    · right; left
      rw [← hyz, hz1]
      group
  · have hsw := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hs hwT (hsub hs2) (hsub hw2) hsS hwS
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hsw
    have hs' : s = y * z * w := by rw [hyz]; group
    refine ⟨u * y, mul_mem hu (hU.le (mem_sup_left hy)), ?_⟩
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    · right; right; left
      rw [hs', hz1]
      group
    · right; right; right
      rw [hs', hz1]
      group

theorem false_of_forall_conj_ne (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {w : G} (hwT : w ∈ T) (hw2 : w ^ 2 ∈ szT₁ L T)
    (hwS : w ∉ szT₁ L T ⊔ zpowers t) (hS : ∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T)
    (hw : ∀ g : G, ∀ u ∈ U₁, g * t * g⁻¹ ≠ u * w) : False := by
  obtain ⟨S, hSeq⟩ := hS
  have hTU := hU.le_normalizer h hS2 hR
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hG : IsSimpleGroup G := h.setting.1
  obtain ⟨a₀, b₀, hab⟩ : ∃ a b : G, a * b ≠ b * a := h.setting.2.1
  have hKS : U₁ ⊔ zpowers w ≤ U₁ ⊔ T := sup_le le_sup_left (zpowers_le.mpr (mem_sup_right hwT))
  have hcomm : ⁅U₁ ⊔ T, U₁ ⊔ T⁆ ≤ U₁ ⊔ zpowers w :=
    (hU.commutator_le h hS2 hR).trans le_sup_left
  have hSK : U₁ ⊔ T ≤ normalizer ((U₁ ⊔ zpowers w : Subgroup G) : Set G) := by
    intro c hc
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun k hk => ?_
    have h1 : ⁅c⁻¹, k⁆ ∈ U₁ ⊔ zpowers w :=
      hcomm (commutator_mem_commutator (inv_mem hc) (hKS hk))
    have e : c⁻¹ * k * c = ⁅c⁻¹, k⁆ * k := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem h1 hk
  have hindex : Nat.Coprime 2 (U₁ ⊔ T).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (hSeq ▸ S.not_dvd_index)
  have htK : t ∉ U₁ ⊔ zpowers w := by
    intro htK
    rcases mem_or_mul_inv_mem_of_mem_sup_zpowers (hTU hwT) (hU.le (mem_sup_left hw2)) htK
      with h1 | h1
    · exact hU.t_not_mem h1
    · exact hw 1 _ h1 (by group)
  have hut : ∀ u ∈ U₁, t⁻¹ * u * t ∈ U₁ := fun u hu => (mem_normalizer_iff''.mp (hTU htT) u).mp hu
  have hcond : ∀ a : G, a⁻¹ * t * a ∈ U₁ ⊔ T → t⁻¹ * (a⁻¹ * t * a) ∈ U₁ ⊔ zpowers w := by
    intro a ha
    have hy2 : (a⁻¹ * t * a) ^ 2 = 1 := by
      rw [show (a⁻¹ * t * a) ^ 2 = a⁻¹ * t ^ 2 * a by rw [sq, sq]; group, h.sq_eq_one, mul_one,
        inv_mul_cancel]
    obtain ⟨u, hu, h1 | h1 | h1 | h1⟩ := hU.exists_eq_of_sq_eq_one h hS2 hR hwT hw2 hwS ha hy2
    · exfalso
      apply hU.conj_not_mem a⁻¹
      rw [inv_inv, h1]
      exact hu
    · rw [h1, show t⁻¹ * (u * t) = t⁻¹ * u * t by group]
      exact mem_sup_left (hut u hu)
    · exact absurd (by rw [inv_inv]; exact h1) (hw a⁻¹ u hu)
    · rw [h1, show t⁻¹ * (u * t * w) = (t⁻¹ * u * t) * w by group]
      exact mul_mem (mem_sup_left (hut u hu)) (mem_sup_right (mem_zpowers w))
  have hnot := CFSG.Quasithin.generalized_thompson_transfer_two (H := U₁ ⊔ T)
    (K := U₁ ⊔ zpowers w) hindex ⟨hKS, (normal_subgroupOf_iff_le_normalizer hKS).mpr hSK⟩ hcomm
    (mem_sup_right htT) htK h.inv hcond
  apply hnot
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := commutator G) with h1 | h1
  · exfalso
    apply hab
    have h2 := commutator_mem_commutator (mem_top a₀) (mem_top b₀)
    rw [← commutator_def, h1, mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  · rw [h1]
    exact mem_top t

theorem exists_outer_mem_centralizer (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {x : G} (hx : x ∈ U₁ ⊔ T)
    (hxC : x ∈ centralizer (R₂ : Set G)) (hxU : x ∉ U₁) :
    ∃ w ∈ T, w ^ 2 ∈ szT₁ L T ∧ w ∉ szT₁ L T ⊔ zpowers t ∧ w ∈ centralizer (R₂ : Set G) := by
  have hTU := hU.le_normalizer h hS2 hR
  obtain ⟨u, hu, s, hs, rfl⟩ := exists_mul_eq_of_mem_sup_of_le_normalizer hTU hx
  have hsC : s ∈ centralizer (R₂ : Set G) := by
    have := mul_mem (inv_mem (hU.le_centralizer hu)) hxC
    rwa [inv_mul_cancel_left] at this
  have hsT₁ : s ∉ szT₁ L T := fun hsT => hxU (mul_mem hu (hU.le (mem_sup_left hsT)))
  obtain ⟨k, hk⟩ := h.isPGroup ⟨s, hs⟩
  have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨n, hn, hn2⟩ := exists_pow_not_mem_sq_mem_of_two_pow hk' hsT₁
  refine ⟨s ^ n, pow_mem hs n, hn2, fun hmem => ?_, pow_mem hsC n⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hmem
  rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
  · apply hn
    rw [← hyz, hz1, mul_one]
    exact hy
  · apply h.t_not_mem_centralizer_of_card_sylow hS2 hR
    have hyC : y ∈ centralizer (R₂ : Set G) :=
      mem_centralizer_iff.mpr fun r hr => (hR.commT₁ y hy r hr).symm
    have e : t = y⁻¹ * s ^ n := by rw [← hyz, hz1]; group
    rw [e]
    exact mul_mem (inv_mem hyC) (pow_mem hsC n)

theorem not_isSylow_sup_of_centralizer (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hC : ¬ (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁) :
    ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T := by
  intro hS
  obtain ⟨x, hxSC, hxU⟩ := Set.not_subset.mp hC
  obtain ⟨hx, hxC⟩ := mem_inf.mp hxSC
  obtain ⟨w, hwT, hw2, hwS, hwC⟩ := hU.exists_outer_mem_centralizer h hS2 hR hx hxC hxU
  refine hU.false_of_forall_conj_ne h hS2 hR hwT hw2 hwS hS fun g u hu hgu => ?_
  apply hU.conj_not_mem_centralizer h hS2 hR g
  rw [hgu]
  exact mul_mem (hU.le_centralizer hu) hwC

theorem inf_centralizer_le_of_isSylow (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hS : ∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T) :
    (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁ := by
  by_contra hC
  exact hU.not_isSylow_sup_of_centralizer h hS2 hR hC hS

theorem not_isSylow_sup (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hncyc : ¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T)
    (hsix : U3SixNineInput) : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T := by
  intro hS
  obtain ⟨v, hvT, hv2, hvS, hv⟩ := hsix G L f t T R₂ U₁ h hS2 hR hU hncyc hS
    (hU.inf_centralizer_le_of_isSylow h hS2 hR hS)
  exact hU.false_of_forall_conj_ne h hS2 hR hvT hv2 hvS hS hv

theorem exists_normalizer_conj_not_mem (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hnS : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T) :
    ∃ s ∈ normalizer ((U₁ ⊔ T : Subgroup G) : Set G), s ∉ U₁ ⊔ T ∧
      (∃ P : Subgroup G, IsPGroup 2 P ∧ U₁ ⊔ T ≤ P ∧ s ∈ P) ∧
        s * t * s⁻¹ ∉ U₁ ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzN, hzP, Q, hQ2, hPQ, hzQ⟩ :=
    exists_normalizer_not_mem_of_not_isSylow (hU.isPGroup_sup h hS2 hR) hnS
  refine ⟨z, hzN, hzP, ⟨Q, hQ2, hPQ, hzQ⟩, fun hztU => ?_⟩
  obtain ⟨u, hu, hut⟩ := hU.conj_of_mem z hztU
  have hmt : u⁻¹ * z ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc u⁻¹ * z * t = u⁻¹ * (z * t * z⁻¹) * z := by group
      _ = u⁻¹ * (u * t * u⁻¹) * z := by rw [hut]
      _ = t * (u⁻¹ * z) := by group
  have hmQ : u⁻¹ * z ∈ Q := mul_mem (inv_mem (hPQ (mem_sup_left hu))) hzQ
  have hQT : Q ⊓ centralizer ({t} : Set G) = T := by
    have hQt2 : IsPGroup 2 (Q ⊓ centralizer ({t} : Set G) : Subgroup G) :=
      hQ2.to_le inf_le_left
    obtain ⟨a, -, ha⟩ :=
      exists_conj_mem_of_isSylowOf h.isSylowOf_centralizer inf_le_right hQt2
    have hle : (Q ⊓ centralizer ({t} : Set G)).map (MulAut.conj a⁻¹).toMonoidHom ≤ T := by
      rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using ha x hx
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective] at h1
    exact (Subgroup.eq_of_le_of_card_ge (le_inf ((le_sup_right : T ≤ U₁ ⊔ T).trans hPQ) h.le)
      h1).symm
  have hmT : u⁻¹ * z ∈ T := by rw [← hQT]; exact mem_inf.mpr ⟨hmQ, hmt⟩
  apply hzP
  have e : z = u * (u⁻¹ * z) := by group
  rw [e]
  exact mul_mem (mem_sup_left hu) (mem_sup_right hmT)

theorem exists_eq_mul_of_conj_not_mem (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {w : G} (hwT : w ∈ T) (hw2 : w ^ 2 ∈ szT₁ L T)
    (hwS : w ∉ szT₁ L T ⊔ zpowers t) {s : G} (hsN : s ∈ normalizer ((U₁ ⊔ T : Subgroup G) : Set G))
    (hst : s * t * s⁻¹ ∉ U₁ ⊔ zpowers t) :
    ∃ u ∈ U₁, s * t * s⁻¹ = u * w ∨ s * t * s⁻¹ = u * t * w := by
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hx : s * t * s⁻¹ ∈ U₁ ⊔ T := (mem_normalizer_iff.mp hsN t).mp (mem_sup_right htT)
  have hx2 : (s * t * s⁻¹) ^ 2 = 1 := by
    rw [show (s * t * s⁻¹) ^ 2 = s * t ^ 2 * s⁻¹ by rw [sq, sq]; group, h.sq_eq_one, mul_one,
      mul_inv_cancel]
  obtain ⟨u, hu, h1 | h1 | h1 | h1⟩ := hU.exists_eq_of_sq_eq_one h hS2 hR hwT hw2 hwS hx hx2
  · exact absurd (by rw [h1]; exact hu) (hU.conj_not_mem s)
  · exact absurd (by rw [h1]; exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t))) hst
  · exact ⟨u, hu, Or.inl h1⟩
  · exact ⟨u, hu, Or.inr h1⟩

end Certificates

end U3U1Data

end CFSG.SeitzReduction.RankOne
