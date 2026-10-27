module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryROne

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.GH74.Uniqueness.Bender

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_rootCoords_fpf_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (σ : E →+* E),
      Nat.card E = (2 ^ f) ^ 2 ∧ (∀ x, σ x = x ^ (2 ^ f)) ∧
      ∃ u v : G → E, U3RootCoords (szT₁ L T) σ u v ∧
        (∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0)) ∧
        ∃ k ∈ centralizer (szA L T t : Set G), k ∈ normalizer (szT₁ L T : Set G) ∧
          ∃ s : E, s ≠ 1 ∧ ∀ y ∈ szT₁ L T, u (k * y * k⁻¹) = s * u y := by
  classical
  obtain ⟨E, hE, hF, hch, σ, hEcard, hσ, -, u, v, hc, hA₁u, -, hodd⟩ :=
    h.exists_rootCoords_scalar_of_card_sylow hS2
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
  have hkA : (d : G) ∈ centralizer (szA L T t : Set G) :=
    h.mem_centralizer_szA_of_mem_centralizer_szA₁ d.2 hdC
  have hkT : (d : G) ∈ normalizer (szT₁ L T : Set G) :=
    (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) d).mp (cartan_le_borel _ _ hdD)
  have hkodd : Odd (orderOf (d : G)) := by
    rw [Subgroup.orderOf_coe]
    have h1 : orderOf (⟨d, hdD⟩ : cartan (Q : Subgroup L) t₀) ∣
        Nat.card (cartan (Q : Subgroup L) t₀) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hcore.odd_card_cartan h1
  obtain ⟨s, -, hs⟩ := hodd (d : G) (mem_inf.mpr ⟨centralizer_le_normalizer _ hkA, hdC⟩) hkodd
  refine ⟨E, hE, hF, hch, σ, hEcard, hσ, u, v, hc, hA₁u, d, hkA, hkT, s, fun hs1 => ?_, hs⟩
  obtain ⟨y, hyT, hyu⟩ := hc.u_surj 1
  have hyL : y ∈ L := szT₁_le_right L T hyT
  have hkyT : (d : G) * y * (d : G)⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hkT y).mp hyT
  have h1 : (d : G) * y * (d : G)⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := by
    have h2 : y⁻¹ * ((d : G) * y * (d : G)⁻¹) ∈ szA₁ (szT₁ L T) :=
      (hA₁u _ (mul_mem (inv_mem hyT) hkyT)).mpr
        (by rw [hc.u_mul_inv hyT hkyT, hs y hyT, hs1, one_mul, sub_self])
    have h3 := (mem_normalizer_iff.mp (normalizer_le_normalizer_inf_centralizer (szT₁ L T)
      (Subgroup.le_normalizer hyT)) _).mp h2
    have e : y * (y⁻¹ * ((d : G) * y * (d : G)⁻¹)) * y⁻¹ = (d : G) * y * (d : G)⁻¹ * y⁻¹ := by
      group
    rw [e] at h3
    exact h3
  have hfpf := hB.fixedPointFree_unitary Q hcore.sq_eq_one hcore.not_mem hdD hd1
    ((hmemQ ⟨y, hyL⟩).mpr hyT) ((hmemZ _).mpr (by simpa using h1))
  have h4 := (hA₁u y hyT).mp ((hmemZ _).mp hfpf)
  rw [hyu] at h4
  exact one_ne_zero h4

theorem conj_mul_inv_mem_of_mem_u3R₁_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {x w : G} (hx : x ∈ u3R₁ L T t) (hw : w ∈ szT₁ L T ⊔ zpowers t) :
    x⁻¹ * w * x * w⁻¹ ∈ szA₁ (szT₁ L T) := by
  have hD := h.partitionData_of_card_sylow hS2
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hw
  obtain ⟨-, -, -, hxinv⟩ := inv_mem hx
  have h1 := hxinv y hy
  rw [inv_inv] at h1
  have hA₁T : ∀ a ∈ szA₁ (szT₁ L T), ∀ g ∈ szT₁ L T, g * a = a * g := fun a ha g hg =>
    (mem_centralizer_iff.mp (mem_inf.mp ha).2 g hg)
  have h2 : x⁻¹ * y * x * y⁻¹ ∈ szA₁ (szT₁ L T) := by
    have e : x⁻¹ * y * x * y⁻¹ = y * (y⁻¹ * (x⁻¹ * y * x)) * y⁻¹ := by group
    rw [e, hA₁T _ h1 y hy, mul_inv_cancel_right]
    exact h1
  rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
  · rw [hz1]
    simpa using h2
  · rw [hz1]
    obtain ⟨c, hc, hct⟩ := hD.exists_conj_t_eq (inv_mem (u3R₁_le_normalizer L T t hx))
    rw [inv_inv] at hct
    have e : x⁻¹ * (y * t) * x * (y * t)⁻¹ = (x⁻¹ * y * x) * (x⁻¹ * t * x) * t⁻¹ * y⁻¹ := by
      group
    rw [e, hct]
    have e2 : x⁻¹ * y * x * (c * t) * t⁻¹ * y⁻¹ = (x⁻¹ * y * x * y⁻¹) * (y * c * y⁻¹) := by group
    rw [e2, show y * c * y⁻¹ = c by rw [hA₁T c hc y hy, mul_inv_cancel_right]]
    exact mul_mem h2 hc

theorem sq_mem_szA_of_mem_u3R₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {r : G}
    (hr : r ∈ u3R₁ L T t) : r ^ 2 ∈ szA L T t := by
  obtain ⟨E, _, _, _, σ, -, -, u, v, hc, hA₁u, k, hkA, hkT, s, hs1, hs⟩ :=
    h.exists_rootCoords_fpf_of_card_sylow hS2
  have hD := h.partitionData_of_card_sylow hS2
  obtain ⟨-, -, -, hAcomm⟩ := h.szA_facts_of_card_sylow hS2
  obtain ⟨-, -, -, hsqT, -, -, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨-, -, -, -, hdisj, -⟩ := h.start_of_card_sylow hS2
  have hinf := h.u3R₁_inf_centralizer_of_card_sylow hS2
  have htC := h.mem_centralizer_szT₁
  have hA := mem_szA_right L T t
  have hA₁A := szA₁_le_szA L T t
  have hAT : ∀ x ∈ szT₁ L T, x ∈ szA L T t → x ∈ szA₁ (szT₁ L T) := by
    intro x hxT hxA
    rcases SzPartition.mem_sup_zpowers_cases hD.mem_centralizer hD.sq_eq_one hxA with h1 | ⟨b, hb, rfl⟩
    · exact h1
    · exfalso
      have htT : t ∈ szT₁ L T := by
        have := mul_mem (inv_mem (szA₁_le _ hb)) hxT
        rwa [inv_mul_cancel_left] at this
      have : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨htT, mem_zpowers t⟩
      rw [hdisj, mem_bot] at this
      have h2 := h.inv
      rw [this, orderOf_one] at h2
      exact absurd h2 (by norm_num)
  obtain ⟨c, hcA₁, hct⟩ := hD.exists_conj_t_eq (u3R₁_le_normalizer L T t hr)
  have hrc : r * c = c * r := (mem_centralizer_iff.mp (u3R₁_le_centralizer L T t hr) c hcA₁).symm
  have hc2 : c * c = 1 := by
    have := hA₁A hcA₁
    obtain ⟨-, hA2, -, -⟩ := h.szA_facts_of_card_sylow hS2
    rw [← sq]
    exact hA2 c this
  have hr2t : r ^ 2 * t = t * r ^ 2 := by
    have h1 : r ^ 2 * t * (r ^ 2)⁻¹ = t := by
      calc r ^ 2 * t * (r ^ 2)⁻¹ = r * (r * t * r⁻¹) * r⁻¹ := by rw [sq]; group
        _ = r * (c * t) * r⁻¹ := by rw [hct]
        _ = (r * c * r⁻¹) * (r * t * r⁻¹) := by group
        _ = c * (c * t) := by rw [hrc, mul_inv_cancel_right, hct]
        _ = t := by rw [← mul_assoc, hc2, one_mul]
    calc r ^ 2 * t = r ^ 2 * t * (r ^ 2)⁻¹ * r ^ 2 := by group
      _ = t * r ^ 2 := by rw [h1]
  have hr2S : r ^ 2 ∈ szT₁ L T ⊔ zpowers t := by
    rw [← hinf]
    exact mem_inf.mpr ⟨pow_mem hr 2, mem_centralizer_singleton_iff.mpr hr2t⟩
  obtain ⟨y, hyT, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers htC hr2S
  have hkN : k ∈ normalizer (szA L T t : Set G) := centralizer_le_normalizer _ hkA
  have hkr : k * r * k⁻¹ ∈ u3R₁ L T t := h.conj_mem_u3R₁_of_card_sylow hS2 hkN hr
  set w := r⁻¹ * (k * r * k⁻¹) with hw
  have hkt : t * k = k * t := mem_centralizer_iff.mp hkA t hA
  have hkc : c * k = k * c := mem_centralizer_iff.mp hkA c (hA₁A hcA₁)
  have hrc' : r⁻¹ * c * r = c := by
    rw [mul_assoc, ← hrc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hrt : r⁻¹ * t * r = c * t := by
    have h1 : c * (r⁻¹ * t * r) = t := by
      calc c * (r⁻¹ * t * r) = (r⁻¹ * c * r) * (r⁻¹ * t * r) := by rw [hrc']
        _ = r⁻¹ * (c * t) * r := by group
        _ = r⁻¹ * (r * t * r⁻¹) * r := by rw [hct]
        _ = t := by group
    calc r⁻¹ * t * r = c⁻¹ * (c * (r⁻¹ * t * r)) := by group
      _ = c⁻¹ * t := by rw [h1]
      _ = c * t := by rw [hcinv]
  have hkt' : k⁻¹ * t * k = t := by
    rw [mul_assoc, hkt, ← mul_assoc, inv_mul_cancel, one_mul]
  have hkct : k * (c * t) * k⁻¹ = c * t := by
    calc k * (c * t) * k⁻¹ = (k * c) * t * k⁻¹ := by group
      _ = c * (k * t) * k⁻¹ := by rw [← hkc]; group
      _ = c * t := by rw [← hkt]; group
  have hwt : w * t = t * w := by
    have h1 : w * t * w⁻¹ = t := by
      calc w * t * w⁻¹ = r⁻¹ * (k * (r * (k⁻¹ * t * k) * r⁻¹) * k⁻¹) * r := by
            simp only [hw]; group
        _ = r⁻¹ * (k * (r * t * r⁻¹) * k⁻¹) * r := by rw [hkt']
        _ = r⁻¹ * (k * (c * t) * k⁻¹) * r := by rw [hct]
        _ = r⁻¹ * (c * t) * r := by rw [hkct]
        _ = (r⁻¹ * c * r) * (r⁻¹ * t * r) := by group
        _ = c * (c * t) := by rw [hrc', hrt]
        _ = t := by rw [← mul_assoc, hc2, one_mul]
    calc w * t = w * t * w⁻¹ * w := by group
      _ = t * w := by rw [h1]
  have hwR : w ∈ u3R₁ L T t := mul_mem (inv_mem hr) hkr
  have hwS : w ∈ szT₁ L T ⊔ zpowers t := by
    rw [← hinf]
    exact mem_inf.mpr ⟨hwR, mem_centralizer_singleton_iff.mpr hwt⟩
  have hα := h.conj_mul_inv_mem_of_mem_u3R₁_of_card_sylow hS2 hr hwS
  have hw2 : w ^ 2 ∈ szA₁ (szT₁ L T) := by
    have := (h.sq_mul_eq_of_card_sylow hS2 hwS (one_mem (szA L T t))).2
    exact this
  set β := r⁻¹ * w * r * w⁻¹ * w ^ 2 with hβ
  have hβA : β ∈ szA L T t := mul_mem (hA₁A hα) (hA₁A hw2)
  have hkr2 : k * r ^ 2 * k⁻¹ = r ^ 2 * β := by
    have hkrw : k * r * k⁻¹ = r * w := by simp only [hw]; group
    calc k * r ^ 2 * k⁻¹ = (k * r * k⁻¹) ^ 2 := by rw [sq, sq]; group
      _ = (r * w) ^ 2 := by rw [hkrw]
      _ = r ^ 2 * β := by simp only [hβ, sq]; group
  have hzA : z ∈ szA L T t := (zpowers_le.mpr hA) hz
  have hkz : k * z * k⁻¹ = z := by
    rw [(mem_centralizer_iff.mp hkA z hzA).symm, mul_inv_cancel_right]
  have hzβ : z * β = β * z := hAcomm z hzA β hβA
  have hkyT : k * y * k⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hkT y).mp hyT
  have hyβ : y⁻¹ * (k * y * k⁻¹) = β := by
    have h1 : (k * y * k⁻¹) * z = y * z * β := by
      calc (k * y * k⁻¹) * z = (k * y * k⁻¹) * (k * z * k⁻¹) := by rw [hkz]
        _ = k * (y * z) * k⁻¹ := by group
        _ = k * r ^ 2 * k⁻¹ := by rw [hyz]
        _ = r ^ 2 * β := hkr2
        _ = y * z * β := by rw [hyz]
    calc y⁻¹ * (k * y * k⁻¹) = y⁻¹ * ((k * y * k⁻¹) * z) * z⁻¹ := by group
      _ = y⁻¹ * (y * z * β) * z⁻¹ := by rw [h1]
      _ = y⁻¹ * (y * (z * β)) * z⁻¹ := by group
      _ = y⁻¹ * (y * (β * z)) * z⁻¹ := by rw [hzβ]
      _ = β := by group
  have hβA₁ : y⁻¹ * (k * y * k⁻¹) ∈ szA₁ (szT₁ L T) :=
    hAT _ (mul_mem (inv_mem hyT) hkyT) (by rw [hyβ]; exact hβA)
  have hu0 := (hA₁u _ (mul_mem (inv_mem hyT) hkyT)).mp hβA₁
  rw [hc.u_mul_inv hyT hkyT, hs y hyT] at hu0
  have huy : u y = 0 := by
    have h1 : (s - 1) * u y = 0 := by linear_combination hu0
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (sub_eq_zero.mp h2) hs1
    · exact h2
  have hyA₁ : y ∈ szA₁ (szT₁ L T) := (hA₁u y hyT).mpr huy
  rw [← hyz]
  exact mul_mem (hA₁A hyA₁) hzA

end U3Start

end CFSG.SeitzReduction.RankOne
