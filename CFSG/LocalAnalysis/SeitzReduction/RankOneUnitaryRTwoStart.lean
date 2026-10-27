module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRElem
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRTwoSetup

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.GH74.Uniqueness.Bender

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem not_mem_szT₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) : t ∉ szT₁ L T := by
  obtain ⟨-, -, -, -, hdisj, -⟩ := h.start_of_card_sylow hS2
  intro htT
  have ht1 : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨htT, mem_zpowers t⟩
  rw [hdisj, mem_bot] at ht1
  have h2 := h.inv
  rw [ht1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem exists_u3RTorus_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ d k : G, d ∈ L ∧ U3RTorus (szT₁ L T) (u3R₁ L T t) t d k := by
  classical
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hcore⟩ := hB.exists_benderCore Q
  have hA₁L : ∀ x ∈ szA₁ (szT₁ L T), x ∈ L := fun x hx => szT₁_le_right L T (szA₁_le _ hx)
  have := hcore.isCyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := cartan (Q : Subgroup L) t₀)
  have hpow : ∀ x : L, x ∈ cartan (Q : Subgroup L) t₀ → ∃ n : ℕ, (x : G) = ((g : L) : G) ^ n := by
    intro x hx
    have h1 : (⟨x, hx⟩ : cartan (Q : Subgroup L) t₀) ∈ Submonoid.powers g :=
      mem_powers_iff_mem_zpowers.mpr (hg _)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp h1
    refine ⟨n, ?_⟩
    have := congrArg (fun y : cartan (Q : Subgroup L) t₀ => ((y : L) : G)) hn
    simpa using this.symm
  set d : G := ((g : L) : G) with hd
  have hdL : d ∈ L := (g : L).2
  have hgN : (g : L) ∈ borel (Q : Subgroup L) := cartan_le_borel _ _ g.2
  have hdT : d ∈ normalizer (szT₁ L T : Set G) :=
    (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) (g : L)).mp hgN
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  have hNA : ∀ x ∈ L, x ∈ normalizer (szT₁ L T : Set G) → x ∈ normalizer (u3R₁ L T t : Set G) := by
    intro x hxL hxT
    have hxA := h.inf_normalizer_le_normalizer_szA ⟨hxL, hxT⟩
    refine mem_normalizer_iff.mpr fun r => ⟨fun hr => h.conj_mem_u3R₁_of_card_sylow hS2 hxA hr,
      fun hr => ?_⟩
    have := h.conj_mem_u3R₁_of_card_sylow hS2 (inv_mem hxA) hr
    rwa [show x⁻¹ * (x * r * x⁻¹) * x⁻¹⁻¹ = r by group] at this
  have hdodd : Odd (orderOf d) := by
    rw [hd, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hcore.odd_card_cartan (_root_.orderOf_dvd_natCard g)
  have he2 : 2 ≤ e := by
    have := h.two_le
    cases hB with
    | unitary n hn e' => exact two_le_unitary_e hn
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ fixCartan (Q : Subgroup L) t₀, x ≠ 1 := by
    by_contra hall
    push Not at hall
    have : fixCartan (Q : Subgroup L) t₀ = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (hall x hx)
    have h1 := hcore.card_fixCartan
    rw [this, card_bot] at h1
    omega
  have hxD : x ∈ cartan (Q : Subgroup L) t₀ := fixCartan_le_cartan _ _ hx
  set k : G := (x : G) with hk
  have hkL : k ∈ L := x.2
  have hkC : k ∈ centralizer (szA₁ (szT₁ L T) : Set G) := by
    refine mem_centralizer_iff.mpr fun z hz => ?_
    by_cases hz1 : z = 1
    · rw [hz1, one_mul, mul_one]
    have hzZ : (⟨z, hA₁L z hz⟩ : L) ∈ rootCenter (Q : Subgroup L) := (hmemZ _).mpr hz
    have hz1' : (⟨z, hA₁L z hz⟩ : L) ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
    rw [← hcore.cartan_inf_centralizer_eq hzZ hz1'] at hx
    have := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
    exact (congrArg Subtype.val this).symm
  have hkT : k ∈ normalizer (szT₁ L T : Set G) :=
    (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) x).mp (cartan_le_borel _ _ hxD)
  obtain ⟨m, hm⟩ := hpow x hxD
  have hkd : k ∈ zpowers d := by
    rw [hk, hm]
    exact pow_mem (mem_zpowers d) m
  have hkodd : Odd (orderOf k) := Odd.of_dvd_nat hdodd (orderOf_dvd_of_mem_zpowers hkd)
  obtain ⟨E, _, _, _, σ, -, -, -, u, v, hc, hA₁u, -, hodd⟩ :=
    h.exists_rootCoords_scalar_of_card_sylow hS2
  have hkA : k ∈ normalizer (szA L T t : Set G) ⊓ centralizer (szA₁ (szT₁ L T) : Set G) :=
    mem_inf.mpr ⟨h.inf_normalizer_le_normalizer_szA ⟨hkL, hkT⟩, hkC⟩
  obtain ⟨s, -, hs⟩ := hodd k hkA hkodd
  have hs1 : s ≠ 1 := by
    intro hs1
    obtain ⟨y, hyT, hyu⟩ := hc.u_surj 1
    have hyL : y ∈ L := szT₁_le_right L T hyT
    have hkyT : k * y * k⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hkT y).mp hyT
    have h1 : k * y * k⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := by
      have h2 : y⁻¹ * (k * y * k⁻¹) ∈ szA₁ (szT₁ L T) :=
        (hA₁u _ (mul_mem (inv_mem hyT) hkyT)).mpr
          (by rw [hc.u_mul_inv hyT hkyT, hs y hyT, hs1, one_mul, sub_self])
      have h3 := (mem_normalizer_iff.mp (normalizer_le_normalizer_inf_centralizer (szT₁ L T)
        (Subgroup.le_normalizer hyT)) _).mp h2
      have e : y * (y⁻¹ * (k * y * k⁻¹)) * y⁻¹ = k * y * k⁻¹ * y⁻¹ := by group
      rw [e] at h3
      exact h3
    have hfpf := hB.fixedPointFree_unitary Q hcore.sq_eq_one hcore.not_mem hxD hx1
      ((hmemQ ⟨y, hyL⟩).mpr hyT) ((hmemZ _).mpr (by simpa using h1))
    have h4 := (hA₁u y hyT).mp ((hmemZ _).mp hfpf)
    rw [hyu] at h4
    exact one_ne_zero h4
  refine ⟨d, k, hdL, hdodd, hNA d hdL hdT, hdT, hdt, fun b hb b' hb' hb1 hb1' => ?_, hkd, hkC,
    fun y hy => ?_⟩
  ·
    obtain ⟨c, hc, hcc⟩ := hcore.exists_cartan_conj ((hmemZ ⟨b, hA₁L b hb⟩).mpr hb)
      (fun h1 => hb1 (congrArg Subtype.val h1)) ((hmemZ ⟨b', hA₁L b' hb'⟩).mpr hb')
      (fun h1 => hb1' (congrArg Subtype.val h1))
    obtain ⟨n, hn⟩ := hpow c hc
    refine ⟨n, ?_⟩
    have := congrArg Subtype.val hcc
    simp only [coe_mul, coe_inv] at this
    rw [← hn, this]
  ·
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    obtain ⟨y', hy', hu'⟩ := hc.u_surj ((s - 1)⁻¹ * u y)
    refine ⟨y', hy', (hA₁u _ (mul_mem (inv_mem hy) ?_)).mpr ?_⟩
    · exact mul_mem ((mem_normalizer_iff.mp hkT y').mp hy') (inv_mem hy')
    · have hky' : k * y' * k⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hkT y').mp hy'
      rw [hc.u_mul_inv hy (mul_mem hky' (inv_mem hy')), hc.mul_u _ hky' _ (inv_mem hy'),
        hc.u_inv hy', hs y' hy', hu']
      linear_combination (u y) * mul_inv_cancel₀ hs1'

section Certificates


theorem u3RSetup_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    U3RSetup (szT₁ L T) (u3R₁ L T t) t (2 ^ f) := by
  obtain ⟨hT₁card, hA₁card, -, hsqT, -, hsqA, -⟩ := h.facts_of_card_sylow hS2
  have hD := h.partitionData_of_card_sylow hS2
  refine ⟨?_, h.sq_eq_one, h.mem_centralizer_szT₁, h.not_mem_szT₁_of_card_sylow hS2, hsqT, hsqA,
    hA₁card, hT₁card, h.card_u3R₁_of_card_sylow hS2, h.sup_le_u3R₁_of_card_sylow hS2,
    u3R₁_le_centralizer L T t, fun r hr => ?_, h.exists_u3R₁_conj_of_card_sylow hS2,
    h.u3R₁_inf_centralizer_of_card_sylow hS2,
    fun r hr => h.sq_mem_szA_of_mem_u3R₁_of_card_sylow hS2 hr⟩
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  · obtain ⟨c, hc, hct⟩ := hD.exists_conj_t_eq (u3R₁_le_normalizer L T t hr)
    rw [hct, mul_inv_cancel_right]
    exact hc

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
