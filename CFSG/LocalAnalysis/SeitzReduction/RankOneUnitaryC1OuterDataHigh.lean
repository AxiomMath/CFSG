module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterDataMain

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

theorem outerData_conj_pow_ne_one {G : Type*} [Group G] {n x : G} {m : ℕ} (hx : x ^ m ≠ 1) :
    (n * x * n⁻¹) ^ m ≠ 1 := by
  rw [conj_pow]
  intro h1
  apply hx
  calc x ^ m = n⁻¹ * (n * x ^ m * n⁻¹) * n := by group
    _ = 1 := by rw [h1]; group

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

theorem exists_mul_of_mem_sup (hc : U3C1OuterConf G L f t T R₂ D V k) {x : G}
    (hx : x ∈ szT₁ L T ⊔ V) : ∃ y ∈ szT₁ L T, ∃ u ∈ V, y * u = x := by
  have hT₁NV : szT₁ L T ≤ normalizer (V : Set G) := fun y' hy' =>
    mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => by
      have e := mem_centralizer_iff.mp (hc.le_centralizer hr) y' hy'
      rw [show y'⁻¹ * r * y' = r by rw [mul_assoc, ← e, inv_mul_cancel_left]]
      exact hr
  exact ncyc_exists_mul_of_mem_sup hT₁NV hx

theorem commute_of_mem_sup (hc : U3C1OuterConf G L f t T R₂ D V k) {x u : G}
    (hx : x ∈ szT₁ L T ⊔ V) (hu : u ∈ V) : x * u = u * x := by
  obtain ⟨y, hy, u', hu', rfl⟩ := hc.exists_mul_of_mem_sup hx
  have e : y * u = u * y := mem_centralizer_iff.mp (hc.le_centralizer hu) y hy
  calc y * u' * u = y * (u * u') := by rw [mul_assoc, hc.comm u' hu' u hu]
    _ = u * (y * u') := by rw [← mul_assoc, e, mul_assoc]

theorem mem_sup_of_pow_four_ne
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G}
    (hx : x ∈ szR (szT₁ L T) V t) (hx4 : x ^ 4 ≠ 1) : x ∈ szT₁ L T ⊔ V := by
  obtain ⟨htT, -, -, -, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, hsqT₁, -, hsqA₁, -⟩ := h.facts_of_card_sylow hS2
  have htC := h.mem_centralizer_szT₁
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hVc : ∀ y ∈ szT₁ L T, ∀ u ∈ V, y * u = u * y := fun y hy u hu =>
    mem_centralizer_iff.mp (hc.le_centralizer hu) y hy
  have htN : t ∈ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) :=
    h.sup_le_normalizer_sup_szT₁ hS2 hVc hc.T_le (mem_sup_left htT)
  rcases outerStep_mem_or_mul_mem ht2 htN hx with h1 | h1
  · exact h1
  · exfalso
    apply hx4
    obtain ⟨y, hy, r, hr, hyr⟩ := hc.exists_mul_of_mem_sup h1
    have hxe : x = y * r * t := by rw [hyr, mul_assoc x t t, ht2, mul_one]
    have hyt : y * t = t * y := mem_centralizer_iff.mp htC y hy
    have htr : t * r = r⁻¹ * t := by
      have := hc.inv r hr
      calc t * r = t * r * t⁻¹ * t := by group
        _ = r⁻¹ * t := by rw [this]
    have hsq1 : (y * r * t) ^ 2 = y ^ 2 := by
      calc (y * r * t) ^ 2 = y * r * (t * y) * r * t := by rw [sq]; group
        _ = y * r * (y * t) * r * t := by rw [hyt]
        _ = y * (r * y) * (t * r) * t := by group
        _ = y * (y * r) * (r⁻¹ * t) * t := by rw [← hVc y hy r hr, htr]
        _ = y * y * (t * t) := by group
        _ = y ^ 2 := by rw [ht2, mul_one, sq]
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hxe, hsq1]
    exact hsqA₁ _ (hsqT₁ y hy)

theorem normalizer_szR_le (hc : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hk : 2 ≤ k) {n : G} (hn : n ∈ normalizer (szR (szT₁ L T) V t : Set G)) :
    n ∈ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) ∧ n ∈ normalizer (V : Set G) ∧
      n ∈ normalizer (szT₁ L T : Set G) ∧ n * t * n⁻¹ * t⁻¹ ∈ V := by
  obtain ⟨-, -, -, -, hinvT₁, -, -⟩ := h.facts_of_card_sylow hS2
  have htC := h.mem_centralizer_szT₁
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hHR : szT₁ L T ⊔ V ≤ szR (szT₁ L T) V t := sup_le_szR _ _ _
  obtain ⟨a, -, b, hb, hab⟩ := hc.exists_pow_four_ne h hS2 hk
  have hb4 : b ^ 4 ≠ 1 := by simpa using (hab 0).1
  have key1 : ∀ m ∈ normalizer (szR (szT₁ L T) V t : Set G), ∀ x ∈ szT₁ L T ⊔ V,
      m * x * m⁻¹ ∈ szT₁ L T ⊔ V := by
    intro m hm x hx
    have h4 : ∀ z ∈ szT₁ L T ⊔ V, z ^ 4 ≠ 1 → m * z * m⁻¹ ∈ szT₁ L T ⊔ V := fun z hz hz4 =>
      hc.mem_sup_of_pow_four_ne h hS2 ((mem_normalizer_iff.mp hm z).mp (hHR hz))
        (outerData_conj_pow_ne_one hz4)
    by_cases hx4 : x ^ 4 = 1
    · have hxb : (x * b) ^ 4 = b ^ 4 := by
        rw [(Commute.mul_pow (hc.commute_of_mem_sup hx hb) 4), hx4, one_mul]
      have h1 := h4 (x * b) (mul_mem hx (mem_sup_right hb)) (by rw [hxb]; exact hb4)
      have h2 := h4 b⁻¹ (mem_sup_right (inv_mem hb)) (by rw [inv_pow]; exact inv_ne_one.mpr hb4)
      rw [show m * x * m⁻¹ = (m * (x * b) * m⁻¹) * (m * b⁻¹ * m⁻¹) by group]
      exact mul_mem h1 h2
    · exact h4 x hx hx4
  have hnH : n ∈ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) :=
    mem_normalizer_iff.mpr fun x => ⟨key1 n hn x, fun hx => by
      have := key1 n⁻¹ (inv_mem hn) _ hx
      rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this⟩
  have hcenV : ∀ z ∈ szT₁ L T ⊔ V, (∀ w ∈ szT₁ L T ⊔ V, z * w = w * z) → z ∈ V := by
    intro z hz hzc
    obtain ⟨y, hy, u, hu, rfl⟩ := hc.exists_mul_of_mem_sup hz
    have hyA : y ∈ szA₁ (szT₁ L T) := mem_inf.mpr ⟨hy, mem_centralizer_iff.mpr fun y' hy' => by
      have e := hzc y' (mem_sup_left hy')
      have e2 : u * y' = y' * u := (mem_centralizer_iff.mp (hc.le_centralizer hu) y' hy').symm
      have e3 : y * y' * u = y' * y * u := by
        calc y * y' * u = y * (y' * u) := by group
          _ = y * (u * y') := by rw [e2]
          _ = y * u * y' := by group
          _ = y' * (y * u) := e
          _ = y' * y * u := by group
      exact (mul_right_cancel e3).symm⟩
    exact mul_mem (hc.le hyA) hu
  have keyV : ∀ m ∈ normalizer (szR (szT₁ L T) V t : Set G), ∀ u ∈ V, m * u * m⁻¹ ∈ V := by
    intro m hm u hu
    refine hcenV _ (key1 m hm u (mem_sup_right hu)) fun w hw => ?_
    have hw' := key1 m⁻¹ (inv_mem hm) w hw
    rw [inv_inv] at hw'
    have e := hc.commute_of_mem_sup hw' hu
    calc m * u * m⁻¹ * w = m * (u * (m⁻¹ * w * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * w * m) * u) * m⁻¹ := by rw [← e]
      _ = w * (m * u * m⁻¹) := by group
  have hnV : n ∈ normalizer (V : Set G) :=
    mem_normalizer_iff.mpr fun u => ⟨keyV n hn u, fun hu => by
      have := keyV n⁻¹ (inv_mem hn) _ hu
      rwa [show n⁻¹ * (n * u * n⁻¹) * n⁻¹⁻¹ = u by group] at this⟩
  have keyt : ∀ m ∈ normalizer (szR (szT₁ L T) V t : Set G), m * t * m⁻¹ * t⁻¹ ∈ V := by
    intro m hm
    obtain ⟨htT, -, -, -, -, -, -⟩ := h.start_of_card_sylow hS2
    have hVc : ∀ y ∈ szT₁ L T, ∀ u ∈ V, y * u = u * y := fun y hy u hu =>
      mem_centralizer_iff.mp (hc.le_centralizer hu) y hy
    have htN : t ∈ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) :=
      h.sup_le_normalizer_sup_szT₁ hS2 hVc hc.T_le (mem_sup_left htT)
    have hxR : m * t * m⁻¹ ∈ szR (szT₁ L T) V t :=
      (mem_normalizer_iff.mp hm t).mp (mem_szR_right _ _ _)
    rcases outerStep_mem_or_mul_mem ht2 htN hxR with h1 | h1
    · exfalso
      have htH : t ∈ szT₁ L T ⊔ V := by
        have := key1 m⁻¹ (inv_mem hm) _ h1
        rwa [show m⁻¹ * (m * t * m⁻¹) * m⁻¹⁻¹ = t by group] at this
      apply hb4
      have e1 : t * b * t⁻¹ = b := by rw [hc.commute_of_mem_sup htH hb, mul_inv_cancel_right]
      have e3 : b⁻¹ = b := by rw [← hc.inv b hb, e1]
      have e2 : b ^ 2 = 1 := by
        rw [sq]
        calc b * b = b * b⁻¹ := by rw [e3]
          _ = 1 := mul_inv_cancel b
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e2, one_pow]
    · obtain ⟨y, hy, r, hr, hyr⟩ := hc.exists_mul_of_mem_sup h1
      have hxe : m * t * m⁻¹ = y * r * t := by
        rw [hyr, mul_assoc (m * t * m⁻¹) t t, ht2, mul_one]
      have hyt : y * t = t * y := mem_centralizer_iff.mp htC y hy
      have htr : t * r = r⁻¹ * t := by
        have := hc.inv r hr
        calc t * r = t * r * t⁻¹ * t := by group
          _ = r⁻¹ * t := by rw [this]
      have hsq1 : (y * r * t) ^ 2 = y ^ 2 := by
        calc (y * r * t) ^ 2 = y * r * (t * y) * r * t := by rw [sq]; group
          _ = y * r * (y * t) * r * t := by rw [hyt]
          _ = y * (r * y) * (t * r) * t := by group
          _ = y * (y * r) * (r⁻¹ * t) * t := by rw [← hVc y hy r hr, htr]
          _ = y * y * (t * t) := by group
          _ = y ^ 2 := by rw [ht2, mul_one, sq]
      have hx2 : (m * t * m⁻¹) ^ 2 = 1 := by
        rw [sq, show m * t * m⁻¹ * (m * t * m⁻¹) = m * (t * t) * m⁻¹ by group, ht2, mul_one,
          mul_inv_cancel]
      rw [hxe, hsq1] at hx2
      have hyA := hinvT₁ y hy hx2
      rw [hxe, show y * r * t * t⁻¹ = y * r by group]
      exact mul_mem (hc.le hyA) hr
  have keyT : ∀ m ∈ normalizer (szR (szT₁ L T) V t : Set G), ∀ y ∈ szT₁ L T,
      m * y * m⁻¹ ∈ szT₁ L T := by
    intro m hm y hy
    have hz := key1 m hm y (mem_sup_left hy)
    have hv := keyt m hm
    set v := m * t * m⁻¹ * t⁻¹ with hvdef
    have hmt : m * t * m⁻¹ = v * t := by rw [hvdef]; group
    have hyt : y * t = t * y := mem_centralizer_iff.mp htC y hy
    have hzx : m * y * m⁻¹ * (v * t) = v * t * (m * y * m⁻¹) := by
      rw [← hmt]
      calc m * y * m⁻¹ * (m * t * m⁻¹) = m * (y * t) * m⁻¹ := by group
        _ = m * (t * y) * m⁻¹ := by rw [hyt]
        _ = m * t * m⁻¹ * (m * y * m⁻¹) := by group
    have hzt : m * y * m⁻¹ * t = t * (m * y * m⁻¹) := by
      have e := hc.commute_of_mem_sup hz hv
      have e2 : v * (m * y * m⁻¹ * t) = v * (t * (m * y * m⁻¹)) := by
        calc v * (m * y * m⁻¹ * t) = (v * (m * y * m⁻¹)) * t := by group
          _ = (m * y * m⁻¹ * v) * t := by rw [← e]
          _ = m * y * m⁻¹ * (v * t) := by group
          _ = v * t * (m * y * m⁻¹) := hzx
          _ = v * (t * (m * y * m⁻¹)) := by group
      exact mul_left_cancel e2
    obtain ⟨y', hy', u', hu', hyu⟩ := hc.exists_mul_of_mem_sup hz
    rw [← hyu] at hzt ⊢
    have hy't : y' * t = t * y' := mem_centralizer_iff.mp htC y' hy'
    have hu'inv := hc.inv u' hu'
    have hu'2 : u' ^ 2 = 1 := by
      have e1 : t * (y' * u') * t⁻¹ = y' * u' := by rw [← hzt, mul_inv_cancel_right]
      have e2 : t * (y' * u') * t⁻¹ = y' * u'⁻¹ := by
        rw [show t * (y' * u') * t⁻¹ = (t * y' * t⁻¹) * (t * u' * t⁻¹) by group, hu'inv,
          show t * y' * t⁻¹ = y' by rw [← hy't, mul_inv_cancel_right]]
      rw [e1] at e2
      have e3 : u' = u'⁻¹ := mul_left_cancel e2
      rw [sq]
      nth_rewrite 2 [e3]
      exact mul_inv_cancel u'
    exact mul_mem hy' (szA₁_le _ (hc.omega u' hu' hu'2))
  refine ⟨hnH, hnV, mem_normalizer_iff.mpr fun y => ⟨keyT n hn y, fun hy => ?_⟩, keyt n hn⟩
  have := keyT n⁻¹ (inv_mem hn) _ hy
  rwa [show n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y by group] at this

theorem szR_le_u3C1U (hc : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    szR (szT₁ L T) V t ≤ u3C1U L T V t := by
  obtain ⟨-, -, hA₁, -⟩ := h.facts_of_card_sylow hS2
  have htC := h.mem_centralizer_szT₁
  have hcen : ∀ x, (∀ y ∈ szT₁ L T, x * y = y * x) → x ∈ szR (szT₁ L T) V t →
      x ∈ u3C1U L T V t := by
    intro x hx hxR
    refine ⟨Subgroup.le_normalizer hxR, mem_centralizer_iff.mpr fun a ha =>
      (hx a (szA₁_le _ ha)).symm, ?_, fun y hy => ?_⟩
    · exact centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => (hx y hy).symm)
    · rw [show x * y * x⁻¹ = y by rw [hx y hy, mul_inv_cancel_right], inv_mul_cancel]
      exact one_mem _
  refine sup_le (sup_le (fun y hy => ⟨Subgroup.le_normalizer (le_szR_left _ _ _ hy),
    mem_centralizer_iff.mpr fun a ha => (mem_centralizer_iff.mp (mem_szA₁.mp ha).2 y hy).symm,
    Subgroup.le_normalizer hy, fun z hz => ?_⟩) fun r hr => hcen r
      (fun y hy => (mem_centralizer_iff.mp (hc.le_centralizer hr) y hy).symm)
      (le_szR_mid _ _ _ hr)) (zpowers_le.mpr
        (hcen t (fun y hy => (mem_centralizer_iff.mp htC y hy).symm) (mem_szR_right _ _ _)))
  rw [hA₁, show z⁻¹ * (y * z * y⁻¹) = ⁅z⁻¹, y⁆ by rw [commutatorElement_def, inv_inv]; group]
  exact commutator_mem_commutator (inv_mem hz) hy

theorem u3C1U_inf_centralizer
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    u3C1U L T V t ⊓ centralizer ({t} : Set G) = szT₁ L T ⊔ zpowers t := by
  have htC := h.mem_centralizer_szT₁
  apply le_antisymm
  · rintro x ⟨hxU, hxt⟩
    have hxA : x ∈ normalizer (szA L T t : Set G) := by
      refine U3Start.mem_normalizer_szA_of_conj_t_mem (b := 1)
        (centralizer_le_normalizer _ hxU.2.1) (one_mem _) ?_
      rw [mem_centralizer_singleton_iff.mp hxt, mul_inv_cancel_right, one_mul]
    rw [← h.u3R₁_inf_centralizer_of_card_sylow hS2]
    exact ⟨u3C1U_inf_normalizer_le ⟨hxU, hxA⟩, hxt⟩
  · refine le_inf ((sup_le (le_szR_left _ _ _) (zpowers_le.mpr (mem_szR_right _ _ _))).trans
      (hc.szR_le_u3C1U h hS2)) (sup_le (fun y hy => ?_) (zpowers_le.mpr ?_))
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htC y hy)
    · exact mem_centralizer_singleton_iff.mpr rfl

theorem le_normalizer_u3C1U_of_two_le
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) :
    normalizer (szR (szT₁ L T) V t : Set G) ≤ normalizer (u3C1U L T V t : Set G) :=
  le_normalizer_u3C1U (fun _ hn => (hc.normalizer_szR_le h hS2 hk hn).2.2.1)
    (fun _ hn => normalizer_le_normalizer_inf_centralizer _ (hc.normalizer_szR_le h hS2 hk hn).2.2.1)

theorem conj_t_not_mem_u3C1U
    (hc : U3C1OuterConf G L f t T R₂ D V k) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hk : 2 ≤ k) {u : G}
    (hu : u ∈ u3C1U L T V t) (huR : u ∉ szR (szT₁ L T) V t) : u * t * u⁻¹ ∉ szA L T t := by
  intro huA
  obtain ⟨-, hA₁card, -, -, -, hsqA₁, -⟩ := h.facts_of_card_sylow hS2
  have htC := h.mem_centralizer_szT₁
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨a, -, b, hb, hab⟩ := hc.exists_pow_four_ne h hS2 hk
  have hb4 : b ^ 4 ≠ 1 := by simpa using (hab 0).1
  have hv := (hc.normalizer_szR_le h hS2 hk hu.1).2.2.2
  set v := u * t * u⁻¹ * t⁻¹ with hvdef
  have htA : t ∈ szA L T t := mem_sup_right (mem_zpowers t)
  have hvA : v ∈ szA L T t := mul_mem huA (inv_mem htA)
  have htA₁ : t ∈ centralizer (szA₁ (szT₁ L T) : Set G) := centralizer_le (szA₁_le _) htC
  obtain ⟨a₁, ha₁, z, hz, haz⟩ := exists_mul_eq_of_mem_sup_zpowers htA₁ hvA
  have hvA₁ : v ∈ szA₁ (szT₁ L T) := by
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    · rw [← haz, hz1, mul_one]; exact ha₁
    · exfalso
      rw [hz1] at haz
      have htV : t ∈ V := by
        rw [show t = a₁⁻¹ * v by rw [← haz]; group]
        exact mul_mem (inv_mem (hc.le ha₁)) hv
      apply hb4
      have e1 : t * b * t⁻¹ = b := by rw [hc.comm t htV b hb, mul_inv_cancel_right]
      have e3 : b⁻¹ = b := by rw [← hc.inv b hb, e1]
      have e2 : b ^ 2 = 1 := by
        rw [sq]
        calc b * b = b * b⁻¹ := by rw [e3]
          _ = 1 := mul_inv_cancel b
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e2, one_pow]
  obtain ⟨z₀, hz₀, hz₀v⟩ := pushUp_exists_pow_eq hc.comm (pow_pos (by norm_num) f) hc.card hc.pow
    hc.omega (le_of_eq hA₁card) (show 1 ≤ k + 1 by omega) (hc.le hvA₁)
    (by rw [pow_one]; exact hsqA₁ v hvA₁)
  set s := z₀ ^ 2 ^ (k - 1) with hsdef
  have hsV : s ∈ V := pow_mem hz₀ _
  have hs2 : s ^ 2 = v := by
    rw [hsdef, ← pow_mul, show 2 ^ (k - 1) * 2 = 2 ^ (k + 1 - 1) by
      rw [← pow_succ]; congr 1; omega, hz₀v]
  have hst : s * t * s⁻¹ = v * t := by
    have h1 := hc.inv s hsV
    calc s * t * s⁻¹ = s * (t * s⁻¹ * t⁻¹) * t := by group
      _ = s * (t * s * t⁻¹)⁻¹ * t := by group
      _ = s * s * t := by rw [h1, inv_inv]
      _ = v * t := by rw [← hs2, sq]
  have hsU : s ∈ u3C1U L T V t := hc.szR_le_u3C1U h hS2 (le_szR_mid _ _ _ hsV)
  have hc' : s⁻¹ * u ∈ u3C1U L T V t ⊓ centralizer ({t} : Set G) := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hsU) hu, mem_centralizer_singleton_iff.mpr ?_⟩
    have e : u * t * u⁻¹ = s * t * s⁻¹ := by rw [hst, hvdef]; group
    calc s⁻¹ * u * t = s⁻¹ * (u * t * u⁻¹) * u := by group
      _ = s⁻¹ * (s * t * s⁻¹) * u := by rw [e]
      _ = t * (s⁻¹ * u) := by group
  rw [hc.u3C1U_inf_centralizer h hS2] at hc'
  apply huR
  rw [show u = s * (s⁻¹ * u) by group]
  exact mul_mem (le_szR_mid _ _ _ hsV)
    ((sup_le (le_szR_left _ _ _) (zpowers_le.mpr (mem_szR_right _ _ _))) hc')

end U3C1OuterConf

@[expose] def U3C1OuterLevelHighRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V : Subgroup G) (k : ℕ), U3C1OuterStepHyp G L f t T R₂ D d V k → U3C1CartanFpf L T D d →
    2 ≤ k →
    CFSG.ABGLocalTools.IsSylowOf 2 (u3C1U L T V t ⊔ T) (normalizer (szR (szT₁ L T) V t : Set G)) ∧
    Nat.card (u3C1U L T V t) = 2 * (2 ^ f) ^ (k + 4) ∧
    ∃ U₁ : Subgroup G, U₁ ≤ u3C1U L T V t ∧ u3C1U L T V t ≤ normalizer (U₁ : Set G) ∧
      U₁ ⊔ zpowers t = u3C1U L T V t ∧ t ∉ U₁ ∧ U₁ ⊓ szR (szT₁ L T) V t = szT₁ L T ⊔ V ∧
      D ≤ normalizer (U₁ : Set G) ∧ T ≤ normalizer (U₁ : Set G) ∧
      ∀ u ∈ U₁, ∀ r ∈ V, r⁻¹ * (u * r * u⁻¹) ∈ szA₁ (szT₁ L T)

theorem u3C1OuterLevelDataHighInput_of_rest
    (hrest : U3C1OuterLevelHighRestInput) : U3C1OuterLevelDataHighInput := by
  intro G _ _ L f t T R₂ D d V k H hC hk
  obtain ⟨hsyl, hcard, U₁, hU₁U, hUU₁, hsup, htU₁, hinf, hDU₁, hTU₁, hV₁⟩ :=
    hrest G L f t T R₂ D d V k H hC hk
  obtain ⟨e, heD, heA, hefpf⟩ := hC.fpf
  have hc := H.conf
  have h := H.start
  have hS2 := H.card_sylow
  exact ⟨u3C1U L T V t, U₁,
    { U_le := u3C1U_le_normalizer
      U_normal := hc.le_normalizer_u3C1U_of_two_le h hS2 hk
      isSylowOf := hsyl
      card_U := hcard
      szR_le := hc.szR_le_u3C1U h hS2
      conj_t_not_mem := fun u hu huR => hc.conj_t_not_mem_u3C1U h hS2 hk hu huR
      conj_szA₁ := fun u hu b hb => U3Start.conj_szA₁_of_mem_u3C1U hu hb
      conj_T₁ := fun u hu y hy => hu.2.2.2 y hy
      conj_V₁ := hV₁
      inf_centralizer := hc.u3C1U_inf_centralizer h hS2
      U₁_le := hU₁U
      U₁_normal := hUU₁
      sup_eq := hsup
      t_not_mem := htU₁
      inf_eq := hinf
      D_le := hDU₁
      T_le := hTU₁
      torus := hc.torus_of_mem h hC.toU3C1Cartan hDU₁ heD heA hefpf }⟩

section Certificates



theorem u3C1NcycSylowStageInput_of_rest (hrest : U3C1OuterLevelHighRestInput)
    (hM1 : U3C1OuterMuOneInput) (hM1S : U3C1OuterMuOneSylowInput) : U3C1NcycSylowStageInput :=
  u3C1NcycSylowStageInput_of_high (u3C1OuterLevelDataHighInput_of_rest hrest) hM1 hM1S

end Certificates

end CFSG.SeitzReduction.RankOne
