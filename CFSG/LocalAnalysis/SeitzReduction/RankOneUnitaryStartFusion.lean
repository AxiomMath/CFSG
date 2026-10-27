module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStartOuter

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.GH74.Uniqueness.Bender

theorem exists_mem_inf_center_of_isPGroup {G : Type*} [Group G] [Finite G] {T U : Subgroup G}
    (hT : IsPGroup 2 T) (hUT : U ≤ T) (hUn : T ≤ normalizer (U : Set G)) (hU : U ≠ ⊥) :
    ∃ a ∈ U, a ∈ centralizer (T : Set G) ∧ a ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hyU, hyZ⟩ := mem_inf.1 hy
  refine ⟨y, mem_subgroupOf.1 hyU, mem_centralizer_iff.2 fun s hs => ?_, fun h1 => hy1 ?_⟩
  · exact congrArg Subtype.val (mem_center_iff.1 hyZ ⟨s, hs⟩)
  · exact Subtype.ext (Subtype.ext h1)

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_mem_szA₁_inf_center_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ a ∈ szA₁ (szT₁ L T), a ∈ centralizer (T : Set G) ∧ a ≠ 1 := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  refine exists_mem_inf_center_of_isPGroup h.isPGroup ((szA₁_le _).trans (szT₁_le_left L T))
    (fun n hn => ?_) ?_
  · refine mem_normalizer_iff.mpr fun x => ⟨fun hx =>
      conj_mem_inf_centralizer_of_mem_normalizer (hTN₁ hn) hx, fun hx => ?_⟩
    have := conj_mem_inf_centralizer_of_mem_normalizer (inv_mem (hTN₁ hn)) hx
    rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this
  · intro hbot
    rw [hbot, card_bot] at hA₁card
    have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.two_le; omega)
    omega

theorem exists_cartan_conj_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {b b' : G}
    (hb : b ∈ szA₁ (szT₁ L T)) (hb1 : b ≠ 1) (hb' : b' ∈ szA₁ (szT₁ L T)) (hb1' : b' ≠ 1) :
    ∃ d ∈ L, b' = d⁻¹ * b * d ∧ d * t = t * d ∧
      d ∈ normalizer (szT₁ L T : Set G) ∧ d ∈ normalizer (szA L T t : Set G) := by
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  have hbL : b ∈ L := szT₁_le_right L T (szA₁_le _ hb)
  have hbL' : b' ∈ L := szT₁_le_right L T (szA₁_le _ hb')
  obtain ⟨d, hd, hdd⟩ := hc.exists_cartan_conj ((hmemZ ⟨b, hbL⟩).mpr hb)
    (fun h1 => hb1 (congrArg Subtype.val h1)) ((hmemZ ⟨b', hbL'⟩).mpr hb')
    (fun h1 => hb1' (congrArg Subtype.val h1))
  have hdN : d ∈ borel (Q : Subgroup L) := cartan_le_borel _ _ hd
  have hdT₁ : (d : G) ∈ normalizer (szT₁ L T : Set G) := by
    refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · have hyL : y ∈ L := szT₁_le_right L T hy
      have h1 := (mem_normalizer_iff.mp hdN ⟨y, hyL⟩).mp ((hmemQ ⟨y, hyL⟩).mpr hy)
      have h2 := (hmemQ _).mp h1
      simpa using h2
    · have hyL : y ∈ L := by
        have h1 : (d : G) * y * (d : G)⁻¹ ∈ L := szT₁_le_right L T hy
        have h2 := mul_mem (mul_mem (inv_mem d.2) h1) d.2
        simpa [mul_assoc] using h2
      have h1 : d * ⟨y, hyL⟩ * d⁻¹ ∈ (Q : Subgroup L) := (hmemQ _).mpr (by simpa using hy)
      exact (hmemQ ⟨y, hyL⟩).mp ((mem_normalizer_iff.mp hdN ⟨y, hyL⟩).mpr h1)
  have hdt : (d : G) * t = t * d := mem_centralizer_iff.mp h.mem d d.2
  have hdA₁ : (d : G) ∈ normalizer (szA₁ (szT₁ L T) : Set G) := by
    refine mem_normalizer_iff.mpr fun x => ⟨fun hx =>
      conj_mem_inf_centralizer_of_mem_normalizer hdT₁ hx, fun hx => ?_⟩
    have := conj_mem_inf_centralizer_of_mem_normalizer (inv_mem hdT₁) hx
    rwa [show (d : G)⁻¹ * (d * x * (d : G)⁻¹) * (d : G)⁻¹⁻¹ = x by group] at this
  have hdz : (d : G) ∈ normalizer ((zpowers t : Subgroup G) : Set G) := by
    rw [normalizer_zpowers_eq_centralizer_of_involution h.inv]
    exact mem_centralizer_singleton_iff.mpr hdt
  refine ⟨d, d.2, ?_, hdt, hdT₁, ?_⟩
  · have := congrArg Subtype.val hdd
    simpa using this
  · rw [szA, mem_normalizer_iff_map_conj_eq] at *
    rw [Subgroup.map_sup, hdA₁, hdz]

theorem conj_not_mem_szA₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (g : G) :
    g⁻¹ * t * g ∉ szA₁ (szT₁ L T) := by
  intro hg
  obtain ⟨-, -, -, -, hdisj, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, hcomm, -⟩ := h.facts_of_card_sylow hS2
  have hTT := h.commutator_le_szT₁_of_card_sylow hS2
  obtain ⟨a, ha, haZ, ha1⟩ := h.exists_mem_szA₁_inf_center_of_card_sylow hS2
  have hg1 : g⁻¹ * t * g ≠ 1 := by
    intro h1
    have : t = 1 := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have h2 := h.inv
    rw [this, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨d, -, had, -, -, -⟩ := h.exists_cartan_conj_of_card_sylow hS2 hg hg1 ha ha1
  have hTa : T ≤ centralizer ({(g * d)⁻¹ * t * (g * d)} : Set G) := by
    intro y hy
    rw [show (g * d)⁻¹ * t * (g * d) = d⁻¹ * (g⁻¹ * t * g) * d by group, ← had]
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp haZ y hy)
  obtain ⟨n, hn, hnt⟩ := exists_mem_normalizer_inv_mul_mul_eq h.le h.sylow hTa
  have haTT : a ∈ ⁅T, T⁆ := by
    rw [hcomm] at ha
    exact commutator_mono (szT₁_le_left L T) (szT₁_le_left L T) ha
  have h1 := conj_mem_commutator_of_mem_normalizer hn haTT
  rw [had, show d⁻¹ * (g⁻¹ * t * g) * d = (g * d)⁻¹ * t * (g * d) by group, ← hnt,
    show n * (n⁻¹ * t * n) * n⁻¹ = t by group] at h1
  have ht1 : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨hTT h1, mem_zpowers t⟩
  rw [hdisj, mem_bot] at ht1
  have h2 := h.inv
  rw [ht1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem exists_normalizer_conj_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {g : G} (hg : g⁻¹ * t * g ∈ szA L T t) :
    (∃ b ∈ szA₁ (szT₁ L T), g⁻¹ * t * g = b * t) ∧
      ∃ n ∈ normalizer (szA L T t : Set G), n⁻¹ * t * n = g⁻¹ * t * g := by
  have hchar := h.normalizer_le_normalizer_szA_of_card_sylow hS2
  have htA₁ : t ∈ centralizer (szA₁ (szT₁ L T) : Set G) :=
    centralizer_le (szA₁_le _) h.mem_centralizer_szT₁
  obtain ⟨b, hb, z, hz, hbz⟩ := exists_mul_eq_of_mem_sup_zpowers htA₁ hg
  have hzt : z = t := by
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with rfl | rfl
    · exfalso
      rw [mul_one] at hbz
      exact h.conj_not_mem_szA₁_of_card_sylow hS2 g (hbz ▸ hb)
    · rfl
  rw [hzt] at hbz
  refine ⟨⟨b, hb, hbz.symm⟩, ?_⟩
  by_cases hb1 : b = 1
  · refine ⟨1, one_mem _, ?_⟩
    rw [← hbz, hb1]
    group
  obtain ⟨a, ha, haZ, ha1⟩ := h.exists_mem_szA₁_inf_center_of_card_sylow hS2
  obtain ⟨d, -, had, hdt, -, hdA⟩ := h.exists_cartan_conj_of_card_sylow hS2 hb hb1 ha ha1
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have htZ : t ∈ centralizer (T : Set G) :=
    mem_centralizer_iff.mpr fun y hy => (mem_centralizer_singleton_iff.mp (h.le hy))
  have hconj : d⁻¹ * (g⁻¹ * t * g) * d = a * t := by
    rw [← hbz, had]
    calc d⁻¹ * (b * t) * d = d⁻¹ * b * d * (d⁻¹ * (t * d)) := by group
      _ = d⁻¹ * b * d * t := by rw [← hdt]; group
  have hTa : T ≤ centralizer ({(g * d)⁻¹ * t * (g * d)} : Set G) := by
    intro y hy
    rw [show (g * d)⁻¹ * t * (g * d) = d⁻¹ * (g⁻¹ * t * g) * d by group, hconj]
    refine mem_centralizer_singleton_iff.mpr ?_
    have e1 := (mem_centralizer_iff.mp haZ y hy)
    have e2 := (mem_centralizer_iff.mp htZ y hy)
    calc y * (a * t) = (y * a) * t := by group
      _ = (a * y) * t := by rw [e1]
      _ = a * (y * t) := by group
      _ = a * (t * y) := by rw [e2]
      _ = a * t * y := by group
  obtain ⟨n₀, hn₀, hn₀t⟩ := exists_mem_normalizer_inv_mul_mul_eq h.le h.sylow hTa
  refine ⟨n₀ * d⁻¹, mul_mem (hchar hn₀) (inv_mem hdA), ?_⟩
  calc (n₀ * d⁻¹)⁻¹ * t * (n₀ * d⁻¹) = d * (n₀⁻¹ * t * n₀) * d⁻¹ := by group
    _ = g⁻¹ * t * g := by rw [hn₀t]; group

end U3Start

end CFSG.SeitzReduction.RankOne
