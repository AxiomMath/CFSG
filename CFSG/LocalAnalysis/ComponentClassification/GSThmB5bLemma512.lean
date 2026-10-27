module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma57
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma517

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise commutatorElement

@[expose] def SuzukiTausskyInput : Prop :=
  ∀ (P : Type) [Group P] [Finite P], IsPGroup 2 P → 8 ≤ Nat.card P → ∀ b : P, orderOf b = 2 →
    Nat.card (centralizer ({b} : Set P)) = 4 →
    ∃ p r : P, closure {p, r} = ⊤ ∧ 2 * orderOf p = Nat.card P ∧ r ^ 2 = 1 ∧
      (r * p * r⁻¹ = p⁻¹ ∨ r * p * r⁻¹ = p ^ (orderOf p / 2 - 1))

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem T_eq : h.T = h.P ⊓ normalizer (h.B : Set H) := by
  ext y
  simp only [Hyp52.T, Hyp52.Q, Hyp52.P, mem_inf]
  tauto

theorem T_eq_centralizer {b : H} (hB : h.B = zpowers b) (hb : orderOf b = 2) :
    h.T = h.P ⊓ centralizer ({b} : Set H) := by
  rw [h.T_eq]
  congr 1
  ext y
  rw [mem_centralizer_singleton_iff, hB]
  constructor
  · intro hy
    have h1 : y * b * y⁻¹ ∈ zpowers b := (mem_normalizer_iff.mp hy b).mp (mem_zpowers b)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    have hb2 : b ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, ← hb, pow_orderOf_eq_one]
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [show m + m = 2 * m by ring, zpow_mul, hb2, one_zpow] at hk
      exfalso
      have : b = 1 := by
        calc b = y⁻¹ * (y * b * y⁻¹) * y := by group
          _ = 1 := by rw [← hk]; group
      rw [this, orderOf_one] at hb
      exact absurd hb (by norm_num)
    · rw [zpow_add_one, zpow_mul, hb2, one_zpow, one_mul] at hk
      calc y * b = (y * b * y⁻¹) * y := by group
        _ = b * y := by rw [← hk]
  · intro hy
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute b y from hy.symm) k).eq

end Hyp52

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem index_two_structure (hB7 : EmbedsTQuotStatement)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) :
    ∃ b : H, h.B = zpowers b ∧ orderOf b = 2 ∧ Nat.card h.T = 4 ∧
      h.T = zpowers h.a ⊔ zpowers b ∧ h.T = h.P ⊓ centralizer ({b} : Set H) := by
  obtain ⟨f, hf⟩ := hB7 H h
  have hcardB : Nat.card h.B ≤ 2 := hT ▸ Nat.card_le_card_of_injective f hf
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.B_ne_bot
  have hb1' : b ≠ 1 := fun he => hb1 (Subtype.ext he)
  have hdvd : orderOf b ∣ Nat.card h.B := by
    rw [← Subgroup.orderOf_mk b hbB]
    exact orderOf_dvd_natCard _
  have hpos : 0 < Nat.card h.B := Nat.card_pos
  have hob1 : orderOf b ≠ 1 := fun he => hb1' (orderOf_eq_one_iff.mp he)
  have hcB2 : Nat.card h.B = 2 := by
    have := Nat.le_of_dvd hpos hdvd
    have hob0 : 0 < orderOf b := orderOf_pos b
    interval_cases hc : Nat.card h.B
    · exfalso; interval_cases hob : orderOf b; exact hob1 rfl
    · rfl
  have hb2 : orderOf b = 2 := by
    rw [hcB2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd h1 hob1
    · exact h1
  have hBb : h.B = zpowers b := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hbB)
    rw [Nat.card_zpowers, hb2, hcB2]
  have hBT := h.toHyp52.B_le_T
  have hcT : Nat.card h.T = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (h.B.subgroupOf h.T)
    have h2 : Nat.card (h.B.subgroupOf h.T) = Nat.card h.B := by
      rw [← Subgroup.card_map_of_injective h.T.subtype_injective, subgroupOf_map_subtype,
        inf_of_le_left hBT]
    rw [h1, hT, h2, hcB2]
  have haT : h.a ∈ h.T := mem_inf.mpr ⟨mem_inf.mpr ⟨h.toHyp52.a_mem_S, h.a_mem_normalizer⟩,
    h.toHyp52.a_mem_P⟩
  have hsup : h.T = zpowers h.a ⊔ zpowers b := by
    have hle : zpowers h.a ⊔ zpowers b ≤ h.T :=
      sup_le (zpowers_le.mpr haT) (hBb ▸ hBT)
    have hlt : zpowers b < zpowers h.a ⊔ zpowers b := by
      refine lt_of_le_of_ne le_sup_right fun he => h.toHyp52.a_not_mem_B ?_
      rw [hBb, he]
      exact mem_sup_left (mem_zpowers _)
    have hc1 := Subgroup.card_lt_of_lt hlt
    rw [Nat.card_zpowers, hb2] at hc1
    have hc2 := Subgroup.card_dvd_of_le hle
    rw [hcT] at hc2
    have hc3 : Nat.card ↥(zpowers h.a ⊔ zpowers b) = 4 := by
      have hle4 := Nat.le_of_dvd (by norm_num) hc2
      interval_cases hc : Nat.card ↥(zpowers h.a ⊔ zpowers b)
      · exact absurd hc2 (by norm_num)
      · rfl
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcT, hc3])).symm
  exact ⟨b, hBb, hb2, hcT, hsup, h.toHyp52.T_eq_centralizer hBb hb2⟩

theorem mem_T_cases {b : H} (hb : orderOf b = 2) (hT : h.T = zpowers h.a ⊔ zpowers b)
    (hab : h.a * b = b * h.a) {y : H} (hy : y ∈ h.T) :
    y = 1 ∨ y = h.a ∨ y = b ∨ y = h.a * b := by
  have hle : zpowers h.a ≤ normalizer ((zpowers b : Subgroup H) : Set H) := by
    refine zpowers_le.mpr (centralizer_le_normalizer _ ?_)
    rw [mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute b h.a from hab.symm) k).eq
  rw [hT] at hy
  have hy' : y ∈ (zpowers h.a : Set H) * (zpowers b : Set H) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hy
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hy'
  have ha2 : h.a ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have hb2 : b ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, ← hb, pow_orderOf_eq_one]
  have key : ∀ {c : H}, c ^ (2 : ℤ) = 1 → ∀ w ∈ zpowers c, w = 1 ∨ w = c := by
    intro c hc w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left; rw [show m + m = 2 * m by ring, zpow_mul, hc, one_zpow]
    · right; rw [zpow_add_one, zpow_mul, hc, one_zpow, one_mul]
  rcases key ha2 u hu with rfl | rfl <;> rcases key hb2 v hv with rfl | rfl <;> simp

theorem a_mem_commutator_of_index_two (hB7 : EmbedsTQuotStatement)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) : h.a ∈ ⁅h.S, h.S⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hBb, hb, -, hTab, hTC⟩ := h.index_two_structure hB7 hT
  have hbB : b ∈ h.B := hBb ▸ mem_zpowers b
  have hbP : b ∈ h.P := h.toHyp52.B_le_P hbB
  have hbS : b ∈ h.S := h.toHyp52.P_le_S hbP
  have hab : h.a * b = b * h.a := (h.toHyp52.comm_a hbS).symm
  have hb1 : b ≠ 1 := fun he => by rw [he, orderOf_one] at hb; exact absurd hb (by norm_num)
  by_cases hP : h.P ≤ centralizer ({b} : Set H)
  ·
    have hPT : h.P = h.T := by rw [hTC, inf_of_le_left hP]
    have hxb : h.x⁻¹ * b * h.x ∈ h.T := by
      rw [← hPT]
      have := h.toHyp52.conj_mem_P (inv_mem h.x_mem) hbP
      rwa [inv_inv] at this
    rcases h.mem_T_cases hb hTab hab hxb with h1 | h1 | h1 | h1
    · exfalso; apply hb1
      calc b = h.x * (h.x⁻¹ * b * h.x) * h.x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · exfalso; apply h.toHyp52.a_not_mem_B
      have : b = h.a := by
        calc b = h.x * (h.x⁻¹ * b * h.x) * h.x⁻¹ := by group
          _ = h.x * h.a * h.x⁻¹ := by rw [h1]
          _ = h.a := by rw [h.toHyp52.x_comm_a, mul_inv_cancel_right]
      rw [← this]; exact hbB
    · exfalso; apply hb1
      have hbx : b ∈ conjugate h.B h.x := by
        rw [mem_conjugate_iff]
        have : h.x * b * h.x⁻¹ = b := by
          calc h.x * b * h.x⁻¹ = h.x * (h.x⁻¹ * b * h.x) * h.x⁻¹ := by rw [h1]
            _ = b := by group
        rw [this]; exact hbB
      exact mem_bot.mp (h.inf_conjugate_x ▸ mem_inf.mpr ⟨hbB, hbx⟩)
    · have hc : ⁅b⁻¹, h.x⁻¹⁆ ∈ ⁅h.S, h.S⁆ :=
        Subgroup.commutator_mem_commutator (inv_mem hbS) (inv_mem h.x_mem)
      have : ⁅b⁻¹, h.x⁻¹⁆ = h.a := by
        rw [commutatorElement_def, inv_inv, inv_inv]
        calc b⁻¹ * h.x⁻¹ * b * h.x = b⁻¹ * (h.x⁻¹ * b * h.x) := by group
          _ = b⁻¹ * (h.a * b) := by rw [h1]
          _ = h.a := by rw [hab]; group
      rw [← this]; exact hc
  ·
    obtain ⟨p, hpP, hpb⟩ : ∃ p ∈ h.P, ¬ p * b = b * p := by
      by_contra hc
      push Not at hc
      exact hP fun p hp => mem_centralizer_singleton_iff.mpr (hc p hp)
    set N : Subgroup h.P := commutator ↥h.P with hN
    have hN1 : N ≠ ⊥ := by
      intro hb'
      apply hpb
      have hc : ⁅(⟨p, hpP⟩ : h.P), ⟨b, hbP⟩⁆ ∈ N :=
        Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
      rw [hb', mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact congrArg Subtype.val hc
    have hP2 : IsPGroup 2 ↥h.P := h.toHyp52.isPGroup_S.to_le h.toHyp52.P_le_S
    have hnil : Group.IsNilpotent ↥h.P := hP2.isNilpotent
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hN1)
    obtain ⟨huN, huZ⟩ := mem_inf.mp u.2
    have huc : ∀ q ∈ h.P, q * ((u : h.P) : H) = ((u : h.P) : H) * q := fun q hq =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp huZ ⟨q, hq⟩)
    have huT : ((u : h.P) : H) ∈ h.T := by
      rw [hTC]
      exact mem_inf.mpr ⟨(u : h.P).2, mem_centralizer_singleton_iff.mpr (huc b hbP).symm⟩
    have hu1' : ((u : h.P) : H) ≠ 1 := fun he => hu1 (Subtype.ext (Subtype.ext he))
    have hua : ((u : h.P) : H) = h.a := by
      rcases h.mem_T_cases hb hTab hab huT with h1 | h1 | h1 | h1
      · exact absurd h1 hu1'
      · exact h1
      · exfalso; apply hP
        intro q hq
        rw [mem_centralizer_singleton_iff, ← h1]
        exact huc q hq
      · exfalso; apply hP
        intro q hq
        rw [mem_centralizer_singleton_iff]
        have h2 := huc q hq
        rw [h1] at h2
        have h3 : q * h.a = h.a * q := h.toHyp52.comm_a (h.toHyp52.P_le_S hq)
        have h4 : h.a * (q * b) = h.a * (b * q) := by
          calc h.a * (q * b) = (q * h.a) * b := by rw [h3]; group
            _ = q * (h.a * b) := by group
            _ = (h.a * b) * q := h2
            _ = h.a * (b * q) := by group
        exact mul_left_cancel h4
    have huPP : ((u : h.P) : H) ∈ ⁅h.P, h.P⁆ := by
      have h1 : (commutator ↥h.P).map h.P.subtype = ⁅h.P, h.P⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype]
      rw [← h1]
      exact mem_map_of_mem _ huN
    rw [← hua]
    exact Subgroup.commutator_mono h.toHyp52.P_le_S h.toHyp52.P_le_S huPP

theorem card_centralizer_in_P {b : H} (hbP : b ∈ h.P) (hT4 : Nat.card h.T = 4)
    (hTC : h.T = h.P ⊓ centralizer ({b} : Set H)) :
    Nat.card (centralizer ({(⟨b, hbP⟩ : h.P)} : Set h.P)) = 4 := by
  have hmap : (centralizer ({(⟨b, hbP⟩ : h.P)} : Set h.P)).map h.P.subtype =
      h.P ⊓ centralizer ({b} : Set H) := by
    ext y
    simp only [mem_map, mem_centralizer_singleton_iff, mem_inf, subtype_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, congrArg Subtype.val hz⟩
    · rintro ⟨hyP, hy⟩
      exact ⟨⟨y, hyP⟩, Subtype.ext hy, rfl⟩
  rw [← hT4, hTC, ← hmap, Subgroup.card_map_of_injective h.P.subtype_injective]

theorem dihedral_of_index_two (hB7 : EmbedsTQuotStatement) (hST : SuzukiTausskyInput)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) (h8 : 8 ≤ Nat.card h.P) :
    ∃ p r : H, p ∈ h.P ∧ r ∈ h.P ∧ closure {p, r} = h.P ∧ 2 * orderOf p = Nat.card h.P ∧
      r ^ 2 = 1 ∧ (r * p * r⁻¹ = p⁻¹ ∨ r * p * r⁻¹ = p ^ (orderOf p / 2 - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hBb, hb, hT4, -, hTC⟩ := h.index_two_structure hB7 hT
  have hbP : b ∈ h.P := h.toHyp52.B_le_P (hBb ▸ mem_zpowers b)
  have hP2 : IsPGroup 2 ↥h.P := h.toHyp52.isPGroup_S.to_le h.toHyp52.P_le_S
  obtain ⟨p, r, hcl, hp, hr, hrel⟩ := hST _ hP2 h8 ⟨b, hbP⟩ (by rw [Subgroup.orderOf_mk, hb])
    (h.card_centralizer_in_P hbP hT4 hTC)
  refine ⟨p, r, p.2, r.2, ?_, by rw [Subgroup.orderOf_coe, hp], by
    rw [← Subgroup.coe_pow, hr, OneMemClass.coe_one], ?_⟩
  · have h1 := congrArg (Subgroup.map h.P.subtype) hcl
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype] at h1
    have h2 : (h.P.subtype '' {p, r} : Set H) = {(p : H), (r : H)} := by
      simp [Set.image_insert_eq, Set.image_singleton]
    rw [h2] at h1
    exact h1
  · rcases hrel with h1 | h1
    · left
      have := congrArg Subtype.val h1
      simpa using this
    · right
      have := congrArg Subtype.val h1
      simpa [Subgroup.orderOf_coe] using this

theorem P_eq_T_of_card_lt (hB7 : EmbedsTQuotStatement)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) (h8 : Nat.card h.P < 8) : h.P = h.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, -, -, hT4, -, hTC⟩ := h.index_two_structure hB7 hT
  have hP2 : IsPGroup 2 ↥h.P := h.toHyp52.isPGroup_S.to_le h.toHyp52.P_le_S
  have hTP : h.T ≤ h.P := hTC ▸ inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
  have h4 : 4 ≤ Nat.card h.P := hT4 ▸ Subgroup.card_le_of_le hTP
  have hc : Nat.card h.P = 4 := by
    rw [hk] at h4 h8 ⊢
    have hk2 : k = 2 := by
      rcases Nat.lt_or_ge k 3 with hk3 | hk3
      · interval_cases k <;> simp_all
      · exfalso
        have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
        omega
    rw [hk2]; norm_num
  exact (Subgroup.eq_of_le_of_card_ge hTP (by rw [hc, hT4])).symm

end Hyp59

end CFSG.ComponentClassification.GSThmB
