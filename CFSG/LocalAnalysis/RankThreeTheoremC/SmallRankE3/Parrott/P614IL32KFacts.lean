module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32Parab
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IKFact
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G] {M B H S K : Subgroup G} {z b : G} {f : ↥K →* GL32}

theorem L32Data.b_pow (h : L32Data M B H S K z b f) : b ^ 3 = 1 := h.B_exp b h.b_mem

theorem L32Data.b_ne_one (h : L32Data M B H S K z b f) : b ≠ 1 := fun h1 =>
  h.b_not_mem (h1 ▸ one_mem _)

theorem L32Data.b_mem_H (h : L32Data M B H S K z b f) : b ∈ H := h.B_le h.b_mem

theorem L32Data.B_eq (h : L32Data M B H S K z b f) : B = zpowers z ⊔ zpowers b := by
  have hle : zpowers z ⊔ zpowers b ≤ B := sup_le (zpowers_le.2 h.z_mem_B) (zpowers_le.2 h.b_mem)
  have hlt : zpowers z < zpowers z ⊔ zpowers b :=
    lt_of_le_of_ne le_sup_left fun he => h.b_not_mem (he ▸ mem_sup_right (mem_zpowers b))
  have h3 : Nat.card (zpowers z) = 3 := by rw [Nat.card_zpowers, h.z_order]
  have hd : Nat.card ↥(zpowers z ⊔ zpowers b) ∣ 9 := h.B_card ▸ card_dvd_of_le hle
  have hd3 : 3 ∣ Nat.card ↥(zpowers z ⊔ zpowers b) := h3 ▸ card_dvd_of_le le_sup_left
  have hgt : 3 < Nat.card ↥(zpowers z ⊔ zpowers b) := h3 ▸ Subgroup.card_lt_of_lt hlt
  have h9 : Nat.card ↥(zpowers z ⊔ zpowers b) = 9 := by
    have hle9 := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : Nat.card ↥(zpowers z ⊔ zpowers b) <;> simp_all
  exact (eq_of_le_of_card_ge hle (by rw [h9, h.B_card])).symm

theorem L32Data.b_mem_normalizer_X (h : L32Data M B H S K z b f) :
    b ∈ normalizer ((K ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
  h.H_le_normalizer_X h.b_mem_H

theorem L32Data.exists_noncomm (h : L32Data M B H S K z b f) :
    ∃ x ∈ K ⊔ pCoreOf 2 H, b * x ≠ x * b := by
  by_contra hcon
  push Not at hcon
  have hbO : b ∈ pCoreOf 2 H := h.charTwo H h.twoLocal ⟨h.b_mem_H,
    mem_centralizer_iff.2 fun o ho => (hcon o (mem_sup_right ho)).symm⟩
  obtain ⟨n, hn⟩ := h.isPGroup_core ⟨b, hbO⟩
  have h1 : b ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : orderOf b ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_eq_prime h.b_pow h.b_ne_one] at h2
  have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

theorem L32Data.B_le_Xb (h : L32Data M B H S K z b f) :
    B ≤ K ⊔ pCoreOf 2 H ⊔ zpowers b := by
  rw [h.B_eq]
  exact sup_le (le_sup_of_le_left (zpowers_le.2 (mem_sup_left h.z_mem_K))) le_sup_right

theorem L32Data.isPGroup_B (h : L32Data M B H S K z b f) : IsPGroup 3 B :=
  IsPGroup.of_card (n := 2) (by rw [h.B_card]; norm_num)

theorem L32Data.not_dvd_index_B (h : L32Data M B H S K z b f) :
    ¬ 3 ∣ (B.subgroupOf (K ⊔ pCoreOf 2 H ⊔ zpowers b)).index := by
  set X := K ⊔ pCoreOf 2 H
  set Y := X ⊔ zpowers b
  have hYN : Y ≤ normalizer (X : Set G) := sup_le le_normalizer (zpowers_le.2 h.b_mem_normalizer_X)
  have hr : X.relIndex (zpowers b) = X.relIndex Y :=
    relIndex_eq_of_sup le_sup_right le_rfl le_sup_left hYN (by rw [sup_comm])
  have hr3 : X.relIndex Y ∣ 3 := by
    have := relIndex_mul_card X (zpowers b)
    rw [Nat.card_zpowers, orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) h.b_pow h.b_ne_one] at this
    exact hr ▸ Dvd.intro _ this
  have hY : Nat.card Y = Nat.card X * X.relIndex Y := by
    have := relIndex_mul_card X Y
    rw [inf_eq_left.2 le_sup_left] at this
    rw [← this, mul_comm]
  have hYB : Nat.card Y = 9 * B.relIndex Y := by
    have := relIndex_mul_card B Y
    rw [inf_eq_left.2 h.B_le_Xb, h.B_card] at this
    rw [← this, mul_comm]
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.1 h.isPGroup_core
  rw [h.card_X, hc] at hY
  have hc3 : ¬ 3 ∣ 2 ^ c := fun hd => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  intro hdvd
  change 3 ∣ B.relIndex Y at hdvd
  obtain ⟨i, hi⟩ := hdvd
  rcases (Nat.dvd_prime Nat.prime_three).1 hr3 with h1 | h1
  ·
    rw [h1, mul_one] at hY
    have : 3 ∣ 2 ^ c * 56 := ⟨3 * i, by linarith⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 this with h2 | h2
    · exact hc3 h2
    · omega
  · rw [h1] at hY
    have : 3 ∣ 2 ^ c * 56 := ⟨i, by linarith⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 this with h2 | h2
    · exact hc3 h2
    · omega

theorem L32Data.card_zpowers (h : L32Data M B H S K z b f) : Nat.card (zpowers z) = 3 := by
  rw [Nat.card_zpowers, h.z_order]

theorem L32Data.isPGroup_zpowers (h : L32Data M B H S K z b f) : IsPGroup 3 (zpowers z) :=
  IsPGroup.of_card (n := 1) (by rw [h.card_zpowers]; norm_num)

theorem L32Data.z_mem_P (h : L32Data M B H S K z b f) :
    z ∈ (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) :=
  ⟨mem_sup_left h.z_mem_K, h.B_le_normalizer_S h.z_mem_B⟩

theorem arith_three {a c i : ℕ} (h7 : a * 7 = 2 ^ c * 168) (h3 : 3 * i = a) : ¬ 3 ∣ i := by
  have hi : i = 2 ^ c * 8 := by
    generalize 2 ^ c = t at h7
    omega
  rw [hi]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with hd | hd
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  · omega

theorem L32Data.not_dvd_index_z (h : L32Data M B H S K z b f) :
    ¬ 3 ∣ ((zpowers z).subgroupOf ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G))).index := by
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.1 h.isPGroup_core
  have hzP : zpowers z ≤ (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) := zpowers_le.2 h.z_mem_P
  have h7 : ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)).relIndex (K ⊔ pCoreOf 2 H) = 7 :=
    h.index_normalizer_eq_seven
  have hP : Nat.card ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) : Subgroup G) * 7 =
      2 ^ c * 168 := by
    have := relIndex_mul_relIndex ⊥ ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G))
      (K ⊔ pCoreOf 2 H) bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left, h7, h.card_X, hc] at this
    exact this
  have hD : 3 * (zpowers z).relIndex ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)) =
      Nat.card ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) : Subgroup G) := by
    have := relIndex_mul_relIndex ⊥ (zpowers z) ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G))
      bot_le hzP
    rwa [relIndex_bot_left, relIndex_bot_left, h.card_zpowers] at this
  exact arith_three hP hD

theorem L32Data.k2813 (hK : KFactLemma2813) (h : L32Data M B H S K z b f)
    {R : Subgroup G} (hSR : S ≤ R) (hRX : R ≤ K ⊔ pCoreOf 2 H) (hR2 : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ (R.subgroupOf (K ⊔ pCoreOf 2 H)).index) :
    Nat.card ↥⁅omegaCenter S, zpowers z⁆ ≤ 16 ∧
      ((K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter R : Subgroup G) : Set G) ≠
          (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) →
        ¬ K ⊔ pCoreOf 2 H ≤ centralizer ((omegaCenter R : Subgroup G) : Set G) →
        ∀ v ∈ omegaCenter S, v * z = z * v → ∀ x ∈ K ⊔ pCoreOf 2 H, v * x = x * v) ∧
      (K ⊔ pCoreOf 2 H ≤ centralizer ((omegaCenter R : Subgroup G) : Set G) →
        ∀ v ∈ omegaCenter S, v * z = z * v → ∀ y ∈ B, ∀ x ∈ K ⊔ pCoreOf 2 H,
          (v * y * v⁻¹ * y⁻¹) * x = x * (v * y * v⁻¹ * y⁻¹)) := by
  have h0 := h.pCoreOf_X
  have h2 : K ⊔ pCoreOf 2 H = K ⊔ pCoreOf 2 (K ⊔ pCoreOf 2 H) := by rw [h0]
  have h3 : ∃ f' : ↥K →* GL32, Function.Surjective f' ∧
      ∀ k : ↥K, f' k = 1 ↔ (k : G) ∈ pCoreOf 2 (K ⊔ pCoreOf 2 H) :=
    ⟨f, h.f_surj, fun k => by rw [h0]; exact h.f_ker k⟩
  have h5 : R ≤ (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) :=
    le_inf hRX (h.le_normalizer_of_sylow hSR hRX hR2 hRi)
  have hV : normalizer ((omegaCenter S : Subgroup G) : Set G) ≤ M :=
    h.char_le _ (omegaCenter_le S) (omegaCenter_ne_bot h.isPGroup_S h.S_ne_bot)
      (omegaCenter_characteristic S)
  have h7 : ∀ Q₀ : Subgroup G,
      Q₀ ≤ pCoreOf 2 ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)) → Q₀ ≠ ⊥ →
      (Q₀.subgroupOf (pCoreOf 2 ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)))).Characteristic →
      ¬ K ⊔ pCoreOf 2 H ≤
        ((K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter
          (pCoreOf 2 ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G))) : Subgroup G) : Set G)) ⊔
        ((K ⊔ pCoreOf 2 H) ⊓ normalizer (Q₀ : Set G)) := by
    intro Q₀ hQS hQ hchar hX
    rw [h.pCoreOf_normalizer_eq] at hQS hchar hX
    have hQM : normalizer (Q₀ : Set G) ≤ M := h.char_le Q₀ hQS hQ hchar
    have hCV : (K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter S : Subgroup G) : Set G) ≤ M :=
      inf_le_right.trans ((centralizer_le_normalizer _).trans hV)
    have hNQ : (K ⊔ pCoreOf 2 H) ⊓ normalizer (Q₀ : Set G) ≤ M := inf_le_right.trans hQM
    exact h.K_not_le fun k hk => sup_le hCV hNQ (hX (mem_sup_left hk))
  have key := hK G (K ⊔ pCoreOf 2 H) K R ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)) b
    h.charTwo_X le_sup_left (h.X_le_H.trans h.K_normal) h.K_perfect h2 h3 hRX hR2 hRi h5
    inf_le_left h.index_normalizer_eq_seven h7 (zpowers z) (zpowers_le.2 h.z_mem_P)
    h.isPGroup_zpowers h.not_dvd_index_z
  rw [h.pCoreOf_normalizer_eq, h0] at key
  obtain ⟨k1, k2, k3⟩ := key
  refine ⟨k1, fun hne hn v hv hvz x hx => k2 hne hn v hv (fun d hd => ?_) x hx, ?_⟩
  · obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hd
    exact ((show Commute v z from hvz).zpow_right n).eq
  · intro hXc v hv hvz y hy x hx
    refine k3 hXc h.b_mem_normalizer_X h.b_pow h.b_cent h.exists_noncomm B h.B_le_Xb
      h.isPGroup_B (zpowers_le.2 h.z_mem_B) h.not_dvd_index_B v hv (fun d hd => ?_) y hy x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hd
    exact ((show Commute v z from hvz).zpow_right n).eq

theorem L32Data.block (hCamp : KFactCampbellBlock) (h : L32Data M B H S K z b f)
    {R : Subgroup G} (hSR : S ≤ R) (hRX : R ≤ K ⊔ pCoreOf 2 H) (hR2 : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ (R.subgroupOf (K ⊔ pCoreOf 2 H)).index)
    (hC : (K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter R : Subgroup G) : Set G) ≤
      normalizer (S : Set G)) :
    ∃ A₀ B₀ : Subgroup G, A₀ ≤ B₀ ∧ B₀ ≤ omegaCenter (K ⊓ pCoreOf 2 H) ∧
      K ⊔ pCoreOf 2 H ≤ normalizer (A₀ : Set G) ∧ K ⊔ pCoreOf 2 H ≤ normalizer (B₀ : Set G) ∧
      K ≤ centralizer (A₀ : Set G) ∧
      (∀ w ∈ K ⊓ pCoreOf 2 H, ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ B₀) ∧
      A₀.relIndex B₀ = 8 ∧
      ∀ g ∈ K ⊔ pCoreOf 2 H, (∀ u ∈ B₀, g * u * g⁻¹ * u⁻¹ ∈ A₀) → g ∈ pCoreOf 2 H := by
  have h0 := h.pCoreOf_X
  have h2 : K ⊔ pCoreOf 2 H = K ⊔ pCoreOf 2 (K ⊔ pCoreOf 2 H) := by rw [h0]
  have h3 : ∃ f' : ↥K →* GL32, Function.Surjective f' ∧
      ∀ k : ↥K, f' k = 1 ↔ (k : G) ∈ pCoreOf 2 (K ⊔ pCoreOf 2 H) :=
    ⟨f, h.f_surj, fun k => by rw [h0]; exact h.f_ker k⟩
  have h5 : R ≤ (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) :=
    le_inf hRX (h.le_normalizer_of_sylow hSR hRX hR2 hRi)
  have h7 : ∀ Q₀ : Subgroup G,
      Q₀ ≤ pCoreOf 2 ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)) → Q₀ ≠ ⊥ →
      (Q₀.subgroupOf (pCoreOf 2 ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)))).Characteristic →
      ¬ K ⊔ pCoreOf 2 H ≤ normalizer (Q₀ : Set G) := by
    intro Q₀ hQS hQ hchar hX
    rw [h.pCoreOf_normalizer_eq] at hQS hchar
    exact h.K_not_le ((le_sup_left.trans hX).trans (h.char_le Q₀ hQS hQ hchar))
  have key := hCamp G (K ⊔ pCoreOf 2 H) K R ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G))
    h.charTwo_X le_sup_left (h.X_le_H.trans h.K_normal) h.K_perfect h2 h3 hRX hR2 hRi h5
    inf_le_left h.index_normalizer_eq_seven (le_inf inf_le_left hC) h7
  rwa [h0] at key

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I
