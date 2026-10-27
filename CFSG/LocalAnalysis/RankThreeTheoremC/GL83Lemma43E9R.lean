module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9Core
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.GL83PartI.I_28_3_S3
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3Rest
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Comm
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Eigen
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Lift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43W
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin
  CFSG.Quasithin.F53Push CFSG.ABGLocalTools Subgroup
open scoped Pointwise

section D8

variable {H : Type*} [Group H]

theorem e9r_zpow_eq_of_mul_eq {ℓ u : H} (hlu : zpowers ℓ ⊓ zpowers u = ⊥) {i j i' j' : ℤ}
    (h : ℓ ^ i * u ^ j = ℓ ^ i' * u ^ j') : ℓ ^ i = ℓ ^ i' := by
  have hx : (ℓ ^ i')⁻¹ * ℓ ^ i = u ^ j' * (u ^ j)⁻¹ := by
    calc (ℓ ^ i')⁻¹ * ℓ ^ i = (ℓ ^ i')⁻¹ * (ℓ ^ i * u ^ j) * (u ^ j)⁻¹ := by group
      _ = (ℓ ^ i')⁻¹ * (ℓ ^ i' * u ^ j') * (u ^ j)⁻¹ := by rw [h]
      _ = u ^ j' * (u ^ j)⁻¹ := by group
  have hmem : (ℓ ^ i')⁻¹ * ℓ ^ i ∈ zpowers ℓ ⊓ zpowers u := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (zpow_mem_zpowers ℓ i')) (zpow_mem_zpowers ℓ i),
      ?_⟩
    rw [hx]
    exact mul_mem (zpow_mem_zpowers u j') (inv_mem (zpow_mem_zpowers u j))
  rw [hlu] at hmem
  have h1 : (ℓ ^ i')⁻¹ * ℓ ^ i = 1 := mem_bot.mp hmem
  calc ℓ ^ i = ℓ ^ i' * ((ℓ ^ i')⁻¹ * ℓ ^ i) := by group
    _ = ℓ ^ i' := by rw [h1, mul_one]

theorem e9r_zpow_eq_one_of_dvd {ℓ : H} (hℓ3 : ℓ ^ 3 = 1) {n : ℤ} (h : (3 : ℤ) ∣ n) :
    ℓ ^ n = 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hℓ3, one_zpow]

theorem e9r_dvd_of_zpow_eq_one {ℓ : H} (hℓ3 : ℓ ^ 3 = 1) (hℓ1 : ℓ ≠ 1) {n : ℤ}
    (h : ℓ ^ n = 1) : (3 : ℤ) ∣ n := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hℓo : orderOf ℓ = 3 := orderOf_eq_prime hℓ3 hℓ1
  have := orderOf_dvd_iff_zpow_eq_one.mpr h
  rwa [hℓo] at this

theorem e9r_conj_mul_zpow {ℓ u r : H} (hℓu : ℓ * u = u * ℓ) {a b c d : ℤ}
    (hrℓ : r * ℓ * r⁻¹ = ℓ ^ a * u ^ b) (hru : r * u * r⁻¹ = ℓ ^ c * u ^ d) (i j : ℤ) :
    r * (ℓ ^ i * u ^ j) * r⁻¹ = ℓ ^ (a * i + c * j) * u ^ (b * i + d * j) := by
  have hcomm : Commute ℓ u := hℓu
  have e1 : r * (ℓ ^ i * u ^ j) * r⁻¹ = (r * ℓ * r⁻¹) ^ i * (r * u * r⁻¹) ^ j := by
    rw [conj_zpow, conj_zpow]; group
  rw [e1, hrℓ, hru]
  have c1 : Commute (ℓ ^ a) (u ^ b) := hcomm.zpow_zpow a b
  have c2 : Commute (ℓ ^ c) (u ^ d) := hcomm.zpow_zpow c d
  rw [c1.mul_zpow, c2.mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  have c3 : Commute (u ^ (b * i)) (ℓ ^ (c * j)) := (hcomm.zpow_zpow (c * j) (b * i)).symm
  calc ℓ ^ (a * i) * u ^ (b * i) * (ℓ ^ (c * j) * u ^ (d * j))
      = ℓ ^ (a * i) * (u ^ (b * i) * ℓ ^ (c * j)) * u ^ (d * j) := by group
    _ = ℓ ^ (a * i) * (ℓ ^ (c * j) * u ^ (b * i)) * u ^ (d * j) := by rw [c3.eq]
    _ = ℓ ^ (a * i + c * j) * u ^ (b * i + d * j) := by
      rw [zpow_add, zpow_add]; group

theorem e9r_exists_conj_mem_zpowers {ℓ u r t : H} (hℓ3 : ℓ ^ 3 = 1)
    (hℓu : ℓ * u = u * ℓ) (hlu : zpowers ℓ ⊓ zpowers u = ⊥) {a b c d : ℤ}
    (hrℓ : r * ℓ * r⁻¹ = ℓ ^ a * u ^ b) (hru : r * u * r⁻¹ = ℓ ^ c * u ^ d)
    (hr2 : r * (r * ℓ * r⁻¹) * r⁻¹ = ℓ⁻¹) (htℓ : t * ℓ * t⁻¹ = ℓ) (htu : t * u * t⁻¹ = u⁻¹) :
    r * ℓ * r⁻¹ ∈ zpowers u ∨ (r * t * r * t⁻¹) * ℓ * (r * t * r * t⁻¹)⁻¹ ∈ zpowers u := by
  by_cases hℓ1 : ℓ = 1
  · left
    rw [hℓ1]
    simp
  have hr2' : ℓ ^ (a * a + c * b) * u ^ (b * a + d * b) = ℓ ^ (-1 : ℤ) * u ^ (0 : ℤ) := by
    rw [← e9r_conj_mul_zpow hℓu hrℓ hru a b, ← hrℓ, hr2, zpow_neg_one, zpow_zero, mul_one]
  have hdiv : (3 : ℤ) ∣ a * a + c * b + 1 := by
    have h1 := e9r_zpow_eq_of_mul_eq hlu hr2'
    have h2 : ℓ ^ (a * a + c * b - (-1)) = 1 := by rw [zpow_sub, h1, mul_inv_cancel]
    have := e9r_dvd_of_zpow_eq_one hℓ3 hℓ1 h2
    simpa using this
  by_cases ha : (3 : ℤ) ∣ a
  · left
    rw [hrℓ, e9r_zpow_eq_one_of_dvd hℓ3 ha, one_mul]
    exact zpow_mem_zpowers u b
  · right
    have ha2 : (3 : ℤ) ∣ a * a - 1 := by
      have : a % 3 = 1 ∨ a % 3 = 2 := by omega
      rcases this with h | h
      · have : a = 3 * (a / 3) + 1 := by omega
        rw [this]; exact ⟨3 * (a / 3) * (a / 3) + 2 * (a / 3), by ring⟩
      · have : a = 3 * (a / 3) + 2 := by omega
        rw [this]; exact ⟨3 * (a / 3) * (a / 3) + 4 * (a / 3) + 1, by ring⟩
    have hdiv2 : (3 : ℤ) ∣ a * a - c * b := by
      have e : a * a - c * b = 2 * (a * a - 1) - (a * a + c * b + 1) + 3 := by ring
      rw [e]
      exact dvd_add (dvd_sub (dvd_mul_of_dvd_right ha2 2) hdiv) (dvd_refl 3)
    have htℓ' : t⁻¹ * ℓ * t = ℓ := by
      calc t⁻¹ * ℓ * t = t⁻¹ * (t * ℓ * t⁻¹) * t := by rw [htℓ]
        _ = ℓ := by group
    have ht1 : t * (ℓ ^ a * u ^ b) * t⁻¹ = ℓ ^ a * u ^ (-b) := by
      have e : t * (ℓ ^ a * u ^ b) * t⁻¹ = (t * ℓ * t⁻¹) ^ a * (t * u * t⁻¹) ^ b := by
        rw [conj_zpow, conj_zpow]; group
      rw [e, htℓ, htu, inv_zpow']
    have e : (r * t * r * t⁻¹) * ℓ * (r * t * r * t⁻¹)⁻¹ =
        r * (t * (r * (t⁻¹ * ℓ * t) * r⁻¹) * t⁻¹) * r⁻¹ := by group
    rw [e, htℓ', hrℓ, ht1, e9r_conj_mul_zpow hℓu hrℓ hru a (-b),
      show a * a + c * -b = a * a - c * b by ring, e9r_zpow_eq_one_of_dvd hℓ3 hdiv2, one_mul]
    exact zpow_mem_zpowers u _

end D8

variable {G : Type} [Group G] [Finite G]

structure E9Case1DataR (G : Type) [Group G] [Finite G] (M O K₀ : Subgroup G) (x : G) :
    Prop where
  O_le : O ≤ M
  O_norm : M ≤ normalizer (O : Set G)
  O_cop : ¬ 3 ∣ Nat.card O
  O₂_le : pCoreOf 2 M ≤ O
  O₂_ne : pCoreOf 2 M ≠ ⊥
  charTwo : CharTwo M
  K₀_le : K₀ ≤ M
  K₀_el : IsElemAbelian 3 K₀
  K₀_card : Nat.card K₀ = 9
  x_mem : x ∈ M
  E_el : IsElemAbelian 3 (zpowers x ⊔ K₀)
  E_card : Nat.card (zpowers x ⊔ K₀ : Subgroup G) = 27
  B_norm : M ≤ normalizer ((K₀ ⊔ O : Subgroup G) : Set G)
  rot : ∃ ρ ∈ M, ρ ∈ normalizer (K₀ : Set G) ∧ ∀ k ∈ K₀, ρ * (ρ * k * ρ⁻¹) * ρ⁻¹ = k⁻¹
  D1 : ∀ Y₀ : Subgroup G, Y₀ ≠ ⊥ → IsPGroup 2 Y₀ →
    3 ≤ CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M) → normalizer (Y₀ : Set G) ≤ M

theorem e9r_exists_conj_zpowers_eq {U O : Subgroup G} (hUO : U ≤ normalizer (O : Set G))
    (hO3 : ¬ 3 ∣ Nat.card O) (hU3 : Nat.card U = 3) {w : G} (hw : w ∈ U ⊔ O)
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) : ∃ k ∈ U ⊔ O, zpowers (k⁻¹ * w * k) = U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUp : IsPGroup 3 U := IsPGroup.of_card (n := 1) (by rw [hU3]; norm_num)
  have hU3' : ∀ v ∈ U, v ^ 3 = 1 := fun v hv => by
    have h := orderOf_dvd_natCard (⟨v, hv⟩ : U)
    rw [hU3, Subgroup.orderOf_mk] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hUsyl : IsSylowOf 3 U (U ⊔ O) := by
    refine isSylowOf_iff.mpr ⟨le_sup_left, hUp, ?_⟩
    have hc := e9_card_sup_mul_card_inf hUO
    rw [e9_inf_eq_bot hU3' hO3, Subgroup.card_bot, hU3, mul_one] at hc
    have hrel := Subgroup.relIndex_mul_card (H := U) (K := U ⊔ O)
    rw [inf_of_le_left le_sup_left, hU3, hc] at hrel
    have : U.relIndex (U ⊔ O) = Nat.card O := by omega
    rw [this]
    exact hO3
  have hwo : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hzp : IsPGroup 3 ((zpowers w).subgroupOf (U ⊔ O)) := by
    have : IsPGroup 3 (zpowers w) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hwo]; simp)
    exact this.comap_subtype
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hQs : IsSylowOf 3 (Q.map (U ⊔ O).subtype) (U ⊔ O) := ⟨Q, rfl⟩
  obtain ⟨k, hkB, hkk⟩ := hUsyl.exists_mem_conj hQs
  have hkw : k⁻¹ * w * k ∈ U :=
    (hkk w).mp ⟨⟨w, hw⟩, hQ (Subgroup.mem_subgroupOf.mpr (mem_zpowers _)), rfl⟩
  refine ⟨k, hkB, Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hkw) ?_⟩
  rw [hU3, Nat.card_zpowers]
  have h3 : (k⁻¹ * w * k) ^ 3 = 1 := by
    rw [show k⁻¹ * w * k = k⁻¹ * w * k⁻¹⁻¹ by rw [inv_inv], conj_pow, hw3, mul_one,
      mul_inv_cancel]
  have h1 : k⁻¹ * w * k ≠ 1 := by
    intro h1
    apply hw1
    calc w = k * (k⁻¹ * w * k) * k⁻¹ := by group
      _ = 1 := by rw [h1]; group
  rw [orderOf_eq_prime h3 h1]

theorem E9Case1DataR.card_eq_four_of_small {M O K₀ : Subgroup G} {x : G}
    (h : E9Case1DataR G M O K₀ x)
    {ℓ : G} (hℓ : ℓ ∈ K₀) (hℓ1 : ℓ ≠ 1) {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M)
    (hYO : IsSylowOf 2 (Y ⊓ O) O) (hxY : x ∈ normalizer (Y : Set G))
    (hℓY : ℓ ∈ normalizer (Y : Set G))
    (hsmall : ∀ Y₀ : Subgroup G, Y₀ ≤ Y → Y₀ ≠ ⊥ → (Y₀.subgroupOf Y).Characteristic →
      CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M) < 3) :
    Nat.card (⁅omegaOneCenterOf (pCoreOf 2 M), zpowers ℓ⁆ : Subgroup G) = 4 := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK₀O : K₀ ≤ normalizer (O : Set G) := h.K₀_le.trans h.O_norm
  have hK3 : ∀ k ∈ K₀, k ^ 3 = 1 := h.K₀_el.2
  have hYO' : Y ≤ normalizer (O : Set G) := hYM.trans h.O_norm
  have hYB : Y ≤ normalizer ((K₀ ⊔ O : Subgroup G) : Set G) := hYM.trans h.B_norm
  have hBO : (K₀ ⊔ O : Subgroup G) ≤ normalizer (O : Set G) :=
    sup_le hK₀O Subgroup.le_normalizer
  have hBM : (K₀ ⊔ O : Subgroup G) ≤ M := sup_le h.K₀_le h.O_le
  have hYB_O : Y ⊓ (K₀ ⊔ O) ≤ O := e9_inf_sup_le hK₀O hK3 hY2
  have hSY : Y ⊓ O ≤ Y := inf_le_left
  have hrank : ∀ Y₀ : Subgroup G, Y₀ ≤ Y → Y₀ ≠ ⊥ → (Y₀.subgroupOf Y).Characteristic →
      ¬ zpowers x ⊔ K₀ ≤ (normalizer (Y₀ : Set G) ⊓ M) ⊔ O := by
    intro Y₀ hle hne hch hEle
    have h3 := l43_three_le_pRank_of_le_sup (H := normalizer (Y₀ : Set G) ⊓ M) (O := O)
      (E := zpowers x ⊔ K₀) (inf_le_right.trans h.O_norm) h.O_cop h.E_el h.E_card hEle
    exact absurd h3 (not_le.mpr (hsmall Y₀ hle hne hch))
  have hO₂Y : pCoreOf 2 M ≤ Y ⊓ O :=
    e9_le_of_normal h.O₂_le
      (h.O_le.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M) hYO
  have hYne : Y ≠ ⊥ := by
    intro hY
    apply h.O₂_ne
    rw [eq_bot_iff]
    intro g hg
    have := (hO₂Y hg).1
    rw [hY] at this
    exact this
  have hYchar : (Y.subgroupOf Y).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  by_cases hact : ∃ y ∈ Y, ∃ k ∈ K₀, y * k * y⁻¹ * k⁻¹ ∉ O
  swap
  ·
    exfalso
    push Not at hact
    obtain ⟨T, hST, hTB, hYT, hTO, hTsup⟩ := l43_exists_lift (O := O) (B := K₀ ⊔ O) (Y := Y)
      le_sup_right hBO hYB hYO' hY2 h.O_cop
      (fun b hb => e9_pow_three_mem_sup hK₀O hK3 hb) hYO
    have hcomm := e9_comm_mem_sup hK₀O hYO' hact
    have hTY : ∀ t ∈ T, ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := by
      intro t ht y hy
      have h1 : y * t * y⁻¹ * t⁻¹ ∈ O := hcomm y hy t (hTB ht)
      have h2 : t * y * t⁻¹ * y⁻¹ ∈ O := by
        have := O.inv_mem h1
        have e : (y * t * y⁻¹ * t⁻¹)⁻¹ = t * y * t⁻¹ * y⁻¹ := by group
        rwa [e] at this
      have h3 : t * y * t⁻¹ * y⁻¹ ∈ T := by
        have e : t * y * t⁻¹ * y⁻¹ = t * (y * t⁻¹ * y⁻¹) := by group
        rw [e]
        exact T.mul_mem ht ((mem_normalizer_iff.mp (hYT hy) t⁻¹).mp (T.inv_mem ht))
      have h4 : t * y * t⁻¹ * y⁻¹ ∈ Y ⊓ O := hTO ▸ ⟨h3, h2⟩
      have e : t * y * t⁻¹ = (t * y * t⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact Y.mul_mem h4.1 hy
    have hTN : T ≤ normalizer (Y : Set G) := by
      intro t ht
      rw [mem_normalizer_iff]
      intro y
      refine ⟨fun hy => hTY t ht y hy, fun hy => ?_⟩
      have := hTY t⁻¹ (T.inv_mem ht) _ hy
      have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
      rwa [e] at this
    refine hrank Y le_rfl hYne hYchar (sup_le ?_ ?_)
    · exact (zpowers_le.mpr (mem_inf.mpr ⟨hxY, h.x_mem⟩)).trans le_sup_left
    · calc K₀ ≤ K₀ ⊔ O := le_sup_left
        _ = T ⊔ O := hTsup.symm
        _ ≤ (normalizer (Y : Set G) ⊓ M) ⊔ O :=
          sup_le_sup_right (le_inf hTN (hTB.trans hBM)) O
  · obtain ⟨y₀, hy₀, k₀, hk₀, hnt⟩ := hact
    have hYℓ : ∀ y ∈ Y, y * ℓ * y⁻¹ * ℓ⁻¹ ∈ O := by
      intro y hy
      have h1 : y * ℓ * y⁻¹ * ℓ⁻¹ ∈ Y := by
        have e : y * ℓ * y⁻¹ * ℓ⁻¹ = y * (ℓ * y⁻¹ * ℓ⁻¹) := by group
        rw [e]
        exact Y.mul_mem hy ((mem_normalizer_iff.mp hℓY y⁻¹).mp (Y.inv_mem hy))
      have h2 : y * ℓ * y⁻¹ * ℓ⁻¹ ∈ K₀ ⊔ O := by
        have hℓB : ℓ ∈ K₀ ⊔ O := mem_sup_left hℓ
        have hyℓ : y * ℓ * y⁻¹ ∈ K₀ ⊔ O := (mem_normalizer_iff.mp (hYB hy) ℓ).mp hℓB
        exact Subgroup.mul_mem _ hyℓ (Subgroup.inv_mem _ hℓB)
      exact hYB_O ⟨h1, h2⟩
    obtain ⟨U₂, hU₂K, hU₂card, hU₂ℓ, hYU₂, y₁, hy₁, b₁, hb₁, hnt'⟩ :=
      l43_exists_eigenline hK₀O hYO' h.O_cop hY2 h.K₀_el h.K₀_card hYB hℓ hℓ1 hYℓ
        ⟨y₀, hy₀, k₀, hk₀, hnt⟩
    have hU₂3 : ∀ k ∈ U₂, k ^ 3 = 1 := fun k hk => hK3 k (hU₂K hk)
    have hU₂O : U₂ ≤ normalizer (O : Set G) := hU₂K.trans hK₀O
    have hB₂O : (U₂ ⊔ O : Subgroup G) ≤ normalizer (O : Set G) :=
      sup_le hU₂O Subgroup.le_normalizer
    have hB₂M : (U₂ ⊔ O : Subgroup G) ≤ M := sup_le (hU₂K.trans h.K₀_le) h.O_le
    obtain ⟨T₂, hST₂, hT₂B, hYT₂, hT₂O, hT₂sup⟩ := l43_exists_lift (O := O) (B := U₂ ⊔ O)
      (Y := Y) le_sup_right hB₂O hYU₂ hYO' hY2 h.O_cop
      (fun b hb => e9_pow_three_mem_sup hU₂O hU₂3 hb) hYO
    have hT₂M : T₂ ≤ M := hT₂B.trans hB₂M
    have hT₂N : T₂ ≤ normalizer (O : Set G) := hT₂B.trans hB₂O
    have hT₂S : T₂ ≤ normalizer ((Y ⊓ O : Subgroup G) : Set G) := by
      have := e9_le_normalizer_inf (A := T₂) (C := O) Subgroup.le_normalizer hT₂N
      rwa [hT₂O] at this
    have hYS : Y ≤ normalizer ((Y ⊓ O : Subgroup G) : Set G) :=
      e9_le_normalizer_inf Subgroup.le_normalizer hYO'
    have hU₂O' : U₂ ⊓ O = ⊥ := e9_inf_eq_bot hU₂3 h.O_cop
    have hcard1 := e9_card_sup_mul_card_inf hU₂O
    rw [hU₂O', Subgroup.card_bot, hU₂card, mul_one] at hcard1
    have hcard2 := e9_card_sup_mul_card_inf hT₂N
    rw [hT₂sup, hT₂O, hcard1] at hcard2
    have hOpos : 0 < Nat.card O := Nat.card_pos
    have hT₃ : Nat.card T₂ = 3 * Nat.card (Y ⊓ O : Subgroup G) := by
      apply Nat.eq_of_mul_eq_mul_right hOpos
      rw [← hcard2]
      ring
    have hnt₂ : ∃ y ∈ Y, ∃ t ∈ T₂, y * t * y⁻¹ * t⁻¹ ∉ Y ⊓ O := by
      have hb₁' : b₁ ∈ (T₂ : Set G) * (O : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right T₂ O hT₂N]
        rw [hT₂sup]
        exact hb₁
      obtain ⟨t, ht, o, ho, hto⟩ := hb₁'
      have hb₁eq : b₁ = t * o := hto.symm
      refine ⟨y₁, hy₁, t, ht, fun hmem => hnt' ?_⟩
      have hc : y₁ * t * y₁⁻¹ * t⁻¹ ∈ O := hmem.2
      have e : y₁ * b₁ * y₁⁻¹ * b₁⁻¹ =
          (y₁ * t * y₁⁻¹ * t⁻¹) * (t * (y₁ * o * y₁⁻¹ * o⁻¹) * t⁻¹) := by
        rw [hb₁eq]
        group
      rw [e]
      have hyo : y₁ * o * y₁⁻¹ * o⁻¹ ∈ O :=
        O.mul_mem ((mem_normalizer_iff.mp (hYO' hy₁) o).mp ho) (O.inv_mem ho)
      exact O.mul_mem hc ((mem_normalizer_iff.mp (hT₂N ht) _).mp hyo)
    obtain ⟨hWsyl, hWcard, hWq⟩ := l43_wStructure hY2 inf_le_left hST₂ hT₂S hYS hYT₂ hT₃ hnt₂
    have hWM : T₂ ⊔ Y ≤ M := sup_le hT₂M hYM
    have hO₂W : pCoreOf 2 M ≤ T₂ ⊔ Y := hO₂Y.trans (inf_le_left.trans le_sup_right)
    have hF : CharTwo (T₂ ⊔ Y) := charTwo_of_core_le h.charTwo hO₂W hWM
    have hO₂ : pCoreOf 2 M ≤ pCoreOf 2 (T₂ ⊔ Y) :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (pCoreOf 2 M) (T₂ ⊔ Y) hO₂W
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hO₂W).mpr
          (hWM.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)))
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    have hK₀eq : zpowers ℓ ⊔ U₂ = K₀ := by
      have hℓ3 : ℓ ^ 3 = 1 := hK3 ℓ hℓ
      have hℓo : orderOf ℓ = 3 := orderOf_eq_prime hℓ3 hℓ1
      have hcomm : K₀ ≤ centralizer (K₀ : Set G) :=
        Subgroup.le_centralizer_iff_isMulCommutative.mpr h.K₀_el.1
      have hzU : zpowers ℓ ≤ normalizer (U₂ : Set G) := by
        refine (zpowers_le.mpr hℓ).trans (hcomm.trans ((Subgroup.centralizer_le hU₂K).trans ?_))
        exact Subgroup.centralizer_le_normalizer (U₂ : Set G)
      have hc := e9_card_sup_mul_card_inf hzU
      rw [hU₂ℓ, Subgroup.card_bot, Nat.card_zpowers, hℓo, hU₂card, mul_one] at hc
      exact Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr hℓ) hU₂K)
        (by rw [hc, h.K₀_card])
    have hnc : NoCharNormal Y (T₂ ⊔ Y) := by
      intro C hCY hC1 hCch hWC
      refine hrank C hCY hC1 hCch (sup_le ?_ ?_)
      · exact (zpowers_le.mpr (mem_inf.mpr ⟨l43_normalizer_le_of_characteristic hCY hCch hxY,
          h.x_mem⟩)).trans le_sup_left
      · have hℓH : zpowers ℓ ≤ normalizer (C : Set G) ⊓ M :=
          zpowers_le.mpr (mem_inf.mpr ⟨l43_normalizer_le_of_characteristic hCY hCch hℓY,
            h.K₀_le hℓ⟩)
        have hT₂H : T₂ ≤ normalizer (C : Set G) ⊓ M := le_inf (le_sup_left.trans hWC) hT₂M
        have hU₂H : U₂ ≤ (normalizer (C : Set G) ⊓ M) ⊔ O := by
          calc U₂ ≤ T₂ ⊔ O := by rw [hT₂sup]; exact le_sup_left
            _ ≤ _ := sup_le_sup_right hT₂H O
        calc K₀ = zpowers ℓ ⊔ U₂ := hK₀eq.symm
          _ ≤ _ := sup_le (hℓH.trans le_sup_left) hU₂H
    have h3T₂ : 3 ∣ Nat.card T₂ := ⟨Nat.card (Y ⊓ O : Subgroup G), hT₃⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3T₂
    have huG : orderOf (u : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hu
    have hu3 : (u : G) ^ 3 = 1 := by rw [← huG]; exact pow_orderOf_eq_one _
    have hu1 : (u : G) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at huG
      omega
    have huW : (u : G) ∈ T₂ ⊔ Y := mem_sup_left u.2
    have h4 := GL83.baumann_niles_s3 hWsyl hF hWq hnc huW hu3 hu1
    have hX := l43_card_commutator_omegaOneCenter hWM huW hu3 hu1 h.charTwo hO₂ h4
    have hO'n : (O.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer h.O_le).mpr h.O_norm
    set π : M →* M ⧸ O.subgroupOf M := QuotientGroup.mk' (O.subgroupOf M) with hπ
    have hπ1 : ∀ m : M, π m = 1 ↔ (m : G) ∈ O := fun m => by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    have hπc : ∀ a b : M, π (a * b * a⁻¹) = π a * π b * (π a)⁻¹ := fun a b => by
      rw [map_mul, map_mul, map_inv]
    obtain ⟨u₀, hu₀⟩ : ∃ u₀ : G, zpowers u₀ = U₂ := by
      have hc : IsCyclic U₂ := isCyclic_of_prime_card (p := 3) hU₂card
      obtain ⟨g, hg⟩ := hc.exists_generator
      refine ⟨(g : G), le_antisymm (zpowers_le.mpr g.2) fun z hz => ?_⟩
      obtain ⟨k, hk⟩ := hg ⟨z, hz⟩
      refine mem_zpowers_iff.mpr ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    have hu₀U : u₀ ∈ U₂ := hu₀ ▸ mem_zpowers u₀
    have hu₀K : u₀ ∈ K₀ := hU₂K hu₀U
    have hu₀3 : u₀ ^ 3 = 1 := hK3 u₀ hu₀K
    have hu₀1 : u₀ ≠ 1 := by
      intro h1
      have : U₂ = ⊥ := by rw [← hu₀, h1, zpowers_one_eq_bot]
      rw [this, Subgroup.card_bot] at hU₂card
      omega
    have hℓM : ℓ ∈ M := h.K₀_le hℓ
    have hu₀M : u₀ ∈ M := h.K₀_le hu₀K
    obtain ⟨ρ, hρM, hρN, hρ2⟩ := h.rot
    have hy₁M : y₁ ∈ M := hYM hy₁
    set ℓb : M ⧸ O.subgroupOf M := π ⟨ℓ, hℓM⟩ with hℓb
    set ub : M ⧸ O.subgroupOf M := π ⟨u₀, hu₀M⟩ with hub
    set rb : M ⧸ O.subgroupOf M := π ⟨ρ, hρM⟩ with hrb
    set tb : M ⧸ O.subgroupOf M := π ⟨y₁, hy₁M⟩ with htb
    have hπinj : ∀ a ∈ K₀, ∀ b ∈ K₀, ∀ (ha : a ∈ M) (hb : b ∈ M), π ⟨a, ha⟩ = π ⟨b, hb⟩ →
        a = b := by
      intro a ha b hb ha' hb' hab
      have h1 : (⟨a, ha'⟩ : M)⁻¹ * ⟨b, hb'⟩ ∈ O.subgroupOf M := QuotientGroup.eq.mp hab
      have h2 : a⁻¹ * b ∈ K₀ ⊓ O := ⟨K₀.mul_mem (K₀.inv_mem ha) hb, mem_subgroupOf.mp h1⟩
      rw [e9_inf_eq_bot hK3 h.O_cop, mem_bot, inv_mul_eq_one] at h2
      exact h2
    have hπK₀ : ∀ k ∈ K₀, ∀ hk : k ∈ M, ∀ i : ℤ, π ⟨k, hk⟩ ^ i = π ⟨k ^ i, M.zpow_mem hk i⟩ :=
      fun k _ hk i => by rw [← map_zpow]; rfl
    have hℓb3 : ℓb ^ 3 = 1 := by
      rw [hℓb, ← map_pow]
      exact (hπ1 _).mpr (by rw [SubgroupClass.coe_pow, hK3 ℓ hℓ]; exact O.one_mem)
    have hub3 : ub ^ 3 = 1 := by
      rw [hub, ← map_pow]
      exact (hπ1 _).mpr (by rw [SubgroupClass.coe_pow, hu₀3]; exact O.one_mem)
    have hℓu : ℓb * ub = ub * ℓb := by
      rw [hℓb, hub, ← map_mul, ← map_mul]
      congr 1
      have := h.K₀_el.1
      exact Subtype.ext (setLike_mul_comm hℓ hu₀K)
    have hlu : zpowers ℓb ⊓ zpowers ub = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (Subgroup.mem_inf.mp hz).1
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (Subgroup.mem_inf.mp hz).2
      rw [hℓb, hπK₀ ℓ hℓ hℓM i] at hj ⊢
      rw [hub, hπK₀ u₀ hu₀K hu₀M j] at hj
      have heq := hπinj _ (K₀.zpow_mem hu₀K j) _ (K₀.zpow_mem hℓ i) _ _ hj
      have hmem : ℓ ^ i ∈ zpowers ℓ ⊓ U₂ :=
        ⟨zpow_mem_zpowers ℓ i, heq ▸ (hu₀ ▸ zpow_mem_zpowers u₀ j)⟩
      rw [hU₂ℓ, mem_bot] at hmem
      rw [mem_bot]
      have : (⟨ℓ ^ i, M.zpow_mem hℓM i⟩ : M) = 1 := Subtype.ext hmem
      rw [this, map_one]
    have hK₀eq' : zpowers ℓ ⊔ zpowers u₀ = K₀ := by rw [hu₀]; exact hK₀eq
    have hcommℓu : ∀ s ∈ zpowers ℓ, ∀ c ∈ zpowers u₀, s * c = c * s := fun s hs c hc => by
      have := h.K₀_el.1
      exact setLike_mul_comm (zpowers_le.mpr hℓ hs) (zpowers_le.mpr hu₀K hc)
    have hdec : ∀ k ∈ K₀, ∃ i j : ℤ, k = ℓ ^ i * u₀ ^ j := by
      intro k hk
      rw [← hK₀eq'] at hk
      obtain ⟨s, hs, c, hc, rfl⟩ := u3l42_decomp hcommℓu hk
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hs
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
      exact ⟨i, j, rfl⟩
    have hπdec : ∀ (k : G) (hk : k ∈ M) (i j : ℤ), k = ℓ ^ i * u₀ ^ j →
        π ⟨k, hk⟩ = ℓb ^ i * ub ^ j := by
      intro k hk i j hkij
      rw [hℓb, hub, hπK₀ ℓ hℓ hℓM i, hπK₀ u₀ hu₀K hu₀M j, ← map_mul]
      congr 1
      exact Subtype.ext hkij
    have hρℓK : ρ * ℓ * ρ⁻¹ ∈ K₀ := (mem_normalizer_iff.mp hρN ℓ).mp hℓ
    have hρuK : ρ * u₀ * ρ⁻¹ ∈ K₀ := (mem_normalizer_iff.mp hρN u₀).mp hu₀K
    obtain ⟨a, b, hab⟩ := hdec _ hρℓK
    obtain ⟨c, d, hcd⟩ := hdec _ hρuK
    have hrℓ : rb * ℓb * rb⁻¹ = ℓb ^ a * ub ^ b := by
      rw [hrb, hℓb, ← hπc]
      exact hπdec _ _ a b hab
    have hru : rb * ub * rb⁻¹ = ℓb ^ c * ub ^ d := by
      rw [hrb, hub, ← hπc]
      exact hπdec _ _ c d hcd
    have hr2 : rb * (rb * ℓb * rb⁻¹) * rb⁻¹ = ℓb⁻¹ := by
      rw [hrb, hℓb, ← hπc, ← hπc, ← map_inv]
      congr 1
      exact Subtype.ext (by simpa using hρ2 ℓ hℓ)
    have htℓ : tb * ℓb * tb⁻¹ = ℓb := by
      have h1 : π (⟨y₁, hy₁M⟩ * ⟨ℓ, hℓM⟩ * ⟨y₁, hy₁M⟩⁻¹ * ⟨ℓ, hℓM⟩⁻¹) = 1 :=
        (hπ1 _).mpr (hYℓ y₁ hy₁)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      rw [htb, hℓb]
      calc π ⟨y₁, hy₁M⟩ * π ⟨ℓ, hℓM⟩ * (π ⟨y₁, hy₁M⟩)⁻¹
          = π ⟨y₁, hy₁M⟩ * π ⟨ℓ, hℓM⟩ * (π ⟨y₁, hy₁M⟩)⁻¹ * (π ⟨ℓ, hℓM⟩)⁻¹ * π ⟨ℓ, hℓM⟩ := by
            group
        _ = π ⟨ℓ, hℓM⟩ := by rw [h1, one_mul]
    have hU₂O : U₂ ≤ normalizer (O : Set G) := hU₂K.trans hK₀O
    have hπU₂ : ∀ (w : G) (hw : w ∈ M), w ∈ U₂ ⊔ O → π ⟨w, hw⟩ ∈ zpowers ub := by
      intro w hw hwU
      have hset := Subgroup.coe_mul_of_left_le_normalizer_right U₂ O hU₂O
      have hw' : w ∈ (U₂ : Set G) * (O : Set G) := by rw [← hset]; exact hwU
      obtain ⟨v, hv, o, ho, rfl⟩ := hw'
      rw [← hu₀] at hv
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
      have hoM : o ∈ M := h.O_le ho
      have e : (⟨u₀ ^ j * o, hw⟩ : M) = ⟨u₀ ^ j, M.zpow_mem hu₀M j⟩ * ⟨o, hoM⟩ := rfl
      rw [e, map_mul, (hπ1 ⟨o, hoM⟩).mpr ho, mul_one, ← hπK₀ u₀ hu₀K hu₀M j]
      exact zpow_mem_zpowers _ j
    have htu : tb * ub * tb⁻¹ = ub⁻¹ := by
      have hyu : y₁ * u₀ * y₁⁻¹ ∈ U₂ ⊔ O := (mem_normalizer_iff.mp (hYU₂ hy₁) u₀).mp
        (mem_sup_left hu₀U)
      have hmem := hπU₂ _ (M.mul_mem (M.mul_mem hy₁M hu₀M) (M.inv_mem hy₁M)) hyu
      have hconj : π ⟨y₁ * u₀ * y₁⁻¹, M.mul_mem (M.mul_mem hy₁M hu₀M) (M.inv_mem hy₁M)⟩ =
          tb * ub * tb⁻¹ := by
        rw [htb, hub, ← hπc]
        rfl
      rw [hconj] at hmem
      obtain ⟨e, he⟩ := mem_zpowers_iff.mp hmem
      have hub3' : ub ^ (3 : ℤ) = 1 := by
        rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hub3]
      have he3 : ub ^ e = ub ^ (e % 3) := zpow_eq_zpow_emod e hub3'
      have hcases : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · exfalso
        rw [he3, h0, zpow_zero] at he
        have h1 : tb * ub * tb⁻¹ = 1 := he.symm
        have h2 : ub = 1 := by
          calc ub = tb⁻¹ * (tb * ub * tb⁻¹) * tb := by group
            _ = 1 := by rw [h1]; group
        have h3 : (u₀ : G) ∈ O := (hπ1 ⟨u₀, hu₀M⟩).mp h2
        have h4 : u₀ ∈ K₀ ⊓ O := ⟨hu₀K, h3⟩
        rw [e9_inf_eq_bot hK3 h.O_cop, mem_bot] at h4
        exact hu₀1 h4
      · exfalso
        rw [he3, h1, zpow_one] at he
        apply hnt'
        have hb₁M : b₁ ∈ M := hB₂M hb₁
        have hb₁π := hπU₂ b₁ hb₁M hb₁
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hb₁π
        have htk : tb * ub ^ k * tb⁻¹ = ub ^ k := by rw [← conj_zpow, ← he]
        have e1 : π ⟨y₁ * b₁ * y₁⁻¹ * b₁⁻¹, M.mul_mem (M.mul_mem (M.mul_mem hy₁M hb₁M)
            (M.inv_mem hy₁M)) (M.inv_mem hb₁M)⟩ = 1 := by
          have e2 : (⟨y₁ * b₁ * y₁⁻¹ * b₁⁻¹, M.mul_mem (M.mul_mem (M.mul_mem hy₁M hb₁M)
              (M.inv_mem hy₁M)) (M.inv_mem hb₁M)⟩ : M) =
              ⟨y₁, hy₁M⟩ * ⟨b₁, hb₁M⟩ * ⟨y₁, hy₁M⟩⁻¹ * ⟨b₁, hb₁M⟩⁻¹ := rfl
          rw [e2, map_mul, map_mul, map_mul, map_inv, map_inv, ← htb, ← hk, htk,
            mul_inv_cancel]
        exact (hπ1 _).mp e1
      · rw [he3, h2] at he
        rw [← he]
        have : ub ^ (2 : ℤ) = ub⁻¹ := by
          have h3 : ub ^ (3 : ℤ) = 1 := by
            rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hub3]
          calc ub ^ (2 : ℤ) = ub ^ (3 : ℤ) * ub⁻¹ := by
                rw [show (3 : ℤ) = 2 + 1 by norm_num, zpow_add, zpow_one]; group
            _ = ub⁻¹ := by rw [h3, one_mul]
        exact this
    obtain ⟨g, hgM, hgℓ⟩ : ∃ g : G, ∃ hg : g ∈ M,
        g * ℓ * g⁻¹ ∈ U₂ ⊔ O := by
      have hπU₂' : ∀ (w : G) (hw : w ∈ M), π ⟨w, hw⟩ ∈ zpowers ub → w ∈ U₂ ⊔ O := by
        intro w hw hwz
        obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hwz
        rw [hub, hπK₀ u₀ hu₀K hu₀M j] at hj
        have h1 : (⟨u₀ ^ j, M.zpow_mem hu₀M j⟩ : M)⁻¹ * ⟨w, hw⟩ ∈ O.subgroupOf M :=
          QuotientGroup.eq.mp hj
        have h2 : (u₀ ^ j)⁻¹ * w ∈ O := mem_subgroupOf.mp h1
        have e : w = u₀ ^ j * ((u₀ ^ j)⁻¹ * w) := by group
        rw [e]
        exact mul_mem_sup (hu₀ ▸ zpow_mem_zpowers u₀ j) h2
      rcases e9r_exists_conj_mem_zpowers hℓb3 hℓu hlu hrℓ hru hr2 htℓ htu with h1 | h1
      · refine ⟨ρ, hρM, hπU₂' _ (M.mul_mem (M.mul_mem hρM hℓM) (M.inv_mem hρM)) ?_⟩
        rw [show (⟨ρ * ℓ * ρ⁻¹, M.mul_mem (M.mul_mem hρM hℓM) (M.inv_mem hρM)⟩ : M) =
          ⟨ρ, hρM⟩ * ⟨ℓ, hℓM⟩ * ⟨ρ, hρM⟩⁻¹ from rfl, hπc]
        exact h1
      · have hgM : ρ * y₁ * ρ * y₁⁻¹ ∈ M :=
          M.mul_mem (M.mul_mem (M.mul_mem hρM hy₁M) hρM) (M.inv_mem hy₁M)
        refine ⟨ρ * y₁ * ρ * y₁⁻¹, hgM, hπU₂' _ (M.mul_mem (M.mul_mem hgM hℓM) (M.inv_mem hgM))
          ?_⟩
        rw [show (⟨ρ * y₁ * ρ * y₁⁻¹ * ℓ * (ρ * y₁ * ρ * y₁⁻¹)⁻¹,
            M.mul_mem (M.mul_mem hgM hℓM) (M.inv_mem hgM)⟩ : M) =
          ⟨ρ * y₁ * ρ * y₁⁻¹, hgM⟩ * ⟨ℓ, hℓM⟩ * ⟨ρ * y₁ * ρ * y₁⁻¹, hgM⟩⁻¹ from rfl, hπc]
        have e : π ⟨ρ * y₁ * ρ * y₁⁻¹, hgM⟩ = rb * tb * rb * tb⁻¹ := by
          rw [hrb, htb, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
          rfl
        rw [e]
        exact h1
    have hXN : M ≤ normalizer ((omegaOneCenterOf (pCoreOf 2 M) : Subgroup G) : Set G) :=
      l43_normalizer_omegaOneCenter
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)
    have hU₂conj : ∀ w ∈ U₂ ⊔ O, w ^ 3 = 1 → w ≠ 1 →
        Nat.card (⁅omegaOneCenterOf (pCoreOf 2 M), zpowers w⁆ : Subgroup G) =
          Nat.card (⁅omegaOneCenterOf (pCoreOf 2 M), U₂⁆ : Subgroup G) := by
      intro w hw hw3 hw1
      obtain ⟨k, hk, hkw⟩ := e9r_exists_conj_zpowers_eq hU₂O h.O_cop hU₂card hw hw3 hw1
      have := l43_card_commutator_conj hXN (m := k⁻¹) (u := w) (M.inv_mem (hB₂M hk))
      rw [inv_inv, hkw] at this
      exact this.symm
    have hgℓ3 : (g * ℓ * g⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hK3 ℓ hℓ, mul_one, mul_inv_cancel]
    have hgℓ1 : g * ℓ * g⁻¹ ≠ 1 := by
      intro h1
      apply hℓ1
      calc ℓ = g⁻¹ * (g * ℓ * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have huB₂ : (u : G) ∈ U₂ ⊔ O := hT₂B u.2
    have h1 := hU₂conj _ hgℓ hgℓ3 hgℓ1
    have h2 := hU₂conj _ huB₂ hu3 hu1
    have h3 := l43_card_commutator_conj hXN (m := g) (u := ℓ) hgM
    rw [← h3, h1, ← h2]
    exact hX

theorem E9Case1DataR.exists_normalizer_le {M O K₀ : Subgroup G} {x : G}
    (h : E9Case1DataR G M O K₀ x) :
    ∃ ℓ ∈ K₀, ℓ ≠ 1 ∧ ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → IsSylowOf 2 (Y ⊓ O) O →
      x ∈ normalizer (Y : Set G) → ℓ ∈ normalizer (Y : Set G) →
        normalizer (Y : Set G) ≤ M := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ ℓ ∈ K₀, ℓ ≠ 1 →
      Nat.card (⁅omegaOneCenterOf (pCoreOf 2 M), zpowers ℓ⁆ : Subgroup G) = 4 := by
    intro ℓ hℓ hℓ1
    obtain ⟨Y, hY2, hYM, hYO, hxY, hℓY, hnot⟩ := hcon ℓ hℓ hℓ1
    by_cases hbig : ∃ Y₀ : Subgroup G, Y₀ ≤ Y ∧ Y₀ ≠ ⊥ ∧ (Y₀.subgroupOf Y).Characteristic ∧
        3 ≤ CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M)
    · exfalso
      obtain ⟨Y₀, hle, hne, hch, hr⟩ := hbig
      exact hnot ((l43_normalizer_le_of_characteristic hle hch).trans
        (h.D1 Y₀ hne (hY2.to_le hle) hr))
    · push Not at hbig
      exact h.card_eq_four_of_small hℓ hℓ1 hY2 hYM hYO hxY hℓY hbig
  have hXN : M ≤ normalizer ((omegaOneCenterOf (pCoreOf 2 M) : Subgroup G) : Set G) :=
    l43_normalizer_omegaOneCenter
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)
  exact l43_not_forall_card_commutator_eq_four h.K₀_el h.K₀_card
    (l43_isElemAbelian_omegaOneCenter
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M))
    (h.K₀_le.trans hXN) hall

end CFSG.LocalAnalysis.RankThreeTheoremC
