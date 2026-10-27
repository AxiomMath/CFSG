module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.GL83PartI.I_28_3_S3
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3Rest
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Comm
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Eigen
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Lift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43W

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin
  CFSG.Quasithin.F53Push CFSG.ABGLocalTools Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem e9_card_sup_mul_card_inf {A N : Subgroup G} (hAN : A ≤ normalizer (N : Set G)) :
    Nat.card (A ⊔ N : Subgroup G) * Nat.card (A ⊓ N : Subgroup G) =
      Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

omit [Finite G] in
theorem e9_le_normalizer_inf {M A C : Subgroup G} (hA : M ≤ normalizer (A : Set G))
    (hC : M ≤ normalizer (C : Set G)) : M ≤ normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have h1 := Subgroup.mem_normalizer_iff.1 (hA hg) h
  have h2 := Subgroup.mem_normalizer_iff.1 (hC hg) h
  exact ⟨fun hh => ⟨h1.1 hh.1, h2.1 hh.2⟩, fun hh => ⟨h1.2 hh.1, h2.2 hh.2⟩⟩

omit [Finite G] in
theorem e9_pow_three_mem_sup {O K : Subgroup G} (hKO : K ≤ normalizer (O : Set G))
    (hK3 : ∀ k ∈ K, k ^ 3 = 1) {b : G} (hb : b ∈ K ⊔ O) : b ^ 3 ∈ O := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right K O hKO
  have hb' : b ∈ (K : Set G) * (O : Set G) := by
    rw [← hset]
    exact hb
  obtain ⟨k, hk, o, ho, rfl⟩ := hb'
  have hkn : k ∈ normalizer (O : Set G) := hKO hk
  have h1 : k⁻¹ * o * k ∈ O := by
    have := (mem_normalizer_iff.mp (inv_mem hkn) o).mp ho
    simpa using this
  have h2 : k⁻¹ ^ 2 * o * k ^ 2 ∈ O := by
    have hk2 : k⁻¹ ^ 2 ∈ normalizer (O : Set G) := pow_mem (inv_mem hkn) 2
    have := (mem_normalizer_iff.mp hk2 o).mp ho
    simpa [inv_pow] using this
  have e : (k * o) ^ 3 = k ^ 3 * (k⁻¹ ^ 2 * o * k ^ 2) * (k⁻¹ * o * k) * o := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [e, hK3 k hk, one_mul]
  exact O.mul_mem (O.mul_mem h2 h1) ho

omit [Finite G] in
theorem e9_inf_sup_le {O K Y : Subgroup G} (hKO : K ≤ normalizer (O : Set G))
    (hK3 : ∀ k ∈ K, k ^ 3 = 1) (hY2 : IsPGroup 2 Y) : Y ⊓ (K ⊔ O) ≤ O := by
  rintro b ⟨hbY, hbB⟩
  have h3 : b ^ 3 ∈ O := e9_pow_three_mem_sup hKO hK3 hbB
  obtain ⟨j, hj⟩ := hY2 ⟨b, hbY⟩
  have hbj : b ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hord : orderOf b ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hbj
  have hcop : Nat.Coprime 3 (orderOf b) :=
    Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.pow_right _ (by norm_num))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact O.pow_mem h3 m

omit [Finite G] in
theorem e9_inf_eq_bot {K O : Subgroup G} (hK3 : ∀ k ∈ K, k ^ 3 = 1)
    (hO3 : ¬ 3 ∣ Nat.card O) : K ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgK, hgO⟩
  have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (hK3 g hgK)
  have hd2 : orderOf g ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨g, hgO⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact mem_bot.mpr (orderOf_eq_one_iff.mp h)
  · exact absurd (h ▸ hd2) hO3

omit [Finite G] in
theorem e9_comm_mem_sup {O K Y : Subgroup G} (hKO : K ≤ normalizer (O : Set G))
    (hYO : Y ≤ normalizer (O : Set G)) (hYK : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ O) :
    ∀ y ∈ Y, ∀ b ∈ K ⊔ O, y * b * y⁻¹ * b⁻¹ ∈ O := by
  let C : Subgroup G :=
    { carrier := {b | b ∈ normalizer (O : Set G) ∧ ∀ y ∈ Y, y * b * y⁻¹ * b⁻¹ ∈ O}
      mul_mem' := by
        rintro b₁ b₂ ⟨hb₁N, hb₁⟩ ⟨hb₂N, hb₂⟩
        refine ⟨(normalizer (O : Set G)).mul_mem hb₁N hb₂N, fun y hy => ?_⟩
        have e : y * (b₁ * b₂) * y⁻¹ * (b₁ * b₂)⁻¹ =
            (y * b₁ * y⁻¹ * b₁⁻¹) * (b₁ * (y * b₂ * y⁻¹ * b₂⁻¹) * b₁⁻¹) := by group
        rw [e]
        exact O.mul_mem (hb₁ y hy) ((mem_normalizer_iff.mp hb₁N _).mp (hb₂ y hy))
      one_mem' := ⟨(normalizer (O : Set G)).one_mem, fun y _ => by simp⟩
      inv_mem' := by
        rintro b ⟨hbN, hb⟩
        refine ⟨(normalizer (O : Set G)).inv_mem hbN, fun y hy => ?_⟩
        have e : y * b⁻¹ * y⁻¹ * b⁻¹⁻¹ = b⁻¹ * (y * b * y⁻¹ * b⁻¹)⁻¹ * b⁻¹⁻¹ := by group
        rw [e]
        exact (mem_normalizer_iff.mp ((normalizer (O : Set G)).inv_mem hbN) _).mp
          (O.inv_mem (hb y hy)) }
  have hK : K ≤ C := fun k hk => ⟨hKO hk, fun y hy => hYK y hy k hk⟩
  have hO : O ≤ C := fun o ho => ⟨Subgroup.le_normalizer ho, fun y hy => by
    exact O.mul_mem ((mem_normalizer_iff.mp (hYO hy) o).mp ho) (O.inv_mem ho)⟩
  intro y hy b hb
  exact (sup_le hK hO hb).2 y hy

omit [Finite G] in
theorem e9_le_of_normal {O N S : Subgroup G} (hNO : N ≤ O) (hNn : O ≤ normalizer (N : Set G))
    (hN2 : IsPGroup 2 N) (hS : IsSylowOf 2 S O) : N ≤ S := by
  obtain ⟨Q, hQ⟩ := hS
  have hnorm : (N.subgroupOf O).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNO).mpr hNn
  have hp : IsPGroup 2 (N.subgroupOf O) := hN2.comap_subtype
  have hle : N.subgroupOf O ≤ (Q : Subgroup O) := hp.le_sylow_of_normal Q
  intro g hg
  have hg' : (⟨g, hNO hg⟩ : O) ∈ N.subgroupOf O := hg
  rw [← hQ]
  exact ⟨⟨g, hNO hg⟩, hle hg', rfl⟩

structure E9Case1Data (G : Type) [Group G] [Finite G] (M O K₀ : Subgroup G) (x : G) :
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
  trans : ∀ a ∈ K₀, ∀ b ∈ K₀, a ≠ 1 → b ≠ 1 → ∃ n ∈ M, n * a * n⁻¹ = b
  D1 : ∀ Y₀ : Subgroup G, Y₀ ≠ ⊥ → IsPGroup 2 Y₀ →
    3 ≤ CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M) → normalizer (Y₀ : Set G) ≤ M

theorem E9Case1Data.false_of_small {M O K₀ : Subgroup G} {x : G} (h : E9Case1Data G M O K₀ x)
    {ℓ : G} (hℓ : ℓ ∈ K₀) (hℓ1 : ℓ ≠ 1) {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M)
    (hYO : IsSylowOf 2 (Y ⊓ O) O) (hxY : x ∈ normalizer (Y : Set G))
    (hℓY : ℓ ∈ normalizer (Y : Set G))
    (hsmall : ∀ Y₀ : Subgroup G, Y₀ ≤ Y → Y₀ ≠ ⊥ → (Y₀.subgroupOf Y).Characteristic →
      CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M) < 3) : False := by
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
    have huB : (u : G) ∈ K₀ ⊔ O := sup_le_sup_right hU₂K O (hT₂B u.2)
    have hK₀p : IsPGroup 3 K₀ :=
      CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 3 K₀ h.K₀_el
    have hK₀syl : IsSylowOf 3 K₀ (K₀ ⊔ O) := by
      refine isSylowOf_iff.mpr ⟨le_sup_left, hK₀p, ?_⟩
      have hc := e9_card_sup_mul_card_inf hK₀O
      rw [e9_inf_eq_bot hK3 h.O_cop, Subgroup.card_bot, h.K₀_card, mul_one] at hc
      have hrel := Subgroup.relIndex_mul_card (H := K₀) (K := K₀ ⊔ O)
      rw [inf_of_le_left le_sup_left, h.K₀_card, hc] at hrel
      have : K₀.relIndex (K₀ ⊔ O) = Nat.card O := by omega
      rw [this]
      exact h.O_cop
    obtain ⟨k, hkB, hk⟩ : ∃ k ∈ K₀ ⊔ O, k⁻¹ * (u : G) * k ∈ K₀ := by
      have hzp : IsPGroup 3 ((zpowers (u : G)).subgroupOf (K₀ ⊔ O)) := by
        have : IsPGroup 3 (zpowers (u : G)) :=
          IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, huG]; simp)
        exact this.comap_subtype
      obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
      have hQs : IsSylowOf 3 (Q.map (K₀ ⊔ O).subtype) (K₀ ⊔ O) := ⟨Q, rfl⟩
      obtain ⟨k, hkB, hkk⟩ := hK₀syl.exists_mem_conj hQs
      refine ⟨k, hkB, (hkk (u : G)).mp ?_⟩
      exact ⟨⟨u, huB⟩, hQ (Subgroup.mem_subgroupOf.mpr (mem_zpowers _)), rfl⟩
    have hu₂1 : k⁻¹ * (u : G) * k ≠ 1 := by
      intro h1
      apply hu1
      have : (u : G) = k * (k⁻¹ * (u : G) * k) * k⁻¹ := by group
      rw [this, h1]
      group
    have hXN : M ≤ normalizer ((omegaOneCenterOf (pCoreOf 2 M) : Subgroup G) : Set G) :=
      l43_normalizer_omegaOneCenter
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)
    have hk4 : Nat.card (⁅omegaOneCenterOf (pCoreOf 2 M), zpowers (k⁻¹ * (u : G) * k)⁆ :
        Subgroup G) = 4 := by
      have := l43_card_commutator_conj hXN (m := k⁻¹) (u := (u : G)) (M.inv_mem (hBM hkB))
      rw [inv_inv] at this
      rw [this]
      exact hX
    have hall : ∀ kk ∈ K₀, kk ≠ 1 →
        Nat.card (⁅omegaOneCenterOf (pCoreOf 2 M), zpowers kk⁆ : Subgroup G) = 4 := by
      intro kk hkk hkk1
      obtain ⟨n, hn, hnk⟩ := h.trans _ hk kk hkk hu₂1 hkk1
      have := l43_card_commutator_conj hXN (m := n) (u := k⁻¹ * (u : G) * k) hn
      rw [hnk] at this
      rw [this]
      exact hk4
    exact l43_not_forall_card_commutator_eq_four h.K₀_el h.K₀_card
      (l43_isElemAbelian_omegaOneCenter
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M))
      (h.K₀_le.trans hXN) hall

theorem E9Case1Data.normalizer_le {M O K₀ : Subgroup G} {x : G} (h : E9Case1Data G M O K₀ x)
    {ℓ : G} (hℓ : ℓ ∈ K₀) (hℓ1 : ℓ ≠ 1) {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M)
    (hYO : IsSylowOf 2 (Y ⊓ O) O) (hxY : x ∈ normalizer (Y : Set G))
    (hℓY : ℓ ∈ normalizer (Y : Set G)) : normalizer (Y : Set G) ≤ M := by
  by_cases hbig : ∃ Y₀ : Subgroup G, Y₀ ≤ Y ∧ Y₀ ≠ ⊥ ∧ (Y₀.subgroupOf Y).Characteristic ∧
      3 ≤ CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M)
  · obtain ⟨Y₀, hle, hne, hch, hr⟩ := hbig
    exact (l43_normalizer_le_of_characteristic hle hch).trans (h.D1 Y₀ hne (hY2.to_le hle) hr)
  · push Not at hbig
    exact (h.false_of_small hℓ hℓ1 hY2 hYM hYO hxY hℓY hbig).elim

end CFSG.LocalAnalysis.RankThreeTheoremC
