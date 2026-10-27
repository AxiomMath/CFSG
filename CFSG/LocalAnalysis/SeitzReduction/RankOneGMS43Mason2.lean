module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Chain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Mason
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Mason2Basic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974)

namespace GMS43

namespace Hyp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T V₁ U₁ : Subgroup G} {y d : G} (h : Hyp L f t T V₁ U₁ y d)
include h

theorem card_commutator_t_le : Nat.card (⁅U₁, zpowers t⁆ : Subgroup G) ≤ 2 ^ f := by
  have h1 := card_commutator_mul_card_inf_centralizer_le h.comm h.t_mem_normalizer
  rw [h.result.centralizer_eq, h.card_U, h.card_U₁, sq] at h1
  exact Nat.le_of_mul_le_mul_right h1 (by positivity)

theorem le_card_commutator_of_mem_sup {w : G} (hw : w ∈ U₁ ⊔ T) (hwE : w ∉ U₁) :
    2 ^ f ≤ Nat.card (⁅U₁, zpowers w⁆ : Subgroup G) := by
  have h1 := GMS28.card_le_card_inf_centralizer_mul h.comm (h.sup_le_normalizer hw)
  have h2 := h.card_inf_centralizer_le hw hwE
  rw [h.card_U₁, sq] at h1
  exact Nat.le_of_mul_le_mul_left (h1.trans (Nat.mul_le_mul_right _ h2)) (by positivity)

theorem false_of_masonConfig (hx : ∃ x ∈ U₁ ⊔ T, x * x = 1 ∧ x ∉ U₁ ⊔ zpowers t)
    {S : Subgroup G} (hSp : IsPGroup 2 S) (hSN : S ≤ normalizer (U₁ : Set G))
    (hlt : U₁ ⊔ T < S) {X : Subgroup G} (hXS : X ≤ S) (hX2 : ∀ x ∈ X, x * x = 1)
    (hXE : ¬ X ≤ U₁) (hXt : ∀ x ∈ X, ∀ g : G, g⁻¹ * t * g ≠ x)
    (hXcard : ∀ x ∈ X, Nat.card (⁅U₁, zpowers x⁆ : Subgroup G) ≤ U₁.relIndex X) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hES : U₁ ⊔ T ≤ S := hlt.le
  have hUS : U₁ ≤ S := le_sup_left.trans hES
  have : (U₁.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hUS).mpr hSN
  have hQp : IsPGroup 2 (S ⧸ U₁.subgroupOf S) := hSp.to_quotient _
  have htS : t ∈ S := hES (mem_sup_right h.mem_T)
  set s₀ : S := ⟨t, htS⟩
  have hs₀ : (s₀ : G) = t := rfl
  set j := QuotientGroup.mk' (U₁.subgroupOf S) s₀ with hj
  obtain ⟨τ, hτT, hττ, hτV⟩ := h.exists_involution_iff.mp hx
  have hjj : j * j = 1 := by
    rw [hj, ← map_mul, mk'_eq_one_iff, Subgroup.coe_mul, hs₀, h.t_mul_t]
    exact one_mem _
  have hcomm_iff := h.mk'_mul_comm_iff hSp hES hs₀
  set Y := (X.subgroupOf S).map (QuotientGroup.mk' (U₁.subgroupOf S)) with hY
  have hYcard : Nat.card Y = U₁.relIndex X := by
    rw [hY, ← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf hXS]
  have hY2 : ∀ v ∈ Y, v * v = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, mk'_eq_one_iff, Subgroup.coe_mul, hX2 _ (mem_subgroupOf.mp ha)]
    exact one_mem _
  have hYj : ∀ v ∈ Y, ¬ IsConj j v := by
    rintro _ ⟨a, ha, rfl⟩
    exact h.not_isConj_mk' hES hs₀ (hX2 _ (mem_subgroupOf.mp ha)) (hXt _ (mem_subgroupOf.mp ha))
  obtain ⟨hY8, hYC⟩ := card_le_of_forall_not_isConj' hQp hjj (h.mk'_comm_of_comm hSp hES hs₀)
    (h.mk'_eq_of_mul_self_eq_one hSp hES hs₀ (τ₀ := ⟨τ, hES (mem_sup_right hτT)⟩) hτT hττ hτV)
    hY2 hYj
  have h16 := h.sixteen_le hx
  rcases (Y ⊓ centralizer ({j} : Set (S ⧸ U₁.subgroupOf S))).bot_or_exists_ne_one with
    hYC0 | ⟨v, hv, hv1⟩
  swap
  ·
    obtain ⟨⟨a, ha, rfl⟩, hvC⟩ := mem_inf.mp hv
    have haS₀ := (hcomm_iff a).mp (mem_centralizer_singleton_iff.mp hvC)
    have haE : (a : G) ∉ U₁ := fun h' => hv1 ((mk'_eq_one_iff a).mpr h')
    have hka := h.le_card_commutator_of_mem_sup haS₀ haE
    have := (hXcard _ (mem_subgroupOf.mp ha)).trans (hYcard ▸ hY8)
    omega
  obtain ⟨hY4, hY4'⟩ := hYC hYC0
  obtain ⟨x, hxX, hxE⟩ := IsConcreteLE.not_le_iff_exists.mp hXE
  have hx0 : x ∉ U₁ ⊔ T := by
    intro hx0
    have hmem : QuotientGroup.mk' (U₁.subgroupOf S) ⟨x, hXS hxX⟩ ∈
        Y ⊓ centralizer ({j} : Set (S ⧸ U₁.subgroupOf S)) :=
      mem_inf.mpr ⟨⟨⟨x, hXS hxX⟩, mem_subgroupOf.mpr hxX, rfl⟩,
        mem_centralizer_singleton_iff.mpr ((hcomm_iff _).mpr hx0)⟩
    rw [hYC0, mem_bot, mk'_eq_one_iff] at hmem
    exact hxE hmem
  rcases Nat.lt_or_ge (Nat.card Y) 4 with hY3 | hY4eq
  ·
    have hC4 := h.card_inf_centralizer_sq_le_of_not_mem hSp hSN hES (hXS hxX) hx0
    have hlow := GMS28.card_le_card_inf_centralizer_mul h.comm (hSN (hXS hxX))
    have hk : Nat.card (⁅U₁, zpowers x⁆ : Subgroup G) ≤ 3 := (hXcard x hxX).trans (by omega)
    rw [h.card_U₁] at hlow
    set c := Nat.card (U₁ ⊓ centralizer ({x} : Set G) : Subgroup G)
    set k := Nat.card (⁅U₁, zpowers x⁆ : Subgroup G)
    set q := 2 ^ f
    have h1 : (q ^ 2) ^ 2 ≤ (c * k) ^ 2 := Nat.pow_le_pow_left hlow 2
    have h3 : (c * k) ^ 2 ≤ q ^ 3 * 9 := by
      rw [mul_pow]
      exact Nat.mul_le_mul hC4 (by nlinarith)
    have h5 : q ^ 3 * q ≤ q ^ 3 * 9 := by
      calc q ^ 3 * q = (q ^ 2) ^ 2 := by ring
        _ ≤ _ := h1.trans h3
    have := Nat.le_of_mul_le_mul_left h5 (by positivity)
    omega
  have hY4eq' : Nat.card Y = 4 := le_antisymm hY4 hY4eq
  obtain ⟨_, ⟨a, ha, rfl⟩, hvord⟩ := hY4' hY4eq'
  have haX : (a : G) ∈ X := mem_subgroupOf.mp ha
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  have hdvd := (centralizer ({j} : Set (S ⧸ U₁.subgroupOf S))).index_dvd_card
  rw [hk] at hdvd
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, index_eq_one] at hn
    obtain ⟨s, hsS, hsE⟩ := IsConcreteLE.exists_of_lt hlt
    have hsC : QuotientGroup.mk' (U₁.subgroupOf S) ⟨s, hsS⟩ ∈
        centralizer ({j} : Set (S ⧸ U₁.subgroupOf S)) := hn ▸ mem_top _
    exact hsE ((hcomm_iff ⟨s, hsS⟩).mp (mem_centralizer_singleton_iff.mp hsC))
  rw [hn] at hvord
  set b := j * QuotientGroup.mk' (U₁.subgroupOf S) a with hb
  have hvv : QuotientGroup.mk' (U₁.subgroupOf S) a * QuotientGroup.mk' (U₁.subgroupOf S) a = 1 :=
    hY2 _ ⟨a, ha, rfl⟩
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hjj
  have hjb : j * b * j⁻¹ = b⁻¹ := by
    rw [hb, hjinv, mul_inv_rev, inv_eq_of_mul_eq_one_right hvv, hjinv, ← mul_assoc, hjj, one_mul]
  have hc2 : b ^ 2 ^ n * b ^ 2 ^ n = 1 := by
    rw [← pow_add, ← two_mul, ← hvord, pow_orderOf_eq_one]
  have hc1 : b ^ 2 ^ n ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (by positivity) ?_
    rw [hvord]
    have := Nat.one_le_two_pow (n := n)
    omega
  have hcj : b ^ 2 ^ n * j = j * b ^ 2 ^ n := by
    have h1 : j * b ^ 2 ^ n * j⁻¹ = b ^ 2 ^ n := by
      rw [← conj_pow, hjb, inv_pow, inv_eq_of_mul_eq_one_right hc2]
    calc b ^ 2 ^ n * j = j * b ^ 2 ^ n * j⁻¹ * j := by rw [h1]
      _ = j * b ^ 2 ^ n := by group
  have hlift : b ^ 2 ^ n = QuotientGroup.mk' (U₁.subgroupOf S) ((s₀ * a) ^ 2 ^ n) := by
    rw [hb, hj, ← map_mul, ← map_pow]
  have hcoe : (((s₀ * a) ^ 2 ^ n : S) : G) = (t * a) ^ 2 ^ n := by
    rw [Subgroup.coe_pow, Subgroup.coe_mul, hs₀]
  rw [hlift] at hc1 hcj
  have hw₀ : (t * (a : G)) ^ 2 ^ n ∈ U₁ ⊔ T := by
    rw [← hcoe]
    exact (hcomm_iff _).mp hcj
  have hwE : (t * (a : G)) ^ 2 ^ n ∉ U₁ := by
    rw [← hcoe]
    exact fun h' => hc1 ((mk'_eq_one_iff _).mpr h')
  have hkw := h.le_card_commutator_of_mem_sup hw₀ hwE
  have hne : ⁅U₁, zpowers ((t * (a : G)) ^ 2 ^ n)⁆ ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hkw
    omega
  have h2 : IsPGroup 2 (zpowers (t * (a : G))) :=
    hSp.to_le (zpowers_le.mpr (mul_mem htS a.2))
  have hM2 := two_pow_mul_card_commutator_mul_pow_le h.elem h.comm h.t_mem_normalizer
    (hSN a.2) h2 n hne
  have hEt := h.card_commutator_t_le
  have hEa : Nat.card (⁅U₁, zpowers (a : G)⁆ : Subgroup G) ≤ 4 :=
    (hXcard _ haX).trans (hYcard ▸ hY4)
  have h3 : 2 ^ (2 ^ n - 1) * 2 ^ f ≤ 4 * 2 ^ f := by
    calc 2 ^ (2 ^ n - 1) * 2 ^ f
        ≤ 2 ^ (2 ^ n - 1) * Nat.card (⁅U₁, zpowers ((t * (a : G)) ^ 2 ^ n)⁆ : Subgroup G) :=
          Nat.mul_le_mul_left _ hkw
      _ ≤ _ := hM2
      _ ≤ 2 ^ f * 4 := Nat.mul_le_mul hEt hEa
      _ = 4 * 2 ^ f := Nat.mul_comm _ _
  have h4 : 2 ^ (2 ^ n - 1) ≤ 4 := Nat.le_of_mul_le_mul_right h3 (by positivity)
  have hn1 : n = 1 := by
    by_contra hn1
    have h5 : 4 ≤ 2 ^ n :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h6 : 8 ≤ 2 ^ (2 ^ n - 1) :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hn1, pow_one] at hn
  have : (centralizer ({j} : Set (S ⧸ U₁.subgroupOf S))).Normal := normal_of_index_eq_two hn
  have hdvd2 := relIndex_dvd_index_of_normal (centralizer ({j} : Set (S ⧸ U₁.subgroupOf S))) Y
  have hmc := relIndex_mul_card (centralizer ({j} : Set (S ⧸ U₁.subgroupOf S))) Y
  rw [inf_comm, hYC0, card_bot, mul_one, hY4eq'] at hmc
  rw [hmc, hn] at hdvd2
  exact absurd (Nat.le_of_dvd (by norm_num) hdvd2) (by norm_num)

end Hyp

end GMS43

theorem gms43MasonInput : GMS43MasonInput := by
  intro G _ _ L f t T V₁ U₁ y d hGold hS hR hel hx _ S hsyl hlt X hXS hX2 hXE hXt hXcard
  exact (GMS43.Hyp.mk hGold hS hR hel).false_of_masonConfig hx hsyl.isPGroup hsyl.le hlt hXS hX2
    hXE hXt hXcard

end CFSG.SeitzReduction.RankOne
