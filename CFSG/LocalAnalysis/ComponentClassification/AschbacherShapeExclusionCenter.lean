module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionConfig
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitCentralExtension
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

open Subgroup

variable {G : Type*} [Group G]

namespace Config

variable {S : Subgroup G} {t x ρ : G} {k : ℕ}

theorem y_pow_four (h : Config S t x ρ k) : h.y ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, h.y_sq, ← pow_mul]
  exact h.x_pow_four

theorem y_mem_zpowers_of_sq_ne_one (h : Config S t x ρ k) {w : G} (hw : w ∈ zpowers ρ)
    (hw2 : w ^ 2 ≠ 1) : h.y ∈ zpowers w := by
  have hdvd : orderOf w ∣ 2 ^ k := by
    rw [← h.rho_order]
    exact orderOf_dvd_of_mem_zpowers hw
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj2 : 2 ≤ j := by
    by_contra hlt
    apply hw2
    rw [← orderOf_dvd_iff_pow_eq_one, hj]
    exact (pow_dvd_pow 2 (by omega : j ≤ 1)).trans (by norm_num)
  set g := w ^ 2 ^ (j - 2) with hg
  have hgo : orderOf g = 4 := by
    rw [hg, orderOf_pow_of_dvd (by positivity) (by rw [hj]; exact pow_dvd_pow 2 (by omega)), hj,
      Nat.pow_div (by omega) (by norm_num), show j - (j - 2) = 2 by omega]
  have hgρ : g ∈ zpowers ρ := pow_mem hw _
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hgρ
  have hg4 : (ρ ^ m) ^ 4 = 1 := by rw [hm, ← hgo]; exact pow_orderOf_eq_one g
  obtain ⟨c, hc⟩ := h.rho_zpow_four hg4
  rw [hm] at hc
  obtain ⟨d, rfl | rfl⟩ := Int.even_or_odd' c
  · exfalso
    have : g ^ 2 = 1 := by
      rw [hc, ← zpow_natCast, ← zpow_mul, show (2 * d * ((2 : ℕ) : ℤ)) = 4 * d by push_cast; ring,
        zpow_mul, show h.y ^ (4 : ℤ) = h.y ^ 4 by norm_cast, h.y_pow_four, one_zpow]
    have := orderOf_dvd_of_pow_eq_one this
    rw [hgo] at this
    norm_num at this
  · have hyg : h.y = g ^ (2 * d + 1) := by
      rw [hc, ← zpow_mul, show (2 * d + 1) * (2 * d + 1) = 4 * (d * d + d) + 1 by ring,
        zpow_add, zpow_mul, show h.y ^ (4 : ℤ) = h.y ^ 4 by norm_cast, h.y_pow_four, one_zpow,
        one_mul, zpow_one]
    rw [hyg, hg]
    exact zpow_mem (pow_mem (mem_zpowers w) _) _

end Config

variable {A : Subgroup G}

theorem central_le_commutator [Finite G] (hA : CFSG.Open.IsQuasisimple A) (S₀ : Sylow 2 A) :
    (S₀ : Subgroup A).map A.subtype ⊓ centralizer (A : Set G) ≤
      ⁅(S₀ : Subgroup A).map A.subtype, (S₀ : Subgroup A).map A.subtype⁆ := by
  intro w hw
  obtain ⟨hwS, hwc⟩ := mem_inf.1 hw
  obtain ⟨a, haS, rfl⟩ := hwS
  set Z : Subgroup A := center A ⊓ (S₀ : Subgroup A) with hZ
  have haZ : a ∈ Z := by
    refine mem_inf.2 ⟨?_, haS⟩
    rw [mem_center_iff]
    intro b
    exact Subtype.ext (mem_centralizer_iff.1 hwc b b.2)
  have hZp : IsPGroup 2 Z := S₀.isPGroup'.to_le inf_le_right
  have hG := AschbacherToolkit.central_sylow_commutator S₀ (Z := Z) inf_le_left hZp
  have haZ' : a ∈ Z ⊓ commutator A := mem_inf.2 ⟨haZ, by rw [hA.1]; exact mem_top a⟩
  rw [hG] at haZ'
  obtain ⟨b, hb, rfl⟩ := (mem_inf.1 haZ').2
  rw [← map_commutator, ← Subgroup.map_subtype_commutator]
  exact ⟨_, ⟨b, hb, rfl⟩, rfl⟩

namespace Config

variable {S : Subgroup G} {t x ρ : G} {k : ℕ}

theorem x_sq_mem_of_ne_one [Finite G] (h : Config S t x ρ k) (hS2 : IsPGroup 2 S)
    (htA : t ∈ normalizer (A : Set G)) {w : G} (hwS : w ∈ S)
    (hwA : w ∈ centralizer (A : Set G)) (hw1 : w ≠ 1) : x ^ 2 ∈ centralizer (A : Set G) := by
  have htt : t * t = 1 := by rw [← pow_two, h.t_sq]
  set W := S ⊓ centralizer (A : Set G) with hW
  have hWp : IsPGroup 2 W := hS2.to_le inf_le_left
  have htW : ∀ g ∈ W, t * g * t⁻¹ ∈ W := by
    intro g hg
    obtain ⟨hgS, hgc⟩ := mem_inf.1 hg
    refine mem_inf.2 ⟨h.t_conj_mem_S hgS, ?_⟩
    rw [mem_centralizer_iff]
    intro a ha
    have hta : t⁻¹ * a * t ∈ A := by
      have := (mem_normalizer_iff.1 (inv_mem htA) a).1 ha
      simpa using this
    have hc := mem_centralizer_iff.1 hgc _ hta
    calc a * (t * g * t⁻¹) = t * ((t⁻¹ * a * t) * g) * t⁻¹ := by group
      _ = t * (g * (t⁻¹ * a * t)) * t⁻¹ := by rw [hc]
      _ = t * g * t⁻¹ * a := by group
  have htN : t ∈ normalizer (W : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    refine ⟨htW g, fun hg => ?_⟩
    have := htW _ hg
    rwa [h.t_inv, show t * (t * g * t) * t = (t * t) * g * (t * t) by group, htt, one_mul,
      mul_one] at this
  have htp : IsPGroup 2 (zpowers t) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact h.t_sq) : orderOf t ∣ 2 ^ 1)
    exact ⟨i, hi⟩
  set Q := W ⊔ zpowers t with hQ
  have hQp : IsPGroup 2 Q := hWp.to_sup_of_normal_left' htp (zpowers_le.2 htN)
  have hWQ : W ≤ Q := le_sup_left
  have hQN : Q ≤ normalizer (W : Set G) := sup_le le_normalizer (zpowers_le.2 htN)
  have hHn : (W.subgroupOf Q).Normal := by
    rw [normal_subgroupOf_iff hWQ]
    intro g q hg hq
    exact (mem_normalizer_iff.1 (hQN hq) g).1 hg
  have hH : W.subgroupOf Q ≠ ⊥ := by
    intro hbot
    apply hw1
    have hmem : (⟨w, hWQ (mem_inf.2 ⟨hwS, hwA⟩)⟩ : Q) ∈ W.subgroupOf Q :=
      mem_subgroupOf.2 (mem_inf.2 ⟨hwS, hwA⟩)
    rw [hbot, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have : Group.IsNilpotent Q := hQp.isNilpotent
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hH
  obtain ⟨⟨q, hq⟩, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hqW : (q : G) ∈ W := mem_subgroupOf.1 (mem_inf.1 hq).1
  have hqt : (q : G) * t = t * q := by
    have := mem_center_iff.1 (mem_inf.1 hq).2 ⟨t, mem_sup_right (mem_zpowers t)⟩
    exact (congrArg Subtype.val this).symm
  have hqx : (q : G) ∈ zpowers x := h.cent _ (mem_inf.1 hqW).1 hqt
  have hq1' : (q : G) ≠ 1 := fun h1 => hq1 (Subtype.ext (Subtype.ext h1))
  have hx2W : x ^ 2 ∈ W := by
    by_cases hq2 : (q : G) ^ 2 = 1
    · rcases Lemma37.mem_zpowers_sq_eq_one h.x_order hqx hq2 with h1 | h1
      · exact absurd h1 hq1'
      · rw [← h1]
        exact hqW
    · rcases Lemma37.mem_zpowers_sq_ne_one h.x_order hqx hq2 with h1 | h1
      · rw [← h1]
        exact pow_mem hqW 2
      · have : x ^ 2 = ((q : G) ^ 2)⁻¹ := by rw [h1, inv_pow, inv_inv]
        rw [this]
        exact inv_mem (pow_mem hqW 2)
  exact (mem_inf.1 hx2W).2

theorem central_le_zpowers_x_sq [Finite G] (hA : CFSG.Open.IsQuasisimple A) (S₀ : Sylow 2 A)
    (h : Config ((S₀ : Subgroup A).map A.subtype) t x ρ k) :
    (S₀ : Subgroup A).map A.subtype ⊓ centralizer (A : Set G) ≤ zpowers (x ^ 2) := by
  intro w hw
  have hcomm := central_le_commutator hA S₀ hw
  have hwρ : w ∈ zpowers ρ := h.commutator_le_zpowers_rho hcomm
  by_cases hy : ∀ g ∈ (S₀ : Subgroup A).map A.subtype, g * h.y = h.y * g
  · exact h.commutator_le_zpowers_z hy hcomm
  · by_cases hw2 : w ^ 2 = 1
    · obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hwρ
      rcases h.rho_zpow_sq hw2 with h1 | h1 <;> rw [h1]
      · exact one_mem _
      · exact mem_zpowers _
    · exfalso
      apply hy
      have hyw := h.y_mem_zpowers_of_sq_ne_one hwρ hw2
      have hyc : h.y ∈ centralizer (A : Set G) := (zpowers_le.2 (mem_inf.1 hw).2) hyw
      intro g hg
      exact mem_centralizer_iff.1 hyc g (map_subtype_le _ hg)

end Config

end CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion
