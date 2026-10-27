module

public import CFSG.CGT.Timmesfeld75.Sec5NineLift
public import CFSG.CGT.Timmesfeld75.Sec6Ctx

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_of_card_two {K : Subgroup G} (hK : Nat.card K = 2) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  obtain ⟨u, v, huv, hall⟩ := Nat.card_eq_two_iff.1 hK
  have key : ∀ k : K, k = u ∨ k = v := fun k => by
    have : k ∈ ({u, v} : Set K) := by rw [hall]; exact Set.mem_univ k
    simpa using this
  have h1 := key 1
  have h2 := key ⟨x, hx⟩
  have h3 := key ⟨y, hy⟩
  have hx' : (⟨x, hx⟩ : K) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hy' : (⟨y, hy⟩ : K) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  apply congrArg Subtype.val (a₁ := (⟨x, hx⟩ : K)) (a₂ := ⟨y, hy⟩)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    first | exact h2.trans h3.symm | (exfalso; exact hx' (h2.trans h1.symm)) |
      (exfalso; exact hy' (h3.trans h1.symm))

section ZStar

variable {T T₁ : Subgroup G}

theorem card_normIn_swap_two [Finite G] (hc : Sec6Ctx T T₁ 2 1) :
    Nat.card (normIn T₁ T) = 2 := by
  rw [hc.card_normIn_swap, hc.card_normIn]
  norm_num

theorem card_normIn_two [Finite G] (hc : Sec6Ctx T T₁ 2 1) :
    Nat.card (normIn T T₁) = 2 := by
  rw [hc.card_normIn]
  norm_num

theorem isolated_bar [Finite G] (hc : Sec6Ctx T T₁ 2 1)
    (h48 : IsWC (barSub T (normIn T₁ T))) {ℓ : G} (hℓ : ℓ ∈ normIn T₁ T) (hℓ1 : ℓ ≠ 1)
    (hℓN : ℓ ∈ Subgroup.normalizer (T : Set G)) (g : NQuot T)
    (hcomm : g * barElt T hℓN * g⁻¹ * barElt T hℓN = barElt T hℓN * (g * barElt T hℓN * g⁻¹)) :
    g * barElt T hℓN * g⁻¹ = barElt T hℓN := by
  have hS3 := hc.sec3
  have hℓT : ℓ ∉ T := fun h => by
    have h' : ℓ ∈ T ⊓ T₁ := ⟨h, normIn_le _ _ hℓ⟩
    rw [hS3.cfg.inf, Subgroup.mem_bot] at h'
    exact hℓ1 h'
  have hlb1 : barElt T hℓN ≠ 1 := fun h => hℓT ((barElt_eq_one_iff hℓN).1 h)
  have hW : barElt T hℓN ∈ barSub T (normIn T₁ T) := barElt_mem_barSub hℓN hℓ
  have hWeq : ∀ w ∈ barSub T (normIn T₁ T), w = 1 ∨ w = barElt T hℓN := by
    intro w hw
    obtain ⟨u, hu, huL, rfl⟩ := exists_eq_barElt_of_mem_barSub hw
    by_cases hu1 : u = 1
    · subst hu1
      exact Or.inl ((barElt_eq_one_iff hu).2 (Subgroup.one_mem _))
    · right
      have := eq_of_card_two (card_normIn_swap_two hc) huL hℓ hu1 hℓ1
      subst this
      rfl
  have hwc := (h48.2 _ hW hlb1).2 g (fun y hy => by
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
    rcases hWeq w hw with rfl | rfl
    · simp only [map_one]
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp
    · rw [Subgroup.mem_centralizer_singleton_iff]
      simpa [MulAut.conj_apply] using hcomm)
  have hmem : g * barElt T hℓN * g⁻¹ ∈ conjSubgroup g (barSub T (normIn T₁ T)) :=
    ⟨barElt T hℓN, hW, by simp [MulAut.conj_apply]⟩
  rw [hwc] at hmem
  rcases hWeq _ hmem with h | h
  · exfalso
    apply hlb1
    calc barElt T hℓN = g⁻¹ * (g * barElt T hℓN * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · exact h

theorem exists_odd_normal_image [Finite G] (hc : Sec6Ctx T T₁ 2 1)
    (h48 : IsWC (barSub T (normIn T₁ T))) {ℓ : G} (hℓ : ℓ ∈ normIn T₁ T) (hℓ1 : ℓ ≠ 1)
    (hℓN : ℓ ∈ Subgroup.normalizer (T : Set G)) :
    ∃ (O : Subgroup (NQuot T)) (_ : O.Normal), Odd (Nat.card O) ∧
      ∀ y ∈ hSub T (normIn T₁ T), ∃ hy : y ∈ Subgroup.normalizer (T : Set G),
        (QuotientGroup.mk (barElt T hy) : NQuot T ⧸ O) = 1 ∨
          (QuotientGroup.mk (barElt T hy) : NQuot T ⧸ O) = QuotientGroup.mk (barElt T hℓN) := by
  classical
  have hS3 := hc.sec3
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  have hℓT : ℓ ∉ T := fun h => by
    have h' : ℓ ∈ T ⊓ T₁ := ⟨h, normIn_le _ _ hℓ⟩
    rw [hS3.cfg.inf, Subgroup.mem_bot] at h'
    exact hℓ1 h'
  have hℓℓ : ℓ * ℓ = 1 := elemAbelian_mul_self hS3.cfg.wc₁.1 (normIn_le _ _ hℓ)
  have hlb1 : barElt T hℓN ≠ 1 := fun h => hℓT ((barElt_eq_one_iff hℓN).1 h)
  have hlbsq : barElt T hℓN * barElt T hℓN = 1 := by
    have : barElt T hℓN * barElt T hℓN =
        barElt T ((Subgroup.normalizer (T : Set G)).mul_mem hℓN hℓN) := rfl
    rw [this, barElt_eq_one_iff, hℓℓ]
    exact T.one_mem
  have hlbinv : (barElt T hℓN)⁻¹ = barElt T hℓN := inv_eq_of_mul_eq_one_right hlbsq
  have : Fintype (NQuot T) := Fintype.ofFinite _
  obtain ⟨O, hOn, hOodd, hOc⟩ := CFSG.ZStar.glauberman_zStar (NQuot T) (barElt T hℓN) hlb1 hlbsq
    (fun g hcomm => isolated_bar hc h48 hℓ hℓ1 hℓN g hcomm)
  have hOc' : ∀ g : NQuot T,
      (QuotientGroup.mk (g * barElt T hℓN * g⁻¹) : NQuot T ⧸ O) =
        QuotientGroup.mk (barElt T hℓN) := by
    intro g
    rw [QuotientGroup.eq]
    have h1 := hOc g
    rw [hlbinv] at h1
    have e : (g * barElt T hℓN * g⁻¹)⁻¹ * barElt T hℓN = g * barElt T hℓN * g⁻¹ * barElt T hℓN := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, hlbinv]
      group
    rw [e]
    exact h1
  refine ⟨O, hOn, hOodd, fun y hy => ?_⟩
  let φ' : ↥(Subgroup.normalizer (T : Set G)) →* NQuot T :=
    QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set G)))
  let φ : ↥(Subgroup.normalizer (T : Set G)) →* (NQuot T ⧸ O) := (QuotientGroup.mk' O).comp φ'
  have hφ : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (T : Set G)),
      φ ⟨x, hx⟩ = QuotientGroup.mk (barElt T hx) := fun x hx => rfl
  have hlsq : φ ⟨ℓ, hℓN⟩ * φ ⟨ℓ, hℓN⟩ = 1 := by
    rw [← map_mul]
    have : (⟨ℓ, hℓN⟩ * ⟨ℓ, hℓN⟩ : ↥(Subgroup.normalizer (T : Set G))) = 1 := Subtype.ext hℓℓ
    rw [this, map_one]
  have hHW : hSub T (normIn T₁ T) ≤ Subgroup.map (Subgroup.normalizer (T : Set G)).subtype
      ((Subgroup.zpowers (φ ⟨ℓ, hℓN⟩)).comap φ) := by
    refine sup_le (fun t ht => ?_) (iSup₂_le fun g hg y hy => ?_)
    · refine Subgroup.mem_map.2 ⟨⟨t, Subgroup.le_normalizer ht⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap, hφ t (Subgroup.le_normalizer ht), (barElt_eq_one_iff _).2 ht,
        QuotientGroup.mk_one]
      exact Subgroup.one_mem _
    · have hyN : y ∈ Subgroup.normalizer (T : Set G) := conjSubgroup_le_normalizer hg hL₁N hy
      refine Subgroup.mem_map.2 ⟨⟨y, hyN⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      have hy0 : g⁻¹ * y * g ∈ normIn T₁ T := mem_conjSubgroup.1 hy
      have hyg : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (T : Set G))) =
          ⟨g, hg⟩ * ⟨g⁻¹ * y * g, hL₁N hy0⟩ * ⟨g, hg⟩⁻¹ := Subtype.ext (by simp [mul_assoc])
      rw [hyg, map_mul, map_mul, map_inv]
      by_cases hy1 : g⁻¹ * y * g = 1
      · have : (⟨g⁻¹ * y * g, hL₁N hy0⟩ : ↥(Subgroup.normalizer (T : Set G))) = 1 :=
          Subtype.ext hy1
        rw [this, map_one, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · have heq : g⁻¹ * y * g = ℓ := eq_of_card_two (card_normIn_swap_two hc) hy0 hℓ hy1 hℓ1
        have : (⟨g⁻¹ * y * g, hL₁N hy0⟩ : ↥(Subgroup.normalizer (T : Set G))) = ⟨ℓ, hℓN⟩ :=
          Subtype.ext heq
        rw [this]
        have hcg : φ ⟨g, hg⟩ * φ ⟨ℓ, hℓN⟩ * (φ ⟨g, hg⟩)⁻¹ = φ ⟨ℓ, hℓN⟩ := by
          have := hOc' (φ' ⟨g, hg⟩)
          simpa [φ, φ', hφ, barElt] using this
        rw [hcg]
        exact Subgroup.mem_zpowers _
  obtain ⟨⟨z, hz⟩, hzW, rfl⟩ := Subgroup.mem_map.1 (hHW hy)
  refine ⟨hz, ?_⟩
  rw [Subgroup.mem_comap] at hzW
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hzW
  have hmk : φ ⟨z, hz⟩ = (φ ⟨ℓ, hℓN⟩) ^ k := hk.symm
  have hkk : (φ ⟨ℓ, hℓN⟩) ^ k = 1 ∨ (φ ⟨ℓ, hℓN⟩) ^ k = φ ⟨ℓ, hℓN⟩ := by
    have h2 : (φ ⟨ℓ, hℓN⟩) ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hlsq
    have : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [this, h, add_zero, zpow_mul, h2, one_zpow]
    · right
      rw [this, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  change (QuotientGroup.mk (barElt T (x := z) hz) : NQuot T ⧸ O) = 1 ∨
    (QuotientGroup.mk (barElt T (x := z) hz) : NQuot T ⧸ O) = QuotientGroup.mk (barElt T hℓN)
  rcases hkk with h | h
  · left
    rw [← hφ z hz, hmk, h]
  · right
    rw [← hφ z hz, hmk, h, hφ]

theorem card_le_eight_of_pGroup_le [Finite G] (hc : Sec6Ctx T T₁ 2 1)
    (h48 : IsWC (barSub T (normIn T₁ T))) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPH : P ≤ hSub T (normIn T₁ T)) : Nat.card P ≤ 8 := by
  classical
  have hS3 := hc.sec3
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  obtain ⟨ℓ, hℓ, hℓ1⟩ : ∃ ℓ ∈ normIn T₁ T, ℓ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hS3.cfg.ne₁ (eq_bot_iff.2 (fun y hy => Subgroup.mem_bot.2 (hcon y hy)))
  have hℓN : ℓ ∈ Subgroup.normalizer (T : Set G) := hL₁N hℓ
  have hℓℓ : ℓ * ℓ = 1 := elemAbelian_mul_self hS3.cfg.wc₁.1 (normIn_le _ _ hℓ)
  obtain ⟨O, hOn, hOodd, hH⟩ := exists_odd_normal_image hc h48 hℓ hℓ1 hℓN
  have := hOn
  have hPN : P ≤ Subgroup.normalizer (T : Set G) := hPH.trans (hSub_le_normalizer hL₁N)
  let φ' : ↥(Subgroup.normalizer (T : Set G)) →* NQuot T :=
    QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set G)))
  let ψ : ↥P →* (NQuot T ⧸ O) :=
    ((QuotientGroup.mk' O).comp φ').comp (Subgroup.inclusion hPN)
  have hψ : ∀ x : P, ψ x = QuotientGroup.mk (barElt T (hPN x.2)) := fun x => rfl
  have hT4 : Nat.card T = 4 := by simpa using hc.hT
  have hw2 : (QuotientGroup.mk (barElt T hℓN) : NQuot T ⧸ O) *
      QuotientGroup.mk (barElt T hℓN) = 1 := by
    have : barElt T hℓN * barElt T hℓN =
        barElt T ((Subgroup.normalizer (T : Set G)).mul_mem hℓN hℓN) := rfl
    rw [← QuotientGroup.mk_mul, this, (barElt_eq_one_iff _).2 (by rw [hℓℓ]; exact T.one_mem),
      QuotientGroup.mk_one]
  have hrange : Nat.card ψ.range ≤ 2 := by
    have hle : ψ.range ≤ Subgroup.zpowers (QuotientGroup.mk (barElt T hℓN) : NQuot T ⧸ O) := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨hy, h⟩ := hH x.1 (hPH x.2)
      rw [hψ]
      rcases h with h | h
      · rw [show barElt T (hPN x.2) = barElt T hy from rfl, h]
        exact Subgroup.one_mem _
      · rw [show barElt T (hPN x.2) = barElt T hy from rfl, h]
        exact Subgroup.mem_zpowers _
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2))
  have hker : Nat.card ψ.ker ≤ 4 := by
    have hmem : ∀ x : ψ.ker, (x.1 : G) ∈ T := by
      intro x
      have hx1 : ψ x.1 = 1 := x.2
      rw [hψ, QuotientGroup.eq_one_iff] at hx1
      obtain ⟨k, hk⟩ := hP x.1
      have hxN : (x.1 : G) ∈ Subgroup.normalizer (T : Set G) := hPN x.1.2
      have hpow : (barElt T hxN) ^ (2 ^ k) = 1 := by
        have h1 : (φ' ⟨x.1, hxN⟩) ^ (2 ^ k) = 1 := by
          rw [← map_pow]
          have : (⟨x.1, hxN⟩ : ↥(Subgroup.normalizer (T : Set G))) ^ (2 ^ k) = 1 :=
            Subtype.ext (by simpa using congrArg Subtype.val hk)
          rw [this, map_one]
        exact h1
      have hord : orderOf (⟨barElt T hxN, hx1⟩ : O) ∣ 2 ^ k := by
        apply orderOf_dvd_of_pow_eq_one
        exact Subtype.ext hpow
      have hord' : orderOf (⟨barElt T hxN, hx1⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
      have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hOodd)
      have h1 : orderOf (⟨barElt T hxN, hx1⟩ : O) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord hcop) hord'
      have h2 : (⟨barElt T hxN, hx1⟩ : O) = 1 := orderOf_eq_one_iff.1 h1
      exact (barElt_eq_one_iff hxN).1 (congrArg Subtype.val h2)
    let f : ψ.ker → ↥T := fun x => ⟨(x.1 : G), hmem x⟩
    have hf : Function.Injective f := fun x y h => by
      have h' : (x.1 : G) = (y.1 : G) := congrArg (fun z : ↥T => (z : G)) h
      exact Subtype.ext (Subtype.ext h')
    rw [← hT4]
    exact Nat.card_le_card_of_injective f hf
  calc Nat.card P = Nat.card ψ.ker * Nat.card ψ.range := (Subgroup.card_ker_mul_card_range ψ).symm
    _ ≤ 4 * 2 := Nat.mul_le_mul hker hrange
    _ = 8 := by norm_num

end ZStar

end CFSG.CGT.T75H
