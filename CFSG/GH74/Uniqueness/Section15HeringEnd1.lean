module

public import CFSG.GH74.Uniqueness.Section15HeringDefs
public import CFSG.GH74.Uniqueness.Section15HeringCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.GH74.Uniqueness.Hering

open Subgroup MulAction

theorem not_dvd_two_pow_sub_one {p : ℕ} (hp : p.Prime) : ¬ p ∣ 2 ^ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  intro h
  have h1 : ((2 ^ p - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, ZMod.pow_card,
    Nat.cast_one] at h1
  norm_num at h1

section Group

variable {G : Type*} [Group G]

theorem orderOf_conj' (c g : G) : orderOf (c⁻¹ * g * c) = orderOf g :=
  (SemiconjBy.orderOf_eq c⁻¹ (show c⁻¹ * g = (c⁻¹ * g * c) * c⁻¹ by group)).symm

theorem isPGroup_zpowers_of_orderOf {p : ℕ} [Fact p.Prime] {g : G} (hg : orderOf g = p) :
    IsPGroup p (zpowers g) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])

theorem inv_eq_self_of_orderOf_eq_two {z : G} (hz : orderOf z = 2) : z⁻¹ = z := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hz, pow_orderOf_eq_one]

theorem conj_zpow_inv {z x : G} (hzx : z * x * z⁻¹ = x⁻¹) (i : ℤ) :
    z * x ^ i * z⁻¹ = (x ^ i)⁻¹ := by
  rw [← conj_zpow, hzx, inv_zpow]

theorem exists_conj_mem_sylow [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G) {g : G}
    (hg : IsPGroup p (zpowers g)) : ∃ c : G, c⁻¹ * g * c ∈ (S : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hg.exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq G S Q
  refine ⟨c, ?_⟩
  have hgQ : g ∈ ((c • S : Sylow p G) : Subgroup G) := hQ (mem_zpowers g)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hgQ
  simpa [MulAut.conj_apply, mul_assoc] using hgQ

end Group

variable {G Ω : Type*} [Group G] [MulAction G Ω] {p : ℕ} {ω : Ω} {K P : Subgroup G}

theorem EndHyp.isPretransitive (h : EndHyp G Ω p ω K P) : IsPretransitive G Ω :=
  (isPreprimitive_of_is_two_pretransitive h.twoTrans).toIsPretransitive

theorem EndHyp.card_group [Finite G] (h : EndHyp G Ω p ω K P) :
    Nat.card G = 2 ^ p * ((2 ^ p - 1) * p) := by
  have := h.isPretransitive
  rw [← Subgroup.card_mul_index (stabilizer G ω), index_stabilizer, orbit_eq_univ,
    Set.ncard_univ, h.card, h.card_stab, mul_comm]

theorem EndHyp.card_stabilizer [Finite G] (h : EndHyp G Ω p ω K P) (x : Ω) :
    Nat.card (stabilizer G x) = (2 ^ p - 1) * p := by
  have := h.isPretransitive
  obtain ⟨g, rfl⟩ := exists_smul_eq G ω x
  rw [stabilizer_smul_eq_stabilizer_map_conj, Subgroup.card_map_of_injective
    (MulAut.conj g).injective, h.card_stab]

theorem EndHyp.odd_card_stab (h : EndHyp G Ω p ω K P) : Odd ((2 ^ p - 1) * p) := by
  have h3 := h.three_le
  refine Nat.odd_mul.mpr ⟨?_, h.prime.odd_of_ne_two (by omega)⟩
  have : Even (2 ^ p) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  rcases this with ⟨c, hc⟩
  exact ⟨c - 1, by omega⟩

theorem EndHyp.smul_ne_of_orderOf_eq_two [Finite G] (h : EndHyp G Ω p ω K P) {t : G}
    (ht : orderOf t = 2) (x : Ω) : t • x ≠ x := by
  intro hx
  have hdvd : orderOf t ∣ Nat.card (stabilizer G x) := Subgroup.orderOf_dvd_natCard _ hx
  rw [ht, h.card_stabilizer x] at hdvd
  exact (Nat.not_even_iff_odd.mpr h.odd_card_stab) (even_iff_two_dvd.mpr hdvd)

theorem EndHyp.exists_conj_zpowers_eq [Finite G] (h : EndHyp G Ω p ω K P) {g : G}
    (hg : orderOf g = p) : ∃ c : G, zpowers (c⁻¹ * g * c) = P := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hPp : IsPGroup p P := IsPGroup.of_card (n := 1) (by rw [h.card_P, pow_one])
  have hidx : ¬ p ∣ P.index := by
    intro hdvd
    have hG := h.card_group
    rw [← Subgroup.card_mul_index P, h.card_P] at hG
    have : P.index = 2 ^ p * (2 ^ p - 1) := by
      apply Nat.eq_of_mul_eq_mul_left h.prime.pos
      rw [hG]
      ring
    rw [this] at hdvd
    rcases (Nat.Prime.dvd_mul h.prime).mp hdvd with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp (h.prime.dvd_of_dvd_pow h2)
      have := h.three_le
      omega
    · exact not_dvd_two_pow_sub_one h.prime h2
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow (hPp.toSylow hidx) (isPGroup_zpowers_of_orderOf hg)
  rw [IsPGroup.toSylow_coe] at hc
  refine ⟨c, (Subgroup.eq_of_le_of_card_ge ((zpowers_le (H := P)).mpr hc) ?_)⟩
  rw [Nat.card_zpowers, h.card_P, orderOf_conj', hg]

theorem EndHyp.exists_conj_mem_K [Finite G] (h : EndHyp G Ω p ω K P) {g : G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p) (hg : orderOf g = r) :
    ∃ c : G, c⁻¹ * g * c ∈ K := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r K))
  set Q' : Subgroup G := (Q : Subgroup K).map K.subtype with hQ'
  have hQ'p : IsPGroup r Q' := Q.isPGroup'.map K.subtype
  have hKidx : K.index = 2 ^ p * p := by
    have hG := h.card_group
    rw [← Subgroup.card_mul_index K, h.card_K] at hG
    have hpos : 0 < 2 ^ p - 1 := by
      have : 2 ≤ 2 ^ p := Nat.le_self_pow h.prime.ne_zero 2
      omega
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hG]
    ring
  have hidx : ¬ r ∣ Q'.index := by
    rw [hQ', Subgroup.index_map_subtype, hKidx]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hr).mp hdvd with h1 | h1
    · exact Q.not_dvd_index h1
    · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
      · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
      · exact hrp ((Nat.prime_dvd_prime_iff_eq hr h.prime).mp h2)
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow (hQ'p.toSylow hidx) (isPGroup_zpowers_of_orderOf hg)
  rw [IsPGroup.toSylow_coe, hQ'] at hc
  exact ⟨c, Subgroup.map_subtype_le _ hc⟩

theorem EndHyp.mul_ne_of_orderOf_eq_two [Finite G] (h : EndHyp G Ω p ω K P) {t g : G}
    (ht : orderOf t = 2) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hg : orderOf g = r) :
    t * g ≠ g * t := by
  intro htg
  have hconj : ∀ c : G, c⁻¹ * g * c * (c⁻¹ * t * c) = c⁻¹ * t * c * (c⁻¹ * g * c) := by
    intro c
    calc c⁻¹ * g * c * (c⁻¹ * t * c) = c⁻¹ * (g * t) * c := by group
      _ = c⁻¹ * (t * g) * c := by rw [htg]
      _ = c⁻¹ * t * c * (c⁻¹ * g * c) := by group
  by_cases hrp : r = p
  · subst hrp
    obtain ⟨c, hc⟩ := h.exists_conj_zpowers_eq hg
    have ht' : c⁻¹ * t * c ∈ centralizer (P : Set G) := by
      rw [← hc, mem_centralizer_iff]
      rintro y ⟨i, rfl⟩
      exact ((Commute.zpow_left (hconj c) i)).eq
    have hdvd := Subgroup.orderOf_dvd_natCard P (h.centralizer_le ht')
    rw [orderOf_conj', ht, h.card_P] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp hdvd).symm
  · obtain ⟨c, hc⟩ := h.exists_conj_mem_K hr hr2 hrp hg
    have hc1 : c⁻¹ * g * c ≠ 1 := by
      intro h1
      rw [← orderOf_conj' c g, h1, orderOf_one] at hg
      exact hr.one_lt.ne hg
    have hfix : (c⁻¹ * g * c) • ((c⁻¹ * t * c) • ω) = (c⁻¹ * t * c) • ω := by
      rw [smul_smul, hconj c, mul_smul, (h.K_le hc : (c⁻¹ * g * c) • ω = ω)]
    have := h.K_fix _ hc hc1 _ hfix
    exact h.smul_ne_of_orderOf_eq_two (by rw [orderOf_conj', ht]) ω this

theorem EndHyp.isConj_of_mem_normalizer [Finite G] (h : EndHyp G Ω p ω K P)
    {s t : normalizer (P : Set G)} (hs : orderOf s = 2) (ht : orderOf t = 2) : IsConj s t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ x : normalizer (P : Set G), orderOf x = 2 → ¬ 2 ∣ (zpowers x).index := by
    intro x hx hdvd
    have h1 := (zpowers x).card_mul_index
    rw [Nat.card_zpowers, hx, h.card_normalizer] at h1
    have h2 : (zpowers x).index = p := by omega
    rw [h2] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).mp hdvd
    have := h.three_le
    omega
  let S₁ := (isPGroup_zpowers_of_orderOf hs).toSylow (hidx s hs)
  let S₂ := (isPGroup_zpowers_of_orderOf ht).toSylow (hidx t ht)
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (normalizer (P : Set G)) S₁ S₂
  have hmem : n * s * n⁻¹ ∈ zpowers t := by
    have h1 : s ∈ (S₁ : Subgroup _) := by
      rw [IsPGroup.toSylow_coe]
      exact mem_zpowers s
    have h2 : n * s * n⁻¹ ∈ ((n • S₁ : Sylow 2 _) : Subgroup _) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨s, h1, by simp [MulAut.conj_apply]⟩
    rw [hn, IsPGroup.toSylow_coe] at h2
    exact h2
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hmem
  have hcases : t ^ i = 1 ∨ t ^ i = t := by
    rw [← zpow_mod_orderOf, ht]
    rcases Int.emod_two_eq_zero_or_one i with h0 | h1
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]
  refine isConj_iff.mpr ⟨n, ?_⟩
  rcases hcases with h0 | h1
  · exfalso
    rw [h0] at hi
    have : s = 1 := by
      have := congrArg (fun y => n⁻¹ * y * n) hi
      simpa [mul_assoc] using this.symm
    rw [this, orderOf_one] at hs
    omega
  · rw [← hi, h1]

theorem EndHyp.isConj_of_orderOf_eq_two [Finite G] (h : EndHyp G Ω p ω K P) {t u : G}
    (ht : orderOf t = 2) (hu : orderOf u = 2) : IsConj t u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (P : Set G)) 2
    (by rw [h.card_normalizer]; exact dvd_mul_right 2 p)
  suffices key : ∀ z : G, orderOf z = 2 → IsConj z (t₀ : G) from
    (key t ht).trans (key u hu).symm
  intro z hz
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  have hzinv := inv_eq_self_of_orderOf_eq_two hz
  have hzz : z * z = 1 := by
    have := inv_mul_cancel z
    rwa [hzinv] at this
  have hpc : CFSG.pCore 2 G = ⊥ := by
    apply h.solvable _ CFSG.pCore_normal
    have := (CFSG.pCore_isPGroup (p := 2) (G := G)).isNilpotent
    infer_instance
  have hnot : ¬ ∀ g : G, IsPGroup 2 (Subgroup.closure ({z, g * z * g⁻¹} : Set G)) := by
    intro hall
    have hmem := CFSG.BaerSuzuki.baer_suzuki z (isPGroup_zpowers_of_orderOf hz) hall
    rw [hpc, mem_bot] at hmem
    exact hz1 hmem
  push Not at hnot
  obtain ⟨g, hg⟩ := hnot
  set v := g * z * g⁻¹ with hv
  have hvinv : v⁻¹ = v := by
    apply inv_eq_self_of_orderOf_eq_two
    rw [hv, show g * z * g⁻¹ = g⁻¹⁻¹ * z * g⁻¹ by group, orderOf_conj', hz]
  set w := z * v with hw
  have hzw : z * w * z⁻¹ = w⁻¹ := by
    calc z * w * z⁻¹ = (z * z) * v * z⁻¹ := by rw [hw]; group
      _ = v * z⁻¹ := by rw [hzz, one_mul]
      _ = w⁻¹ := by rw [hw, mul_inv_rev, hvinv]
  have hw2 : ¬ IsPGroup 2 (zpowers w) := by
    intro hw2
    apply hg
    have hnorm : zpowers z ≤ normalizer ((zpowers w : Subgroup G) : Set G) := by
      rw [zpowers_le]
      apply mem_normalizer_of_conj_mem
      rintro x ⟨i, rfl⟩
      exact ⟨-i, by simp only; rw [conj_zpow_inv hzw, zpow_neg]⟩
    have hsup := IsPGroup.to_sup_of_normal_left' hw2 (isPGroup_zpowers_of_orderOf hz) hnorm
    apply hsup.to_le
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact mem_sup_right (mem_zpowers _)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, show v = z⁻¹ * w by rw [hw]; group]
      exact mul_mem (mem_sup_right (inv_mem (mem_zpowers _))) (mem_sup_left (mem_zpowers _))
  obtain ⟨r, hr, hr2, hrw⟩ : ∃ r, r.Prime ∧ r ≠ 2 ∧ r ∣ orderOf w := by
    by_contra hcon
    push Not at hcon
    apply hw2
    have h0 : orderOf w ≠ 0 := (orderOf_pos w).ne'
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd h0 (fun {d} hd hdvd =>
      by_contra fun hne => hcon d hd hne hdvd)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers]; exact hpow)
  set x := w ^ (orderOf w / r) with hx
  have hxr : orderOf x = r := orderOf_pow_orderOf_div (orderOf_pos w).ne' hrw
  have hzx : z * x * z⁻¹ = x⁻¹ := by
    have := conj_zpow_inv hzw ((orderOf w / r : ℕ) : ℤ)
    rw [zpow_natCast] at this
    exact this
  by_cases hrp : r = p
  · subst hrp
    obtain ⟨c, hc⟩ := h.exists_conj_zpowers_eq hxr
    have hconj : (c⁻¹ * z * c) * (c⁻¹ * x * c) * (c⁻¹ * z * c)⁻¹ = (c⁻¹ * x * c)⁻¹ := by
      calc (c⁻¹ * z * c) * (c⁻¹ * x * c) * (c⁻¹ * z * c)⁻¹ = c⁻¹ * (z * x * z⁻¹) * c := by
            group
        _ = (c⁻¹ * x * c)⁻¹ := by rw [hzx]; group
    have hz'N : c⁻¹ * z * c ∈ normalizer (P : Set G) := by
      apply mem_normalizer_of_conj_mem
      rw [← hc]
      rintro y ⟨i, rfl⟩
      refine ⟨-i, ?_⟩
      simp only
      rw [zpow_neg, ← conj_zpow, hconj, inv_zpow]
    have hz'2 : orderOf (⟨c⁻¹ * z * c, hz'N⟩ : normalizer (P : Set G)) = 2 := by
      rw [Subgroup.orderOf_mk, orderOf_conj', hz]
    have h1 := (normalizer (P : Set G)).subtype.map_isConj
      (h.isConj_of_mem_normalizer hz'2 ht₀)
    exact (isConj_iff.mpr ⟨c⁻¹, by group⟩ : IsConj z (c⁻¹ * z * c)).trans h1
  · exfalso
    obtain ⟨c, hc⟩ := h.exists_conj_mem_K hr hr2 hrp hxr
    have hx'1 : c⁻¹ * x * c ≠ 1 := by
      intro h1
      rw [← orderOf_conj' c x, h1, orderOf_one] at hxr
      exact hr.one_lt.ne hxr
    have hfix : (c⁻¹ * x * c)⁻¹ • ((c⁻¹ * z * c) • ω) = (c⁻¹ * z * c) • ω := by
      rw [smul_smul, show (c⁻¹ * x * c)⁻¹ * (c⁻¹ * z * c) = (c⁻¹ * z * c) * (c⁻¹ * x * c) by
        calc (c⁻¹ * x * c)⁻¹ * (c⁻¹ * z * c) = c⁻¹ * (x⁻¹ * z) * c := by group
          _ = c⁻¹ * (z * x * z⁻¹ * z) * c := by rw [hzx]
          _ = (c⁻¹ * z * c) * (c⁻¹ * x * c) := by group, mul_smul,
        (h.K_le hc : (c⁻¹ * x * c) • ω = ω)]
    have := h.K_fix _ (K.inv_mem hc) (inv_ne_one.mpr hx'1) _ hfix
    exact h.smul_ne_of_orderOf_eq_two (by rw [orderOf_conj', hz]) ω this

end CFSG.GH74.Uniqueness.Hering
