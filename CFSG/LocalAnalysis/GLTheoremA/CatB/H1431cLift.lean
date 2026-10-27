module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cFacts
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Rank
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open CFSG.HardMathSupport.Solomon.Coordinator (c25Pre c25Pre_le mem_c25Pre c25_mem_normalizer_pre c25_card_pre
  c25_isElemAbelian_sup_zpowers c25_isPGroup_of_elemAbelian fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY rank_le_twoLocal_of_normalizes_pre)
open CFSG.LocalAnalysis.GLTheoremA (pQuotHom ker_pQuotHom chev_barAut_eq_one_iff_centMod
  chev_coe_normalizerMonoidHom card_sup_mul_card_inf_of_le_normalizer isElemAbelian_commute
  exists_card_eq_pow_of_isElemAbelian)

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_zpowers_normal {c e x : G} (hce : Commute c e)
    (hx : x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers e) : ∃ i j : ℤ, x = c ^ i * e ^ j := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ⟨k, 0, by simp⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ⟨0, k, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    have h1 : e ^ j * c ^ k = c ^ k * e ^ j := (hce.symm.zpow_zpow j k).eq
    refine ⟨i + k, j + l, ?_⟩
    rw [zpow_add, zpow_add]
    calc c ^ i * e ^ j * (c ^ k * e ^ l) = c ^ i * (e ^ j * c ^ k) * e ^ l := by group
      _ = c ^ i * (c ^ k * e ^ j) * e ^ l := by rw [h1]
      _ = c ^ i * c ^ k * (e ^ j * e ^ l) := by group
  | inv x hx hx' =>
    obtain ⟨i, j, rfl⟩ := hx'
    refine ⟨-i, -j, ?_⟩
    have h1 : e ^ (-j) * c ^ (-i) = c ^ (-i) * e ^ (-j) := (hce.symm.zpow_zpow (-j) (-i)).eq
    calc (c ^ i * e ^ j)⁻¹ = e ^ (-j) * c ^ (-i) := by
          rw [mul_inv_rev, zpow_neg, zpow_neg]
      _ = c ^ (-i) * e ^ (-j) := h1

theorem barAut_eq_conj_pi {K : Subgroup G} {x : G} (hx : x ∈ K)
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) :
    barAut 3 K ⟨x, hxN⟩ = MulAut.conj (pQuotHom 3 K ⟨x, hx⟩) := by
  ext y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
  rw [barAut_mk, MulAut.conj_apply]
  change QuotientGroup.mk (K.normalizerMonoidHom ⟨x, hxN⟩ z) =
    QuotientGroup.mk (⟨x, hx⟩ : ↥K) * QuotientGroup.mk z * (QuotientGroup.mk (⟨x, hx⟩ : ↥K))⁻¹
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1

theorem normalizer_c25Pre_of_fix {K : Subgroup G} {X : Subgroup (PQuot 3 K)} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hfix : ∀ u ∈ X, barAut 3 K ⟨g, hg⟩ u = u) :
    g ∈ Subgroup.normalizer (c25Pre K X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨hhK, hhX⟩ := mem_c25Pre.1 hh
    have hgh : g * h * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hg h).1 hhK
    refine mem_c25Pre.2 ⟨hgh, ?_⟩
    have h1 : barAut 3 K ⟨g, hg⟩ (QuotientGroup.mk (⟨h, hhK⟩ : ↥K)) =
        QuotientGroup.mk (⟨g * h * g⁻¹, hgh⟩ : ↥K) := by
      rw [barAut_mk]
      rfl
    rw [← h1, hfix _ hhX]
    exact hhX
  · intro hh
    obtain ⟨hghK, hX⟩ := mem_c25Pre.1 hh
    have hhK : h ∈ K := (Subgroup.mem_normalizer_iff.1 hg h).2 hghK
    refine mem_c25Pre.2 ⟨hhK, ?_⟩
    have h1 : barAut 3 K ⟨g, hg⟩ (QuotientGroup.mk (⟨h, hhK⟩ : ↥K)) =
        QuotientGroup.mk (⟨g * h * g⁻¹, hghK⟩ : ↥K) := by
      rw [barAut_mk]
      rfl
    have h2 : barAut 3 K ⟨g, hg⟩ (QuotientGroup.mk (⟨h, hhK⟩ : ↥K)) =
        barAut 3 K ⟨g, hg⟩ (QuotientGroup.mk (⟨g * h * g⁻¹, hghK⟩ : ↥K)) := by
      rw [h1, hfix _ hX]
    exact (barAut 3 K ⟨g, hg⟩).injective h2 ▸ hX


theorem pQuotHom_conj {K : Subgroup G} {g s : G} (hgN : g ∈ Subgroup.normalizer (K : Set G))
    (hsK : s ∈ K) (hgs : g * s * g⁻¹ ∈ K) :
    pQuotHom 3 K ⟨g * s * g⁻¹, hgs⟩ = barAut 3 K ⟨g, hgN⟩ (pQuotHom 3 K ⟨s, hsK⟩) := by
  change QuotientGroup.mk (⟨g * s * g⁻¹, hgs⟩ : ↥K) =
    barAut 3 K ⟨g, hgN⟩ (QuotientGroup.mk (⟨s, hsK⟩ : ↥K))
  rw [barAut_mk]
  rfl

theorem eq_one_of_pi_eq_one {K : Subgroup G} {s : G} (hsK : s ∈ K) (hs3 : ∃ k : ℕ, s ^ 3 ^ k = 1)
    (hπ : pQuotHom 3 K ⟨s, hsK⟩ = 1) : s = 1 := by
  have hO : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  obtain ⟨k, hk⟩ := hs3
  have hdvd : orderOf s ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hker : (⟨s, hsK⟩ : ↥K) ∈ (pQuotHom 3 K).ker := hπ
  rw [ker_pQuotHom] at hker
  have hle : Subgroup.zpowers (⟨s, hsK⟩ : ↥K) ≤ GLAPPrimeCore 3 ↥K :=
    Subgroup.zpowers_le.2 hker
  have hd : orderOf (⟨s, hsK⟩ : ↥K) ∣ Nat.card (GLAPPrimeCore 3 ↥K) := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have hord : orderOf (⟨s, hsK⟩ : ↥K) = orderOf s := Subgroup.orderOf_mk s hsK
  rw [hord, hm] at hd
  have hm0 : m = 0 := by
    by_contra hm0
    have h3 : 3 ∣ 3 ^ m := dvd_pow_self 3 hm0
    have h3' : 3 ∣ Nat.card (GLAPPrimeCore 3 ↥K) := h3.trans hd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hO h3'
  subst hm0
  rw [pow_zero, orderOf_eq_one_iff] at hm
  exact hm

theorem isElemAbelian_zpowers_of_pow_eq_one {e : G} (he3 : e ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers e) := by
  refine ⟨inferInstance, fun x hx => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [he3]

theorem isElemAbelian_zpowers_sup {c e : G} (hc3 : c ^ 3 = 1) (he3 : e ^ 3 = 1) (hce : Commute c e) :
    IsElemAbelian 3 (Subgroup.zpowers c ⊔ Subgroup.zpowers e) := by
  refine c25_isElemAbelian_sup_zpowers ?_ hc3 ?_
  · exact isElemAbelian_zpowers_of_pow_eq_one he3
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((hce.zpow_right k).eq).symm


theorem normalizer_zpowers_of_commute {c e : G} (hce : Commute c e) :
    e ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  have hx : ∀ y ∈ Subgroup.zpowers c, e * y * e⁻¹ = y := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [(hce.symm.zpow_right k).eq]
    group
  intro x
  constructor
  · intro hxc
    rw [hx x hxc]
    exact hxc
  · intro hxc
    have h1 : e * (e * x * e⁻¹) * e⁻¹ = e * x * e⁻¹ := hx _ hxc
    have h2 : x = e * x * e⁻¹ := by
      calc x = e⁻¹ * (e * x * e⁻¹) * e := by group
        _ = e⁻¹ * (e * (e * x * e⁻¹) * e⁻¹) * e := by rw [h1]
        _ = e * x * e⁻¹ := by group
    rw [h2]
    exact hxc


theorem factorization_three_pow_mul {k n : ℕ} (hn : Nat.Coprime 3 n) (hn0 : n ≠ 0) :
    (3 ^ k * n).factorization 3 = k := by
  have h1 : (3 ^ k).factorization 3 = k := by
    rw [Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have h2 : n.factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hn)
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hn0, Finsupp.add_apply, h1, h2, add_zero]

theorem exists_lift_pair {K : Subgroup G} {c e : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) (heN : e ∈ Subgroup.normalizer (K : Set G))
    (hc3 : c ^ 3 = 1) (he3 : e ^ 3 = 1) (hce : Commute c e) (hc1 : c ≠ 1) (he1 : e ≠ 1)
    (hcK : CentMod 3 K c)
    {E : Subgroup (PQuot 3 K)} (hE : IsElemAbelian 3 E)
    (hEfix : ∀ x ∈ E, barAut 3 K ⟨e, heN⟩ x = x)
    (hcap : Subgroup.zpowers c ⊓ Subgroup.zpowers e = ⊥)
    (hHE : (Subgroup.zpowers c ⊔ Subgroup.zpowers e) ⊓ c25Pre K E = ⊥) :
    ∃ S : Subgroup G, S ≤ c25Pre K E ∧ IsElemAbelian 3 S ∧ Nat.card ↥S = Nat.card ↥E ∧
      ∀ s ∈ S, c * s = s * c ∧ e * s = s * e := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hE
  have hO : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  have hO0 : Nat.card (GLAPPrimeCore 3 ↥K) ≠ 0 := Nat.card_pos.ne'
  have hcbar : barAut 3 K ⟨c, hcN⟩ = 1 := (chev_barAut_eq_one_iff_centMod hcN).2 hcK
  have hÊK : c25Pre K E ≤ K := c25Pre_le E
  have hcÊ : c ∈ Subgroup.normalizer (c25Pre K E : Set G) :=
    normalizer_c25Pre_of_fix hcN (fun x _ => by rw [hcbar, MulAut.one_apply])
  have heÊ : e ∈ Subgroup.normalizer (c25Pre K E : Set G) := normalizer_c25Pre_of_fix heN hEfix
  have hHN : Subgroup.zpowers c ⊔ Subgroup.zpowers e ≤ Subgroup.normalizer (c25Pre K E : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hcÊ) (Subgroup.zpowers_le.2 heÊ)
  have hHel : IsElemAbelian 3 (Subgroup.zpowers c ⊔ Subgroup.zpowers e) :=
    isElemAbelian_zpowers_sup hc3 he3 hce
  have hcardc : Nat.card ↥(Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hcarde : Nat.card ↥(Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime he3 he1]
  have hHcard : Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers e) = 9 := by
    have h := card_sup_mul_card_inf_of_le_normalizer
      (A := Subgroup.zpowers c) (B := Subgroup.zpowers e)
      (Subgroup.zpowers_le.2 (normalizer_zpowers_of_commute hce))
    rw [hcap, Subgroup.card_bot, hcardc, hcarde] at h
    omega
  have hÊcard : Nat.card ↥(c25Pre K E) = Nat.card (GLAPPrimeCore 3 ↥K) * 3 ^ k := by
    rw [c25_card_pre, hk]
  have hÊH : c25Pre K E ⊓ (Subgroup.zpowers c ⊔ Subgroup.zpowers e) = ⊥ := by
    rw [inf_comm]
    exact hHE
  have hcardM : Nat.card ↥(c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)) =
      9 * Nat.card ↥(c25Pre K E) := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := c25Pre K E)
      (B := Subgroup.zpowers c ⊔ Subgroup.zpowers e) hHN
    rw [hÊH, Subgroup.card_bot, hHcard] at h
    omega
  have hH3M : IsPGroup 3 ((Subgroup.zpowers c ⊔ Subgroup.zpowers e).subgroupOf
      (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e))) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hg : ((g : ↥(c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e))) : G) ∈
        Subgroup.zpowers c ⊔ Subgroup.zpowers e := Subgroup.mem_subgroupOf.1 g.2
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hHel.2 _ hg
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hH3M
  have hMcard3 : Nat.card ↥(c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)) =
      3 ^ (k + 2) * Nat.card (GLAPPrimeCore 3 ↥K) := by
    rw [hcardM, hÊcard]
    ring
  have hHM : Subgroup.zpowers c ⊔ Subgroup.zpowers e ≤
      c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e) := le_sup_right
  have hMN : c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e) ≤
      Subgroup.normalizer (c25Pre K E : Set G) := sup_le Subgroup.le_normalizer hHN
  have hQ'M : Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype ≤
      c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hHQ' : Subgroup.zpowers c ⊔ Subgroup.zpowers e ≤
      Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype := by
    intro h hh
    have hhM : h ∈ c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e) := hHM hh
    have hmem : (⟨h, hhM⟩ : ↥(c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e))) ∈
        Q.toSubgroup := hQ (Subgroup.mem_subgroupOf.2 hh)
    exact ⟨⟨h, hhM⟩, hmem, rfl⟩
  have hQ'card : Nat.card ↥(Q.toSubgroup.map
      (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype) = 3 ^ (k + 2) := by
    rw [Subgroup.card_map_of_injective (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype_injective,
      Sylow.card_eq_multiplicity Q, hMcard3, factorization_three_pow_mul hO hO0]
  have hÊQsup : c25Pre K E ⊔ Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype =
      c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e) :=
    le_antisymm (sup_le le_sup_left hQ'M) (sup_le le_sup_left (hHQ'.trans le_sup_right))
  obtain ⟨S, hS⟩ : ∃ S : Subgroup G, S = c25Pre K E ⊓
      Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype := ⟨_, rfl⟩
  have hSÊ : S ≤ c25Pre K E := by
    rw [hS]
    exact inf_le_left
  have hSQ' : S ≤ Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype := by
    rw [hS]
    exact inf_le_right
  have hSK : S ≤ K := hSÊ.trans hÊK
  have hScard : Nat.card ↥S = Nat.card ↥E := by
    have h := card_sup_mul_card_inf_of_le_normalizer (A := c25Pre K E)
      (B := Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype)
      (hQ'M.trans hMN)
    have h3 : (3 : ℕ) ^ (k + 2) = 9 * Nat.card ↥E := by
      rw [hk]
      ring
    rw [hÊQsup, hcardM, hQ'card, h3, ← hS] at h
    have hpos : 0 < 9 * Nat.card ↥(c25Pre K E) := by
      have := Nat.card_pos (α := ↥(c25Pre K E))
      omega
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h]
    ring
  have hS3 : ∀ s ∈ S, ∃ j : ℕ, s ^ 3 ^ j = 1 := by
    intro s hs
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 (hSQ' hs)
    obtain ⟨j, hj⟩ := Q.isPGroup' ⟨y, hy⟩
    refine ⟨j, ?_⟩
    have h1 : y ^ 3 ^ j = 1 := by
      have h2 := congrArg Subtype.val hj
      simpa using h2
    rw [← map_pow, h1, map_one]
  have hπE : ∀ s (hs : s ∈ S), pQuotHom 3 K ⟨s, hSK hs⟩ ∈ E := fun s hs =>
    (mem_c25Pre.1 (hSÊ hs)).2
  have hmul : ∀ {s t : G} (hs : s ∈ S) (ht : t ∈ S),
      pQuotHom 3 K ⟨s * t, hSK (S.mul_mem hs ht)⟩ =
        pQuotHom 3 K ⟨s, hSK hs⟩ * pQuotHom 3 K ⟨t, hSK ht⟩ :=
    fun hs ht => by
      rw [← map_mul]
      rfl
  have hinj : ∀ {s t : G} (hs : s ∈ S) (ht : t ∈ S),
      pQuotHom 3 K ⟨s, hSK hs⟩ = pQuotHom 3 K ⟨t, hSK ht⟩ → s = t := by
    intro s t hs ht hst
    have hu : s * t⁻¹ ∈ S := S.mul_mem hs (S.inv_mem ht)
    have hπ : pQuotHom 3 K ⟨s * t⁻¹, hSK hu⟩ = 1 := by
      have e1 : (⟨s * t⁻¹, hSK hu⟩ : ↥K) = ⟨s, hSK hs⟩ * (⟨t, hSK ht⟩ : ↥K)⁻¹ :=
        Subtype.ext (by simp)
      rw [e1, map_mul, map_inv, hst, mul_inv_cancel]
    exact mul_inv_eq_one.1 (eq_one_of_pi_eq_one (hSK hu) (hS3 _ hu) hπ)
  have hSel : IsElemAbelian 3 S := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj (S.mul_mem a.2 b.2) (S.mul_mem b.2 a.2)
      rw [hmul a.2 b.2, hmul b.2 a.2]
      exact isElemAbelian_commute hE (hπE _ a.2) (hπE _ b.2)
    · have hx3 : pQuotHom 3 K ⟨x ^ 3, hSK (S.pow_mem hx 3)⟩ = 1 := by
        have e2 : (⟨x ^ 3, hSK (S.pow_mem hx 3)⟩ : ↥K) = ⟨x, hSK hx⟩ ^ 3 := Subtype.ext (by simp)
        rw [e2, map_pow]
        exact hE.2 _ (hπE x hx)
      exact hinj (S.pow_mem hx 3) S.one_mem (hx3.trans (map_one _).symm)
  have hcomm : ∀ s (hs : s ∈ S), c * s * c⁻¹ = s := by
    intro s hs
    have hcH : c ∈ Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype :=
      hHQ' (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
    have hcs : c * s * c⁻¹ ∈ S := by
      rw [hS]
      exact ⟨(Subgroup.mem_normalizer_iff.1 hcÊ s).1 (hSÊ hs),
        (Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype).mul_mem
          ((Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype).mul_mem hcH
            (hSQ' hs))
          ((Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype).inv_mem hcH)⟩
    apply hinj hcs hs
    rw [pQuotHom_conj hcN (hSK hs) (hSK hcs), hcbar, MulAut.one_apply]
  have hecomm : ∀ s (hs : s ∈ S), e * s * e⁻¹ = s := by
    intro s hs
    have heH : e ∈ Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype :=
      hHQ' (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
    have hes : e * s * e⁻¹ ∈ S := by
      rw [hS]
      exact ⟨(Subgroup.mem_normalizer_iff.1 heÊ s).1 (hSÊ hs),
        (Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype).mul_mem
          ((Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype).mul_mem heH
            (hSQ' hs))
          ((Q.toSubgroup.map (c25Pre K E ⊔ (Subgroup.zpowers c ⊔ Subgroup.zpowers e)).subtype).inv_mem heH)⟩
    apply hinj hes hs
    rw [pQuotHom_conj heN (hSK hs) (hSK hes), hEfix _ (hπE s hs)]
  exact ⟨S, hSÊ, hSel, hScard, fun s hs =>
    ⟨mul_inv_eq_iff_eq_mul.1 (hcomm s hs), mul_inv_eq_iff_eq_mul.1 (hecomm s hs)⟩⟩

theorem normalizer_of_commute_subgroup {H : Subgroup G} {s : G} (h : ∀ x ∈ H, Commute s x) :
    s ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : s * x * s⁻¹ = x := by
      rw [(h x hx).eq]
      group
    rw [h1]
    exact hx
  · intro hy
    have h1 : s * (s * x * s⁻¹) = (s * x * s⁻¹) * s := (h _ hy).eq
    have h3 : s⁻¹ * (s * x * s⁻¹) * s = s * x * s⁻¹ := by
      calc s⁻¹ * (s * x * s⁻¹) * s = s⁻¹ * ((s * x * s⁻¹) * s) := by group
        _ = s⁻¹ * (s * (s * x * s⁻¹)) := by rw [h1]
        _ = s * x * s⁻¹ := by group
    have h4 : x = s * x * s⁻¹ := by
      calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
        _ = s * x * s⁻¹ := h3
    have hy' := hy
    rw [← h4] at hy'
    exact hy'

theorem barAut_zpow_mul {K : Subgroup G} {c e : G} (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (heN : e ∈ Subgroup.normalizer (K : Set G)) {i j : ℤ}
    {g : ↥(Subgroup.normalizer (K : Set G))} (hg : (g : G) = c ^ i * e ^ j) :
    barAut 3 K g = (barAut 3 K ⟨c, hcN⟩) ^ i * (barAut 3 K ⟨e, heN⟩) ^ j := by
  have hg' : g = (⟨c, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ i *
      (⟨e, heN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ j :=
    Subtype.ext (by simp [hg])
  rw [hg', map_mul, map_zpow, map_zpow]

theorem zpowers_sup_inf_c25Pre_eq_bot {K : Subgroup G} {c e : G} {E : Subgroup (PQuot 3 K)}
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) (heN : e ∈ Subgroup.normalizer (K : Set G))
    (hc3 : c ^ 3 = 1) (he3 : e ^ 3 = 1) (hce : Commute c e) (he1 : e ≠ 1)
    (hcbar : barAut 3 K ⟨c, hcN⟩ = 1) (hE : IsElemAbelian 3 E)
    (hEZ : E ⊓ Subgroup.center (PQuot 3 K) = ⊥)
    (hpow : ∀ a ∈ E, barAut 3 K ⟨e, heN⟩ ≠ MulAut.conj a) :
    (Subgroup.zpowers c ⊔ Subgroup.zpowers e) ⊓ c25Pre K E = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHel : IsElemAbelian 3 (Subgroup.zpowers c ⊔ Subgroup.zpowers e) :=
    isElemAbelian_zpowers_sup hc3 he3 hce
  have hτ3 : (barAut 3 K ⟨e, heN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨e, heN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using he3)
    rw [h1, map_one]
  have hτ1 : barAut 3 K ⟨e, heN⟩ ≠ 1 := fun h => hpow 1 E.one_mem (by rw [map_one]; exact h)
  have hτord : orderOf (barAut 3 K ⟨e, heN⟩) = 3 := orderOf_eq_prime hτ3 hτ1
  have hτpow : ∀ j : ℤ, (barAut 3 K ⟨e, heN⟩) ^ j = (barAut 3 K ⟨e, heN⟩) ^ (j % 3) := by
    intro j
    have h := zpow_mod_orderOf (barAut 3 K ⟨e, heN⟩) j
    rw [hτord] at h
    exact h.symm
  rw [eq_bot_iff]
  rintro x ⟨hxH, hxÊ⟩
  rw [Subgroup.mem_bot]
  obtain ⟨i, j, rfl⟩ := mem_sup_zpowers_normal hce hxH
  have hyK : c ^ i * e ^ j ∈ K := c25Pre_le E hxÊ
  have hyN : (⟨c ^ i * e ^ j, Subgroup.le_normalizer hyK⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨c ^ i * e ^ j, Subgroup.le_normalizer hyK⟩ := rfl
  obtain ⟨p, hp⟩ : ∃ p : PQuot 3 K, p = pQuotHom 3 K ⟨c ^ i * e ^ j, hyK⟩ := ⟨_, rfl⟩
  have hpE : p ∈ E := by
    rw [hp]
    exact (mem_c25Pre.1 hxÊ).2
  have hconj : MulAut.conj p = (barAut 3 K ⟨e, heN⟩) ^ j := by
    rw [hp, ← barAut_eq_conj_pi hyK (Subgroup.le_normalizer hyK)]
    rw [barAut_zpow_mul hcN heN (g := ⟨c ^ i * e ^ j, Subgroup.le_normalizer hyK⟩) rfl, hcbar,
      one_zpow, one_mul]
  have hs3 : ∃ k : ℕ, (c ^ i * e ^ j) ^ 3 ^ k = 1 := ⟨1, by simpa using hHel.2 _ hxH⟩
  have hj3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hj3 with h0 | h1 | h2
  · have hτ0 : (barAut 3 K ⟨e, heN⟩) ^ j = 1 := by
      rw [hτpow, h0, zpow_zero]
    have hconj1 : MulAut.conj p = 1 := by rw [hconj, hτ0]
    have hcent : p ∈ Subgroup.center (PQuot 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have hw := congrArg (fun φ : MulAut (PQuot 3 K) => φ w) hconj1
      simp only [MulAut.conj_apply, MulAut.one_apply] at hw
      exact (mul_inv_eq_iff_eq_mul.1 hw).symm
    have hpz : p ∈ E ⊓ Subgroup.center (PQuot 3 K) := ⟨hpE, hcent⟩
    rw [hEZ, Subgroup.mem_bot] at hpz
    exact eq_one_of_pi_eq_one hyK hs3 (hp ▸ hpz)
  · have hτ1' : (barAut 3 K ⟨e, heN⟩) ^ j = barAut 3 K ⟨e, heN⟩ := by
      rw [hτpow, h1, zpow_one]
    exact (hpow p hpE (by rw [hconj, hτ1'])).elim
  · have hτ2' : (barAut 3 K ⟨e, heN⟩) ^ j = (barAut 3 K ⟨e, heN⟩) ^ 2 := by
      rw [hτpow, h2]
      norm_num
    have h4 : barAut 3 K ⟨e, heN⟩ = ((barAut 3 K ⟨e, heN⟩) ^ 2) ^ 2 := by
      calc barAut 3 K ⟨e, heN⟩ = (barAut 3 K ⟨e, heN⟩) ^ 3 * barAut 3 K ⟨e, heN⟩ := by
            rw [hτ3, one_mul]
        _ = ((barAut 3 K ⟨e, heN⟩) ^ 2) ^ 2 := by group
    have hc2 : MulAut.conj (p ^ 2) = barAut 3 K ⟨e, heN⟩ := by
      rw [map_pow, hconj, hτ2', ← h4]
    exact (hpow (p ^ 2) (E.pow_mem hpE 2) hc2.symm).elim

theorem rkTau_barAut {K B : Subgroup G} (hrk : GLATwoLocalRank 3 ↥(K ⊔ B) ≤ 4)
    (hB : IsElemAbelian 3 B) {c e : G} (hcB : c ∈ B) (hc1 : c ≠ 1) (hcK : CentMod 3 K c)
    (heB : e ∈ B) (heN : e ∈ Subgroup.normalizer (K : Set G)) :
    RkTau (barAut 3 K ⟨e, heN⟩) := by
  unfold RkTau
  intro U hU hU2 hUfix E hEfix hEN hE hEZ hpow
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hcK.1
  have hc3 : c ^ 3 = 1 := hB.2 c hcB
  have he3 : e ^ 3 = 1 := hB.2 e heB
  have hce : Commute c e := isElemAbelian_commute hB hcB heB
  have hcbar : barAut 3 K ⟨c, hcN⟩ = 1 := (chev_barAut_eq_one_iff_centMod hcN).2 hcK
  have hτ1 : barAut 3 K ⟨e, heN⟩ ≠ 1 := fun h => hpow 1 E.one_mem (by rw [map_one]; exact h)
  have he1 : e ≠ 1 := by
    rintro rfl
    apply hτ1
    have h1 : (⟨(1 : G), heN⟩ : ↥(Subgroup.normalizer (K : Set G))) = 1 := Subtype.ext rfl
    rw [h1, map_one]
  have hEfix' : ∀ x ∈ E, barAut 3 K ⟨e, heN⟩ x = x := fun x hx => mem_fixSubgroup.1 (hEfix hx)
  have hUfix' : ∀ u ∈ U, barAut 3 K ⟨e, heN⟩ u = u := fun u hu => mem_fixSubgroup.1 (hUfix hu)
  have hcardc : Nat.card ↥(Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hcarde : Nat.card ↥(Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime he3 he1]
  have hcap : Subgroup.zpowers c ⊓ Subgroup.zpowers e = ⊥ := by
    have hd : Nat.card ↥(Subgroup.zpowers c ⊓ Subgroup.zpowers e) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_right : Subgroup.zpowers c ⊓ Subgroup.zpowers e ≤ Subgroup.zpowers e)
      rwa [hcarde] at h
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : Subgroup.zpowers c ⊓ Subgroup.zpowers e = Subgroup.zpowers e :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      have hle : Subgroup.zpowers e ≤ Subgroup.zpowers c := by
        rw [← heq]
        exact inf_le_left
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hle (Subgroup.mem_zpowers e))
      apply hτ1
      have h2 : (⟨e, heN⟩ : ↥(Subgroup.normalizer (K : Set G))) = (⟨c, hcN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ k :=
        Subtype.ext (by simp [hk.symm])
      rw [h2, map_zpow, hcbar, one_zpow]
  have hHE : (Subgroup.zpowers c ⊔ Subgroup.zpowers e) ⊓ c25Pre K E = ⊥ :=
    zpowers_sup_inf_c25Pre_eq_bot hcN heN hc3 he3 hce he1 hcbar hE hEZ hpow
  obtain ⟨S, hSÊ, hSel, hScard, hcomm⟩ :=
    exists_lift_pair hcN heN hc3 he3 hce hc1 he1 hcK hE hEfix' hcap hHE
  have hSK : S ≤ K := hSÊ.trans (c25Pre_le E)
  have hHcard : Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers e) = 9 := by
    have h := card_sup_mul_card_inf_of_le_normalizer
      (A := Subgroup.zpowers c) (B := Subgroup.zpowers e)
      (Subgroup.zpowers_le.2 (normalizer_zpowers_of_commute hce))
    rw [hcap, Subgroup.card_bot, hcardc, hcarde] at h
    omega
  have hHS : (Subgroup.zpowers c ⊔ Subgroup.zpowers e) ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxH, hxS⟩
    rw [Subgroup.mem_bot]
    have hx : x ∈ (Subgroup.zpowers c ⊔ Subgroup.zpowers e) ⊓ c25Pre K E := ⟨hxH, hSÊ hxS⟩
    rw [hHE, Subgroup.mem_bot] at hx
    exact hx
  have hSN : S ≤ Subgroup.normalizer ((Subgroup.zpowers c ⊔ Subgroup.zpowers e : Subgroup G) : Set G) := by
    intro s hs
    apply normalizer_of_commute_subgroup
    intro x hx
    obtain ⟨i, j, rfl⟩ := mem_sup_zpowers_normal hce hx
    have hsc : Commute s c := ((hcomm s hs).1).symm
    have hse : Commute s e := ((hcomm s hs).2).symm
    exact (hsc.zpow_right i).mul_right (hse.zpow_right j)
  have hTcard : Nat.card ↥((Subgroup.zpowers c ⊔ Subgroup.zpowers e) ⊔ S) = 9 * Nat.card ↥E := by
    have h := card_sup_mul_card_inf_of_le_normalizer
      (A := Subgroup.zpowers c ⊔ Subgroup.zpowers e) (B := S) hSN
    rw [hHS, Subgroup.card_bot, hHcard, hScard, mul_one] at h
    exact h
  have hTeq : (Subgroup.zpowers c ⊔ Subgroup.zpowers e) ⊔ S =
      Subgroup.zpowers e ⊔ (Subgroup.zpowers c ⊔ S) := by
    rw [sup_comm (Subgroup.zpowers c) (Subgroup.zpowers e), sup_assoc]
  rw [hTeq] at hTcard
  have hcC : c ∈ Subgroup.centralizer (S : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun h hh => ((hcomm h hh).1).symm)
  have hT1 : IsElemAbelian 3 (Subgroup.zpowers c ⊔ S) := c25_isElemAbelian_sup_zpowers hSel hc3 hcC
  have heC : e ∈ Subgroup.centralizer ((Subgroup.zpowers c ⊔ S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hle : Subgroup.zpowers c ⊔ S ≤ Subgroup.centralizer ({e} : Set G) := by
      apply sup_le
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hce
      · intro s hs
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm s hs).2.symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  have hT2 : IsElemAbelian 3 (Subgroup.zpowers e ⊔ (Subgroup.zpowers c ⊔ S)) :=
    c25_isElemAbelian_sup_zpowers hT1 he3 heC
  have hTN : Subgroup.zpowers e ⊔ (Subgroup.zpowers c ⊔ S) ≤
      Subgroup.normalizer (c25Pre K U : Set G) := by
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact normalizer_c25Pre_of_fix heN hUfix'
    · apply sup_le
      · rw [Subgroup.zpowers_le]
        exact normalizer_c25Pre_of_fix hcN (fun u _ => by rw [hcbar, MulAut.one_apply])
      · intro s hs
        exact c25_mem_normalizer_pre (hSK hs) (hEN (mem_c25Pre.1 (hSÊ hs)).2)
  have hTX : Subgroup.zpowers e ⊔ (Subgroup.zpowers c ⊔ S) ≤ K ⊔ B := by
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact (le_sup_right : B ≤ K ⊔ B) heB
    · apply sup_le
      · rw [Subgroup.zpowers_le]
        exact (le_sup_right : B ≤ K ⊔ B) hcB
      · exact hSK.trans le_sup_left
  obtain ⟨j, hj⟩ := (c25_isPGroup_of_elemAbelian hT2).exists_card_eq
  have hj4 : j ≤ 4 :=
    (rank_le_twoLocal_of_normalizes_pre (le_sup_left : K ≤ K ⊔ B) hU hU2 hT2 hTX hTN hj).trans hrk
  have h81 : 3 ^ j ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hj4
  rw [hj] at hTcard
  have hfin : 9 * Nat.card ↥E ≤ 3 ^ 4 := by
    rw [← hTcard]
    exact h81
  norm_num at hfin ⊢
  omega

end CFSG.LocalAnalysis.GLTheoremA.H1431c






end
