module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.GH74.GLS.LU.Local.Conj
public import CFSG.GH74.GLS.LU.Local.GenCore

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS
open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local

variable {G : Type} [Group G] [Finite G] {q : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G}

omit [Finite G] in
theorem Cz_conj_z {c : G} (hc : c ∈ Cz z) : c * z * c⁻¹ = z := by
  have := mem_centralizer_singleton_iff.mp hc
  calc c * z * c⁻¹ = z * c * c⁻¹ := by rw [this]
    _ = z := by group

theorem two_elem_centralizer_K (hs : LUSyl G z S K₁ K₂ t u) (hc : LUComps G q z K₁ K₂) {e : G}
    (he : e ∈ Cz z) (hK : ∀ k ∈ K₁ ⊔ K₂, e * k = k * e) {n : ℕ} (hn : e ^ (2 ^ n) = 1) :
    e ∈ zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : ∃ m : ℕ, orderOf e = 2 ^ m := by
    have h1 : orderOf e ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    exact (Nat.dvd_prime_pow Nat.prime_two).mp h1 |>.imp fun m hm => hm.2
  obtain ⟨c, hcC, hcs⟩ := exists_conj_mem_sylow_of_le S hs.S_le_Cz he hord
  have hK' : ∀ k ∈ K₁ ⊔ K₂, (c⁻¹ * e * c) * k = k * (c⁻¹ * e * c) := by
    intro k hk
    have hk' := hc.conj_sup_mem hcC hk
    have := hK _ hk'
    calc (c⁻¹ * e * c) * k = c⁻¹ * (e * (c * k * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * k * c⁻¹) * e) * c := by rw [this]
      _ = k * (c⁻¹ * e * c) := by group
  have h1 := hs.cs _ hcs hK'
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h1
  have hcz := Cz_conj_z hcC
  have : e = c * (c⁻¹ * e * c) * c⁻¹ := by group
  rw [this, ← hi]
  refine mem_zpowers_iff.mpr ⟨i, ?_⟩
  calc z ^ i = (c * z * c⁻¹) ^ i := by rw [hcz]
    _ = c * z ^ i * c⁻¹ := conj_zpow


omit [Finite G] in
theorem le_pPrimeCoreOf_odd {N X : Subgroup G} (hNX : N ≤ X)
    (hnorm : X ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime 2 (Nat.card N)) :
    N ≤ pPrimeCoreOf 2 X := by
  have hnormal : (N.subgroupOf X).Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hnorm h.2) a).mp ha
  have hcop' : Nat.Coprime 2 (Nat.card (N.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
  have hle : N.subgroupOf X ≤ pPrimeCore 2 X := le_sSup ⟨hnormal, hcop'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hle

@[expose] def CCK (z : G) (K₁ K₂ : Subgroup G) : Subgroup G :=
  Cz z ⊓ centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)

omit [Finite G] in
theorem mem_CCK {e : G} : e ∈ CCK z K₁ K₂ ↔ e ∈ Cz z ∧ ∀ k ∈ K₁ ⊔ K₂, e * k = k * e := by
  unfold CCK
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun k hk => (h2 k hk).symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun k hk => (h2 k hk).symm⟩

omit [Finite G] in
theorem CCK_le_Cz : CCK z K₁ K₂ ≤ Cz z := inf_le_left

theorem conj_mem_CCK (hc : LUComps G q z K₁ K₂) {c e : G} (hcC : c ∈ Cz z)
    (he : e ∈ CCK z K₁ K₂) : c * e * c⁻¹ ∈ CCK z K₁ K₂ := by
  rw [mem_CCK] at he ⊢
  obtain ⟨heC, heK⟩ := he
  refine ⟨(Cz z).mul_mem ((Cz z).mul_mem hcC heC) ((Cz z).inv_mem hcC), fun k hk => ?_⟩
  have hk' : c⁻¹ * k * c ∈ K₁ ⊔ K₂ := by
    simpa using hc.conj_sup_mem ((Cz z).inv_mem hcC) hk
  have := heK _ hk'
  calc c * e * c⁻¹ * k = c * (e * (c⁻¹ * k * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * k * c) * e) * c⁻¹ := by rw [this]
    _ = k * (c * e * c⁻¹) := by group

theorem z_mem_CCK (hc : LUComps G q z K₁ K₂) : z ∈ CCK z K₁ K₂ := by
  rw [mem_CCK]
  refine ⟨mem_centralizer_singleton_iff.mpr rfl, fun k hk => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc.comm hk
  have h1 := hc.cz₁ ha
  have h2 := hc.cz₂ hb
  calc z * (a * b) = (z * a) * b := by group
    _ = (a * z) * b := by rw [h1]
    _ = a * (z * b) := by group
    _ = a * (b * z) := by rw [h2]
    _ = (a * b) * z := by group

theorem odd_mem_A0_of_centralizes (hs : LUSyl G z S K₁ K₂ t u) (hc : LUComps G q z K₁ K₂) {e : G}
    (he : e ∈ CCK z K₁ K₂) (hodd : Odd (orderOf e)) : e ∈ A0 z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup G := CCK z K₁ K₂ with hD
  have hzD : z ∈ D := z_mem_CCK hc
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥D) := inferInstance
  have h2el : ∀ τ : ↥D, ∀ n : ℕ, τ ^ (2 ^ n) = 1 → (τ : G) ∈ zpowers z := by
    intro τ n hτ
    have hτG : (τ : G) ^ (2 ^ n) = 1 := by
      have := congrArg Subtype.val hτ
      simpa using this
    have hmem := mem_CCK.mp τ.2
    exact two_elem_centralizer_K hs hc hmem.1 hmem.2 hτG
  have hTle : (T : Subgroup ↥D) ≤ zpowers (⟨z, hzD⟩ : ↥D) := by
    intro τ hτ
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨τ, hτ⟩
    have hn' : τ ^ (2 ^ n) = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (h2el τ n hn')
    refine mem_zpowers_iff.mpr ⟨i, Subtype.ext ?_⟩
    simpa using hi
  have hTcyc : IsCyclic ↥(T : Subgroup ↥D) := by
    have h1 : IsCyclic ↥((T : Subgroup ↥D).subgroupOf (zpowers (⟨z, hzD⟩ : ↥D))) := inferInstance
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTle).surjective
  obtain ⟨-, hmul, -, ⟨hN1, hNodd, hNidx, -⟩, -⟩ := cyclic_sylow_normal_odd_complement T hTcyc
  set N' : Subgroup ↥D := pPrimeCore 2 ↥D with hN'
  set N'' : Subgroup G := N'.map D.subtype with hN''
  have hall : ∀ d : G, d ∈ D → Odd (orderOf d) → d ∈ N'' := by
    intro d hd hdodd
    set d' : ↥D := ⟨d, hd⟩ with hd'
    have hd'ord : orderOf d' = orderOf d := Subgroup.orderOf_mk d hd
    have hmem : d' ∈ (N' : Set ↥D) * (T : Set ↥D) := by rw [hmul]; exact Set.mem_univ _
    obtain ⟨a, ha, τ, hτ, hdaτ⟩ := Set.mem_mul.mp hmem
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨τ, hτ⟩
    have hk' : τ ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    let φ : ↥D →* ↥D ⧸ N' := QuotientGroup.mk' N'
    have hφd : φ d' = φ τ := by
      rw [← hdaτ, map_mul]
      have : φ a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
      rw [this, one_mul]
    have h2k : (φ d') ^ (2 ^ k) = 1 := by rw [hφd, ← map_pow, hk', map_one]
    have hodd' : (φ d') ^ (orderOf d') = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hcop : Nat.Coprime (2 ^ k) (orderOf d') := by
      rw [hd'ord]
      exact Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hdodd)
    have h1 : orderOf (φ d') = 1 := by
      have h2 : orderOf (φ d') ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2k
      have h3 : orderOf (φ d') ∣ orderOf d' := orderOf_dvd_of_pow_eq_one hodd'
      exact Nat.eq_one_of_dvd_coprimes hcop h2 h3
    have : φ d' = 1 := orderOf_eq_one_iff.mp h1
    have hmemN' : d' ∈ N' := (QuotientGroup.eq_one_iff d').mp this
    exact ⟨d', hmemN', rfl⟩
  have hN''odd : ∀ d ∈ N'', Odd (orderOf d) := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := Subgroup.mem_map.mp hd
    have h1 : orderOf d' ∣ Nat.card N' := Subgroup.orderOf_dvd_natCard _ hd'
    have h2 : Odd (orderOf d') := Odd.of_dvd_nat hNodd h1
    rw [show (D.subtype d' : G) = (d' : G) from rfl, Subgroup.orderOf_coe]
    exact h2
  have hN''le : N'' ≤ D := Subgroup.map_subtype_le N'
  have hN''norm : Cz z ≤ Subgroup.normalizer (N'' : Set G) := by
    intro c hcC
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ c ∈ Cz z, ∀ n ∈ N'', c * n * c⁻¹ ∈ N'' := by
      intro c hcC n hn
      have hnD := hN''le hn
      have h1 : c * n * c⁻¹ ∈ D := conj_mem_CCK hc hcC hnD
      refine hall _ h1 ?_
      have := hN''odd n hn
      have e : orderOf (c * n * c⁻¹) = orderOf n := by
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective n
        simpa using this
      rw [e]; exact this
    intro n
    constructor
    · exact fun hn => key c hcC n hn
    · intro hn
      have := key c⁻¹ ((Cz z).inv_mem hcC) _ hn
      simpa [mul_assoc] using this
  have hN''cop : Nat.Coprime 2 (Nat.card N'') := by
    rw [hN'', Subgroup.card_map_of_injective D.subtype_injective]
    exact (Nat.coprime_two_left).mpr hNodd
  have hN''A0 : N'' ≤ A0 z :=
    le_pPrimeCoreOf_odd (hN''le.trans CCK_le_Cz) hN''norm hN''cop
  exact hN''A0 (hall e he hodd)


omit [Finite G] in
theorem mem_zpowers_of_centralizes₁ (hc : LUComps G q z K₁ K₂) {a : G} (ha : a ∈ K₁)
    (h : ∀ k ∈ K₁, a * k = k * a) : a ∈ zpowers z := by
  have : (⟨a, ha⟩ : ↥K₁) ∈ center ↥K₁ := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact (h k k.2).symm
  have h1 : a ∈ (center ↥K₁).map K₁.subtype := ⟨⟨a, ha⟩, this, rfl⟩
  rw [hc.cen₁] at h1
  exact h1

omit [Finite G] in
theorem two_pow_of_commute {a b : G} (hab : Commute a b) {m n : ℕ} (ha : a ^ (2 ^ m) = 1)
    (hb : b ^ (2 ^ n) = 1) : (a * b) ^ (2 ^ (m + n)) = 1 := by
  rw [hab.mul_pow, pow_add, pow_mul, ha, one_pow, mul_comm (2 ^ m) (2 ^ n), pow_mul, hb, one_pow,
    mul_one]

theorem cs₁_aux (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsK : ∀ k ∈ K₁, s * k = k * s) (hsK' : s ∉ K₁ ⊔ K₂) :
    s ∈ K₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsC : s ∈ Cz z := hs.S_le_Cz hsS
  have hz2 : z ∈ K₂ := hc.z_mem₂
  have htS : t ∈ (S : Subgroup G) := hs.t_mem
  have htC : t ∈ Cz z := hs.S_le_Cz htS
  have ht2 : t * t = 1 := hs.t_sq
  set K : Subgroup G := K₁ ⊔ K₂ with hK
  set Q : Subgroup G := (S : Subgroup G) ⊓ K with hQ
  set Qs : Subgroup ↥(S : Subgroup G) := Q.subgroupOf (S : Subgroup G) with hQs
  set N₁ : Subgroup G := normalizer (K₁ : Set G) with hN₁
  set S1s : Subgroup ↥(S : Subgroup G) := N₁.subgroupOf (S : Subgroup G) with hS1s
  have hsN₁ : s ∈ N₁ := Subgroup.centralizer_le_normalizer (K₁ : Set G)
    (mem_centralizer_iff.mpr (fun a ha => (hsK a ha).symm))
  have hQS1 : Qs ≤ S1s := by
    intro x hx
    have hxQ : (x : G) ∈ Q := hx
    exact hc.le_normalizer₁ hxQ.2
  have hS1top : S1s ≠ ⊤ := by
    intro h
    have : (⟨t, htS⟩ : ↥(S : Subgroup G)) ∈ S1s := by rw [h]; trivial
    exact hs.t_not_normalizer hc this
  have hQne : Qs ≠ S1s := by
    intro h
    have : (⟨s, hsS⟩ : ↥(S : Subgroup G)) ∈ S1s := hsN₁
    rw [← h] at this
    exact hsK' this.2
  have hQcard : Nat.card ↥Qs = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Q ≤ (S : Subgroup G))).toEquiv
  have hQidx : Qs.index = 4 := by
    have h1 := Subgroup.card_mul_index Qs
    have h2 := hs.card_S
    rw [← hQcard] at h2
    have hpos : 0 < Nat.card ↥Qs := Nat.card_pos
    have : Nat.card ↥Qs * Qs.index = Nat.card ↥Qs * 4 := by rw [h1, h2]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hrel : Qs.relIndex S1s * S1s.index = Qs.index := Subgroup.relIndex_mul_index hQS1
  have hS1idx : S1s.index ≠ 1 := fun h => hS1top (Subgroup.index_eq_one.mp h)
  have hrel1 : Qs.relIndex S1s ≠ 1 := fun h => hQne (le_antisymm hQS1 (Subgroup.relIndex_eq_one.mp h))
  have hrel0 : Qs.relIndex S1s ≠ 0 := by
    intro h; rw [h] at hrel; omega
  have hS10 : S1s.index ≠ 0 := by
    intro h; rw [h] at hrel; omega
  have hrel2 : Qs.relIndex S1s = 2 := by
    rw [hQidx] at hrel
    have h1 : 2 ≤ Qs.relIndex S1s := by omega
    have h2 : 2 ≤ S1s.index := by omega
    nlinarith
  set s' : G := t * s * t⁻¹ with hs'
  have hs'S : s' ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem htS hsS)
    ((S : Subgroup G).inv_mem htS)
  have hs'C : s' ∈ Cz z := hs.S_le_Cz hs'S
  have ht1 : ∀ k ∈ K₂, t * k * t⁻¹ ∈ K₁ := fun k hk => LUComps.mem_of_map hs.t_swap₂ hk
  have ht1' : ∀ k ∈ K₁, t * k * t⁻¹ ∈ K₂ := fun k hk => LUComps.mem_of_map hs.t_swap hk
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs'K₂ : ∀ k ∈ K₂, s' * k = k * s' := by
    intro k hk
    have hk1 : t * k * t⁻¹ ∈ K₁ := ht1 k hk
    have h1 := hsK _ hk1
    have : k = t * (t * k * t⁻¹) * t⁻¹ := by
      calc k = (t * t) * k * (t * t)⁻¹ := by rw [ht2]; group
        _ = t * (t * k * t⁻¹) * t⁻¹ := by group
    calc s' * k = t * s * t⁻¹ * (t * (t * k * t⁻¹) * t⁻¹) := by rw [← this]
      _ = t * (s * (t * k * t⁻¹)) * t⁻¹ := by group
      _ = t * ((t * k * t⁻¹) * s) * t⁻¹ := by rw [h1]
      _ = (t * (t * k * t⁻¹) * t⁻¹) * (t * s * t⁻¹) := by group
      _ = k * s' := by rw [← this]
  have hs'N₁ : s' ∈ N₁ := by
    rcases hc.perm hs'C with ⟨e1, -⟩ | ⟨e1, e2⟩
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr e1
    · exfalso
      apply hc.ne
      have hn2 : s' ∈ normalizer (K₂ : Set G) := Subgroup.centralizer_le_normalizer (K₂ : Set G)
        (mem_centralizer_iff.mpr (fun a ha => (hs'K₂ a ha).symm))
      have := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn2
      rw [← e2]
      exact this
  have hs'Q : s' ∉ K := by
    intro h
    apply hsK'
    have h1 := hc.conj_sup_mem (Cz z |>.inv_mem htC) h
    have e : t⁻¹ * s' * t⁻¹⁻¹ = s := by
      rw [hs', inv_inv]; group
    rw [e] at h1
    exact h1
  have hs'1 : (⟨s', hs'S⟩ : ↥(S : Subgroup G)) ∈ S1s := hs'N₁
  have hs'2 : (⟨s', hs'S⟩ : ↥(S : Subgroup G)) ∉ Qs := fun h => hs'Q (show s' ∈ Q from h).2
  have hs1 : (⟨s, hsS⟩ : ↥(S : Subgroup G)) ∈ S1s := hsN₁
  have hs2 : (⟨s, hsS⟩ : ↥(S : Subgroup G)) ∉ Qs := fun h => hsK' (show s ∈ Q from h).2
  have hidx2 : (Qs.subgroupOf S1s).index = 2 := hrel2
  have hq : (⟨s, hsS⟩ : ↥(S : Subgroup G))⁻¹ * ⟨s', hs'S⟩ ∈ Qs := by
    have := (Subgroup.mul_mem_iff_of_index_two hidx2 (a := ⟨(⟨s, hsS⟩ : ↥(S : Subgroup G))⁻¹,
      S1s.inv_mem hs1⟩) (b := ⟨⟨s', hs'S⟩, hs'1⟩)).mpr (by
      constructor
      · intro h
        have h' : (⟨s, hsS⟩ : ↥(S : Subgroup G))⁻¹ ∈ Qs := h
        exact absurd (by simpa using Qs.inv_mem h') hs2
      · intro h; exact absurd h hs'2)
    exact this
  have hqQ : s⁻¹ * s' ∈ Q := hq
  obtain ⟨k₁', hk₁', k₂', hk₂', hq'⟩ := mem_sup_of_commute hc.comm hqQ.2
  have hs'eq : s' = s * (k₁' * k₂') := by rw [← hq']; group
  have hk₂C : k₂' ∈ Cz z := hc.comp₂.1 hk₂'
  have heK₂ : ∀ k ∈ K₂, (s * k₂') * k = k * (s * k₂') := by
    intro k hk
    have h1 := hs'K₂ k hk
    rw [hs'eq] at h1
    have hk2k : k₂' * k ∈ K₂ := K₂.mul_mem hk₂' hk
    have e1 : k₁' * (k₂' * k) = (k₂' * k) * k₁' := hc.comm k₁' hk₁' _ hk2k
    have e2 : k₁' * k₂' = k₂' * k₁' := hc.comm k₁' hk₁' k₂' hk₂'
    have h2 : (s * k₂' * k) * k₁' = (k * (s * k₂')) * k₁' := by
      calc (s * k₂' * k) * k₁' = s * ((k₂' * k) * k₁') := by group
        _ = s * (k₁' * (k₂' * k)) := by rw [e1]
        _ = s * (k₁' * k₂') * k := by group
        _ = k * (s * (k₁' * k₂')) := h1
        _ = k * (s * (k₂' * k₁')) := by rw [e2]
        _ = (k * (s * k₂')) * k₁' := by group
    exact mul_right_cancel h2
  have hsk₂ : s * k₂' = k₂' * s := by
    have h1 := heK₂ k₂' hk₂'
    have h2 : (s * k₂') * k₂' = (k₂' * s) * k₂' := by
      calc (s * k₂') * k₂' = k₂' * (s * k₂') := h1
        _ = (k₂' * s) * k₂' := by group
    exact mul_right_cancel h2
  have heC : s * k₂' ∈ Cz z := (Cz z).mul_mem hsC hk₂C
  have heK : ∀ k ∈ K₁ ⊔ K₂, (s * k₂') * k = k * (s * k₂') := by
    intro k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc.comm hk
    have h1 := hsK a ha
    have h2 : a * k₂' = k₂' * a := hc.comm a ha k₂' hk₂'
    have h3 := heK₂ b hb
    calc (s * k₂') * (a * b) = s * (k₂' * a) * b := by group
      _ = s * (a * k₂') * b := by rw [h2]
      _ = (s * a) * k₂' * b := by group
      _ = (a * s) * k₂' * b := by rw [h1]
      _ = a * ((s * k₂') * b) := by group
      _ = a * (b * (s * k₂')) := by rw [h3]
      _ = (a * b) * (s * k₂') := by group
  obtain ⟨n, hn⟩ := (S.isPGroup') ⟨s, hsS⟩
  have hn' : s ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨n', hn''⟩ := (S.isPGroup') ⟨s⁻¹ * s', (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hsS) hs'S⟩
  have hq2 : (s⁻¹ * s') ^ (2 ^ n') = 1 := by
    have := congrArg Subtype.val hn''
    simpa using this
  have hk₂2 : k₂' ^ (2 ^ (n' + 1)) = 1 := by
    rw [hq'] at hq2
    have hcomm : Commute k₁' k₂' := hc.comm k₁' hk₁' k₂' hk₂'
    rw [hcomm.mul_pow] at hq2
    have h1 : k₂' ^ (2 ^ n') = (k₁' ^ (2 ^ n'))⁻¹ := eq_inv_of_mul_eq_one_right hq2
    have h2 : k₂' ^ (2 ^ n') ∈ K₁ ⊓ K₂ := by
      refine ⟨?_, K₂.pow_mem hk₂' _⟩
      rw [h1]; exact K₁.inv_mem (K₁.pow_mem hk₁' _)
    rw [hc.inf_eq] at h2
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp h2
    have hz2' : z * z = 1 := hs.z_sq
    have : (k₂' ^ (2 ^ n')) ^ 2 = 1 := by
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      have : z ^ ((2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_two]; exact hz2'
      rw [this, one_zpow]
    rw [← pow_mul] at this
    rwa [pow_succ]
  have heord : (s * k₂') ^ (2 ^ (n + (n' + 1))) = 1 :=
    two_pow_of_commute (hsk₂) hn' hk₂2
  have hez := two_elem_centralizer_K hs hc heC heK heord
  have : s = (s * k₂') * k₂'⁻¹ := by group
  rw [this]
  exact K₂.mul_mem ((zpowers_le.mpr hz2) hez) (K₂.inv_mem hk₂')

theorem cs₁ (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsK : ∀ k ∈ K₁, s * k = k * s) : s ∈ K₂ := by
  classical
  have hsC : s ∈ Cz z := hs.S_le_Cz hsS
  have hz2 : z ∈ K₂ := hc.z_mem₂
  by_cases hsK' : s ∈ K₁ ⊔ K₂
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc.comm hsK'
    have haz : a ∈ zpowers z := by
      refine mem_zpowers_of_centralizes₁ hc ha (fun k hk => ?_)
      have h1 := hsK k hk
      have hbk : b * k = k * b := (hc.comm k hk b hb).symm
      have h2 : (a * k) * b = (k * a) * b := by
        calc (a * k) * b = a * (k * b) := by group
          _ = a * (b * k) := by rw [hbk]
          _ = (a * b) * k := by group
          _ = k * (a * b) := h1
          _ = (k * a) * b := by group
      exact mul_right_cancel h2
    exact (K₂).mul_mem ((zpowers_le.mpr hz2) haz) hb
  · exact cs₁_aux hc hs hsS hsK hsK'


theorem solvable_of_odd_index_le_four {Γ : Type*} [Group Γ] [Finite Γ] (T : Subgroup Γ)
    (hT : Odd (Nat.card T)) (hidx : T.index ≤ 4) : Group.IsSolvable Γ := by
  have hTs : Group.IsSolvable ↥T := CFSG.Milestones.odd_order_solvable hT
  let f := MulAction.toPermHom Γ (Γ ⧸ T)
  have hker : f.ker ≤ T := by
    intro g hg
    have h1 : g • ((1 : Γ) : Γ ⧸ T) = ((1 : Γ) : Γ ⧸ T) := by
      have := MonoidHom.mem_ker.mp hg
      exact congrArg (fun π => π ((1 : Γ) : Γ ⧸ T)) this
    have h2 : ((g * 1 : Γ) : Γ ⧸ T) = ((1 : Γ) : Γ ⧸ T) := h1
    rw [QuotientGroup.eq] at h2
    simpa using T.inv_mem h2
  have hkers : Group.IsSolvable ↥f.ker :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hker)
      (Subgroup.inclusion_injective hker)
  have hperm : Group.IsSolvable (Equiv.Perm (Γ ⧸ T)) := by
    refine Equiv.Perm.isSolvable ?_
    rw [← Subgroup.index_eq_card]
    exact hidx
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)


omit [Finite G] in
theorem Fstar_le_Cz (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) :
    Fstar (S : Subgroup G) K₁ K₂ u ≤ Cz z := by
  intro x hx
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
  have h1 : (x' : G) ∈ centralizer (((S : Subgroup G) ⊓ (K₁ ⊔ K₂) ⊔ zpowers u : Subgroup G) : Set G) :=
    x'.2
  have hzQ : z ∈ ((S : Subgroup G) ⊓ (K₁ ⊔ K₂) ⊔ zpowers u : Subgroup G) :=
    Subgroup.mem_sup_left ⟨hs.z_mem, Subgroup.mem_sup_left hc.z_mem₁⟩
  have := Subgroup.mem_centralizer_iff.mp h1 z hzQ
  exact mem_centralizer_singleton_iff.mpr this.symm

theorem index_Q (hs : LUSyl G z S K₁ K₂ t u) :
    (((S : Subgroup G) ⊓ (K₁ ⊔ K₂)).subgroupOf (S : Subgroup G)).index = 4 := by
  set Q : Subgroup G := (S : Subgroup G) ⊓ (K₁ ⊔ K₂) with hQ
  set Qs : Subgroup ↥(S : Subgroup G) := Q.subgroupOf (S : Subgroup G) with hQs
  have hQcard : Nat.card ↥Qs = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Q ≤ (S : Subgroup G))).toEquiv
  have h1 := Subgroup.card_mul_index Qs
  have h2 := hs.card_S
  rw [← hQcard] at h2
  have hpos : 0 < Nat.card ↥Qs := Nat.card_pos
  have : Nat.card ↥Qs * Qs.index = Nat.card ↥Qs * 4 := by rw [h1, h2]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem perfect_le_K (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u)
    (hgen : ∀ c ∈ Cz z, ∃ a ∈ A0 z, ∃ k ∈ K₁ ⊔ K₂, ∃ s ∈ (S : Subgroup G),
      ∃ y ∈ Fstar (S : Subgroup G) K₁ K₂ u, c = a * k * s * y)
    {Λ : Subgroup G} (hΛC : Λ ≤ Cz z) (hΛ : ⁅Λ, Λ⁆ = Λ) : Λ ≤ K₁ ⊔ K₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := Cz z with hX
  set Kx : Subgroup ↥X := (K₁ ⊔ K₂).subgroupOf X with hKx
  have hKxn : Kx.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ K₁ ⊔ K₂ := hn
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ K₁ ⊔ K₂
    exact hc.conj_sup_mem g.2 hn'
  let π : ↥X →* ↥X ⧸ Kx := QuotientGroup.mk' Kx
  set Ax : Subgroup ↥X := pPrimeCore 2 ↥X with hAx
  set Fx : Subgroup ↥X := (Fstar (S : Subgroup G) K₁ K₂ u).subgroupOf X with hFx
  have hAxodd : Odd (Nat.card Ax) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hFxodd : Odd (Nat.card Fx) := by
    have h1 : Nat.Coprime 2 (Nat.card (Fstar (S : Subgroup G) K₁ K₂ u)) := by
      unfold Fstar pPrimeCoreOf
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact pPrimeCore_coprime_card
    have h2 : Nat.card Fx = Nat.card (Fstar (S : Subgroup G) K₁ K₂ u) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Fstar_le_Cz hc hs)).toEquiv
    rw [h2]; exact Nat.coprime_two_left.mp h1
  have hPodd : Odd (Nat.card ↥(Ax ⊔ Fx)) := by
    refine odd_card_sup_of_le_normalizer ?_ hAxodd hFxodd
    rw [(Subgroup.normalizer_eq_top_iff).mpr (inferInstance : Ax.Normal)]
    exact le_top
  set T : Subgroup (↥X ⧸ Kx) := (Ax ⊔ Fx).map π with hT
  have hTodd : Odd (Nat.card T) :=
    Odd.of_dvd_nat hPodd (Subgroup.card_map_dvd (Ax ⊔ Fx) π)
  set Qs : Subgroup ↥(S : Subgroup G) := ((S : Subgroup G) ⊓ (K₁ ⊔ K₂)).subgroupOf (S : Subgroup G)
    with hQs
  have hQsn : Qs.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂) := hn
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂)
    exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem g.2 hn'.1) ((S : Subgroup G).inv_mem g.2),
      hc.conj_sup_mem (hs.S_le_Cz g.2) hn'.2⟩
  have hSX : (S : Subgroup G) ≤ X := hs.S_le_Cz
  let f : ↥(S : Subgroup G) → ((↥X ⧸ Kx) ⧸ T) := fun s =>
    ((π ⟨(s : G), hSX s.2⟩ : ↥X ⧸ Kx) : (↥X ⧸ Kx) ⧸ T)
  have hfconst : ∀ a b : ↥(S : Subgroup G), (QuotientGroup.leftRel Qs) a b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have hq : (a⁻¹ * b : ↥(S : Subgroup G)) ∈ Qs := hab
    have hqm : ((a⁻¹ * b : ↥(S : Subgroup G)) : G) ∈ (S : Subgroup G) ⊓ (K₁ ⊔ K₂) := hq
    have hqK : ((a⁻¹ * b : ↥(S : Subgroup G)) : G) ∈ K₁ ⊔ K₂ := hqm.2
    have hπ : π ⟨((a⁻¹ * b : ↥(S : Subgroup G)) : G), hSX (a⁻¹ * b).2⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hqK
    have hb : (⟨(b : G), hSX b.2⟩ : ↥X) = ⟨(a : G), hSX a.2⟩ *
        ⟨((a⁻¹ * b : ↥(S : Subgroup G)) : G), hSX (a⁻¹ * b).2⟩ := by
      apply Subtype.ext; simp
    show ((π ⟨(a : G), hSX a.2⟩ : ↥X ⧸ Kx) : (↥X ⧸ Kx) ⧸ T) = ((π ⟨(b : G), hSX b.2⟩ : ↥X ⧸ Kx) : (↥X ⧸ Kx) ⧸ T)
    rw [hb, map_mul, hπ, mul_one]
  let F : (↥(S : Subgroup G) ⧸ Qs) → ((↥X ⧸ Kx) ⧸ T) := Quotient.lift f hfconst
  have hFsurj : Function.Surjective F := by
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, haA, k, hk, s, hsS, y', hyF, hx⟩ := hgen (x : G) x.2
    refine ⟨((⟨s, hsS⟩ : ↥(S : Subgroup G)) : ↥(S : Subgroup G) ⧸ Qs), ?_⟩
    show ((π ⟨s, hSX hsS⟩ : ↥X ⧸ Kx) : (↥X ⧸ Kx) ⧸ T) = ((π x : ↥X ⧸ Kx) : (↥X ⧸ Kx) ⧸ T)
    have haX : a ∈ X := by
      obtain ⟨a', -, rfl⟩ := Subgroup.mem_map.mp haA
      exact a'.2
    have hkX : k ∈ X := sup_le hc.comp₁.1 hc.comp₂.1 hk
    have hyX : y' ∈ X := Fstar_le_Cz hc hs hyF
    set ax : ↥X := ⟨a, haX⟩ with hax
    set kx : ↥X := ⟨k, hkX⟩ with hkx
    set sx : ↥X := ⟨s, hSX hsS⟩ with hsx
    set yx : ↥X := ⟨y', hyX⟩ with hyx
    have hxeq : x = ax * kx * sx * yx := Subtype.ext hx
    have hax' : ax ∈ Ax := by
      obtain ⟨a', ha', hea⟩ := Subgroup.mem_map.mp haA
      have : a' = ax := Subtype.ext hea
      rw [← this]; exact ha'
    have hyx' : yx ∈ Fx := Subgroup.mem_subgroupOf.mpr hyF
    have hkx' : π kx = 1 := (QuotientGroup.eq_one_iff _).mpr hk
    rw [QuotientGroup.eq]
    have e : (π sx)⁻¹ * π x = π (sx⁻¹ * ax * sx * yx) := by
      rw [hxeq]; simp only [map_mul, map_inv, hkx']; group
    rw [e]
    refine Subgroup.mem_map_of_mem π ?_
    refine (Ax ⊔ Fx).mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hyx')
    exact (inferInstance : Ax.Normal).conj_mem ax hax' sx⁻¹ |> fun h => by simpa [mul_assoc] using h
  have hTidx : T.index ≤ 4 := by
    rw [Subgroup.index_eq_card]
    have h1 := Nat.card_le_card_of_surjective F hFsurj
    have h2 : Nat.card (↥(S : Subgroup G) ⧸ Qs) = 4 := by rw [← Subgroup.index_eq_card]; exact index_Q hs
    omega
  have hsolv : Group.IsSolvable (↥X ⧸ Kx) := solvable_of_odd_index_le_four T hTodd hTidx
  set Λ' : Subgroup ↥X := Λ.subgroupOf X with hΛ'
  have hΛ'map : Λ'.map X.subtype = Λ := Subgroup.map_subgroupOf_eq_of_le hΛC
  have hΛ'perf : ⁅Λ', Λ'⁆ = Λ' := by
    apply Subgroup.map_injective (X.subtype_injective)
    rw [Subgroup.map_commutator, hΛ'map, hΛ]
  set H : Subgroup (↥X ⧸ Kx) := Λ'.map π with hH
  have hHperf : ⁅H, H⁆ = H := by
    rw [hH, ← Subgroup.map_commutator, hΛ'perf]
  have hHbot : H = ⊥ := by
    by_contra hne
    have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
    have : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hHperf
    exact Group.IsPerfect.not_isSolvable ↥H inferInstance
  intro g hg
  have hgΛ' : (⟨g, hΛC hg⟩ : ↥X) ∈ Λ' := hg
  have h1 : π ⟨g, hΛC hg⟩ ∈ H := Subgroup.mem_map_of_mem π hgΛ'
  rw [hHbot, Subgroup.mem_bot] at h1
  have h2 : (⟨g, hΛC hg⟩ : ↥X) ∈ Kx := (QuotientGroup.eq_one_iff _).mp h1
  exact h2

end CFSG.GH74.GLS.LU.Local
