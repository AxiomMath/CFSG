module

public import CFSG.GroupTheory.WielandtProductSetup
public import CFSG.GroupTheory.WielandtProductAux

public section

namespace CFSG.GroupTheory.WielandtProduct

open Subgroup
open scoped Pointwise

theorem card_subgroupOf_eq {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
  rw [← Subgroup.inf_subgroupOf_right H K]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem mem_normalizer_map_subtype {G : Type*} [Group G] {K : Subgroup G} {T : Subgroup K}
    {x : K} (hx : x ∈ normalizer (T : Set K)) :
    (x : G) ∈ normalizer ((T.map K.subtype : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨x * t * x⁻¹, (mem_normalizer_iff.mp hx t).mp ht, rfl⟩
  · rintro ⟨t, ht, hty⟩
    refine ⟨x⁻¹ * t * x, ?_, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem hx) t).mp ht
      simpa using this
    · have hty' : (t : G) = x * y * (x : G)⁻¹ := hty
      simp only [coe_subtype, coe_mul, coe_inv, hty']
      group

theorem mem_normalizer_inf_of_mem_normalizer_subgroupOf {G : Type*} [Group G]
    {K P : Subgroup G} {x : K} (hx : x ∈ normalizer ((P.subgroupOf K : Subgroup K) : Set K)) :
    (x : G) ∈ normalizer ((P ⊓ K : Subgroup G) : Set G) := by
  have hmap : (P.subgroupOf K).map K.subtype = P ⊓ K := by
    rw [Subgroup.subgroupOf_map_subtype]
  have := mem_normalizer_map_subtype hx
  rwa [hmap] at this

namespace MinCounter

variable {G : Type} [Group G] [Finite G] {A B : Subgroup G} (h : MinCounter G A B)
include h

theorem exists_mem_sylowOf_zOf {p : ℕ} [hp : Fact p.Prime] (hpA : p ∣ Nat.card A) :
    ∃ z ∈ sylowOf A p, z ∈ zOf A ∧ z ≠ 1 ∧ ∀ y ∈ sylowOf A p, Commute z y := by
  have := h.nilA
  obtain ⟨z, hzP, hzo, hzc⟩ :=
    exists_orderOf_eq_commute_of_isPGroup isPGroup_sylowOf (sylowOf_ne_bot hpA)
  have hz1 : z ≠ 1 := fun h1 => hp.out.one_lt.ne' (by rw [← hzo, h1, orderOf_one])
  refine ⟨z, hzP, mem_zOf.2 ⟨sylowOf_le hzP, fun y hy => ?_⟩, hz1, hzc⟩
  exact (mem_centralizer_singleton_iff.mp (le_centralizer_of_mem_sylowOf hzP hzc hy)).symm

theorem mem_normalizer_of_sylowOf_conj {r : ℕ} [hr : Fact r.Prime] (hrA : r ∣ Nat.card A)
    {g : G} (hg : ∀ y ∈ sylowOf A r, g⁻¹ * y * g ∈ A) : g ∈ normalizer (A : Set G) := by
  have := h.nilA
  let Pg : Subgroup G := (sylowOf A r).map (MulAut.conj g⁻¹).toMonoidHom
  have hmemPg : ∀ x, x ∈ Pg ↔ ∃ y ∈ sylowOf A r, g⁻¹ * y * g = x := by
    intro x
    simp [Pg]
  have hPgP : Pg ≤ sylowOf A r := by
    refine le_sylowOf_of_isPGroup (isPGroup_sylowOf.map _) fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := (hmemPg x).1 hx
    exact hg y hy
  have hcard : Nat.card Pg = Nat.card (sylowOf A r) :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have hPgeq : Pg = sylowOf A r := Subgroup.eq_of_le_of_card_ge hPgP hcard.ge
  obtain ⟨z, hzP, hzZ, hz1, hzc⟩ := h.exists_mem_sylowOf_zOf hrA
  have hwP : g⁻¹ * z * g ∈ sylowOf A r := hPgP ((hmemPg _).2 ⟨z, hzP, rfl⟩)
  have hwc : ∀ y ∈ sylowOf A r, Commute (g⁻¹ * z * g) y := by
    intro y hy
    rw [← hPgeq] at hy
    obtain ⟨y', hy', rfl⟩ := (hmemPg y).1 hy
    have := (hzc y' hy').map (MulAut.conj g⁻¹)
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hwZ : g⁻¹ * z * g ∈ zOf A := mem_zOf.2 ⟨sylowOf_le hwP, fun y hy =>
    (mem_centralizer_singleton_iff.mp (le_centralizer_of_mem_sylowOf hwP hwc hy)).symm⟩
  have hw1 : g⁻¹ * z * g ≠ 1 := fun h1 => hz1 (by
    have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [this, h1]
    group)
  have hCz := h.centralizer_eq hzZ hz1
  have hCw := h.centralizer_eq hwZ hw1
  rw [mem_normalizer_iff]
  intro y
  have e1 : y ∈ A ↔ y * (g⁻¹ * z * g) = (g⁻¹ * z * g) * y := by
    rw [← hCw, mem_centralizer_singleton_iff]
  have e2 : g * y * g⁻¹ ∈ A ↔ (g * y * g⁻¹) * z = z * (g * y * g⁻¹) := by
    rw [← hCz, mem_centralizer_singleton_iff]
  rw [e1, e2]
  constructor
  · intro hy
    calc g * y * g⁻¹ * z = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by rw [hy]
      _ = z * (g * y * g⁻¹) := by group
  · intro hy
    calc y * (g⁻¹ * z * g) = g⁻¹ * (g * y * g⁻¹ * z) * g := by group
      _ = g⁻¹ * (z * (g * y * g⁻¹)) * g := by rw [hy]
      _ = g⁻¹ * z * g * y := by group

theorem mem_normalizer_of_conj_mem_zOf {x g : G} (hxA : x ∈ A) (hx1 : x ≠ 1)
    (hgx : g⁻¹ * x * g ∈ zOf A) : g ∈ normalizer (A : Set G) := by
  have := h.nilA
  obtain ⟨k, hk⟩ := exists_pow_prime_orderOf hx1
  have : Fact (orderOf (x ^ k)).Prime := ⟨hk⟩
  have hxk : x ^ k ∈ A := pow_mem hxA k
  have hxk1 : x ^ k ≠ 1 := fun h1 => hk.one_lt.ne' (by rw [h1, orderOf_one])
  have hpA : orderOf (x ^ k) ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hxk
  have hxP : x ^ k ∈ sylowOf A (orderOf (x ^ k)) := mem_sylowOf_of_orderOf_eq hxk rfl
  have hconj : g⁻¹ * x ^ k * g = (g⁻¹ * x * g) ^ k := by
    have := conj_pow (a := g⁻¹) (b := x) (i := k)
    simpa using this.symm
  have hgxk : g⁻¹ * x ^ k * g ∈ zOf A := hconj ▸ pow_mem hgx k
  have hgxk1 : g⁻¹ * x ^ k * g ≠ 1 := fun h1 => hxk1 (by
    have : x ^ k = g * (g⁻¹ * x ^ k * g) * g⁻¹ := by group
    rw [this, h1]
    group)
  have hC := h.centralizer_eq hgxk hgxk1
  obtain ⟨r, hr, hrA, hrp⟩ := h.exists_prime_ne hk
  have : Fact r.Prime := ⟨hr⟩
  refine h.mem_normalizer_of_sylowOf_conj hrA fun y hy => ?_
  rw [← hC, mem_centralizer_singleton_iff]
  have hc := commute_of_mem_sylowOf_of_ne (A := A) hrp hy hxP
  have := hc.map (MulAut.conj g⁻¹)
  simpa [MulAut.conj_apply, mul_assoc] using this.eq

theorem mem_normalizer_of_mem_zOf_conj {z g : G} (hz : z ∈ zOf A) (hz1 : z ≠ 1)
    (hgz : g⁻¹ * z * g ∈ A) : g ∈ normalizer (A : Set G) := by
  have hne : g⁻¹ * z * g ≠ 1 := fun h1 => hz1 (by
    have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [this, h1]
    group)
  have hmem : g⁻¹⁻¹ * (g⁻¹ * z * g) * g⁻¹ ∈ zOf A := by
    have : g⁻¹⁻¹ * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rw [this]
    exact hz
  have := h.mem_normalizer_of_conj_mem_zOf hgz hne hmem
  simpa using inv_mem this

theorem exists_sylow_eq_subgroupOf {K : Subgroup G} (hZK : zOf A ≤ K) {p : ℕ}
    [hp : Fact p.Prime] (hpA : p ∣ Nat.card A) :
    ∃ T : Sylow p K, (T : Subgroup K) = (sylowOf A p).subgroupOf K := by
  have := h.nilA
  have hPK : IsPGroup p ((sylowOf A p).subgroupOf K) :=
    (isPGroup_sylowOf (A := A) (p := p)).comap_of_injective K.subtype K.subtype_injective
  obtain ⟨T, hT⟩ := hPK.exists_le_sylow
  refine ⟨T, le_antisymm ?_ hT⟩
  have hT' : IsPGroup p ((T : Subgroup K).map K.subtype) := T.isPGroup'.map _
  obtain ⟨S', hS'⟩ := hT'.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G (h.sylow hpA) S'
  obtain ⟨z, hzP, hzZ, hz1, -⟩ := h.exists_mem_sylowOf_zOf hpA
  have hzT' : z ∈ (T : Subgroup K).map K.subtype :=
    ⟨⟨z, hZK hzZ⟩, hT (show ((⟨z, hZK hzZ⟩ : K) : G) ∈ sylowOf A p from hzP), rfl⟩
  have hmemS : ∀ y, y ∈ (S' : Subgroup G) → x⁻¹ * y * x ∈ sylowOf A p := by
    intro y hy
    rw [← hx, Sylow.coe_subgroup_smul, mem_conj_smul_iff, h.coe_sylow] at hy
    exact hy
  have hxN := h.mem_normalizer_of_mem_zOf_conj hzZ hz1 (sylowOf_le (hmemS z (hS' hzT')))
  intro t ht
  rw [mem_subgroupOf]
  have htT' : (t : G) ∈ (T : Subgroup K).map K.subtype := ⟨t, ht, rfl⟩
  have h1 := hmemS _ (hS' htT')
  have htA : (t : G) ∈ A := by
    have := (mem_normalizer_iff.mp hxN (x⁻¹ * t * x)).mp (sylowOf_le h1)
    simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := hT' ⟨t, htT'⟩
  exact mem_sylowOf_iff.2 ⟨htA, k, by simpa using congrArg Subtype.val hk⟩

theorem le_of_forall_prime_dvd {K M : Subgroup G} (hZK : zOf A ≤ K) (hMK : M ≤ K)
    (hAM : A ⊓ K ≤ M) (hpr : ∀ q : ℕ, q.Prime → q ∣ Nat.card M → q ∣ Nat.card A) :
    M ≤ A := by
  have := h.nilA
  have htop : A.subgroupOf M = ⊤ := by
    refine eq_top_of_forall_sylow_le fun p hp => ?_
    have : Fact p.Prime := ⟨hp⟩
    by_cases hpM : p ∣ Nat.card M
    · have hpA := hpr p hp hpM
      obtain ⟨T, hT⟩ := h.exists_sylow_eq_subgroupOf hZK hpA
      have hcK : Nat.card (sylowOf A p ⊓ K : Subgroup G) = p ^ (Nat.card K).factorization p := by
        rw [← card_subgroupOf_eq, ← hT]
        exact Sylow.card_eq_multiplicity T
      have hPM : sylowOf A p ⊓ K ≤ M := (inf_le_inf_right K sylowOf_le).trans hAM
      have hPMeq : sylowOf A p ⊓ M = sylowOf A p ⊓ K :=
        le_antisymm (inf_le_inf_left _ hMK) (le_inf inf_le_left hPM)
      have hv : (Nat.card K).factorization p = (Nat.card M).factorization p := by
        apply le_antisymm
        · exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
            (hcK ▸ Subgroup.card_dvd_of_le hPM)
        · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
            (Subgroup.card_dvd_of_le hMK) p
      have hcS : Nat.card ((sylowOf A p).subgroupOf M) = p ^ (Nat.card M).factorization p := by
        rw [card_subgroupOf_eq, hPMeq, hcK, hv]
      refine ⟨Sylow.ofCard _ hcS, fun x hx => ?_⟩
      rw [Sylow.coe_ofCard, mem_subgroupOf] at hx
      exact mem_subgroupOf.mpr (sylowOf_le hx)
    · refine ⟨Classical.arbitrary _, ?_⟩
      have hc := Sylow.card_eq_multiplicity (Classical.arbitrary (Sylow p M))
      rw [Nat.factorization_eq_zero_of_not_dvd hpM, pow_zero, Subgroup.card_eq_one] at hc
      rw [hc]
      exact bot_le
  exact Subgroup.subgroupOf_eq_top.mp htop

theorem le_of_normalizer_le {K : Subgroup G} (hZK : zOf A ≤ K)
    (hN : ∀ r : ℕ, r.Prime → r ∣ Nat.card A → ∀ x ∈ K,
      x ∈ normalizer ((sylowOf A r ⊓ K : Subgroup G) : Set G) → x ∈ A) : K ≤ A := by
  have := h.nilA
  have := h.nilB
  have := h.isSimpleGroup
  obtain ⟨p, hp, hpA⟩ := Nat.exists_prime_and_dvd fun h1 =>
    h.ne_bot_left (Subgroup.card_eq_one.mp h1)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr, hrA, hrp⟩ := h.exists_prime_ne hp
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨S, hS⟩ := h.exists_sylow_eq_subgroupOf hZK hpA
  obtain ⟨R, hR⟩ := h.exists_sylow_eq_subgroupOf hZK hrA
  have hSR : ∀ s ∈ (S : Subgroup K), ∀ t ∈ (R : Subgroup K), Commute s t := by
    intro s hs t ht
    rw [hS, mem_subgroupOf] at hs
    rw [hR, mem_subgroupOf] at ht
    exact Subtype.ext (commute_of_mem_sylowOf_of_ne (A := A) (Ne.symm hrp) hs ht).eq
  have hRH : normalizer ((R : Subgroup K) : Set K) ≤ A.subgroupOf K := by
    intro x hx
    rw [hR] at hx
    exact mem_subgroupOf.mpr (hN r hr hrA x x.2
      (mem_normalizer_inf_of_mem_normalizer_subgroupOf hx))
  have hH : ∀ y ∈ A.subgroupOf K, ∃ k : ℕ, ∀ s ∈ (S : Subgroup K), Commute (y ^ p ^ k) s := by
    intro y hy
    rw [mem_subgroupOf] at hy
    refine ⟨(orderOf (y : G)).factorization p, fun s hs => ?_⟩
    rw [hS, mem_subgroupOf] at hs
    have h0 : orderOf (y : G) ≠ 0 := (isOfFinOrder_of_finite (y : G)).orderOf_pos.ne'
    have hord : orderOf ((y : G) ^ p ^ (orderOf (y : G)).factorization p) =
        orderOf (y : G) / p ^ (orderOf (y : G)).factorization p :=
      orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (Nat.ordProj_dvd _ _)
    have hnd : ¬ p ∣ orderOf ((y : G) ^ p ^ (orderOf (y : G)).factorization p) := by
      rw [hord]
      exact Nat.not_dvd_ordCompl hp h0
    have hc := commute_of_mem_sylowOf hs (pow_mem hy _) hnd
    exact Subtype.ext (by simpa using hc.eq.symm)
  obtain ⟨K₀, hK₀n, hK₀c, m, hm⟩ := exists_isNormalPComplement S R (A.subgroupOf K) hSR hRH hH
  refine h.le_of_forall_prime_dvd hZK le_rfl inf_le_right fun q hq hqK => ?_
  by_contra hqA
  have : Fact q.Prime := ⟨hq⟩
  have hqB : q ∣ Nat.card B := by
    have : q ∣ Nat.card A * Nat.card B := h.card_eq ▸ hqK.trans (Subgroup.card_dvd_of_le le_top
      |>.trans (by rw [Subgroup.card_top]))
    exact ((Nat.Prime.dvd_mul hq).1 this).resolve_left hqA
  have hpq : p ≠ q := fun he => hqA (he ▸ hpA)
  have hTK₀ : ∀ T : Sylow q K, (T : Subgroup K) ≤ K₀ := by
    intro T
    refine le_of_coprime_index ?_
    obtain ⟨a, ha⟩ := T.isPGroup'.exists_card_eq
    rw [ha, hm]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hp).2 (Ne.symm hpq))
  have hpT : ¬ p ∣ Nat.card (Sylow q K) := by
    intro hd
    let T : Sylow q K := Classical.arbitrary _
    have hF := Sylow.normalizer_sup_eq_top' T (hTK₀ T)
    have hidx := index_dvd_card_of_sup_eq_top hF
    rw [Sylow.card_eq_index_normalizer T] at hd
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hK₀c.symm (hd.trans hidx)
  obtain ⟨a₀, ha₀Z, ha₀o⟩ := h.exists_mem_zOf_orderOf hpA
  have ha₀K : a₀ ∈ K := hZK ha₀Z
  have hZp : IsPGroup p (zpowers (⟨a₀, ha₀K⟩ : K)) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by
      ext
      simp [← ha₀o, pow_orderOf_eq_one])
  obtain ⟨T', hT'⟩ := hZp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q K) hpT
  have ha₀T' : (⟨a₀, ha₀K⟩ : K) ∈ normalizer ((T' : Subgroup K) : Set K) :=
    (Subgroup.sylow_mem_fixedPoints_iff _).mp hT' (mem_zpowers _)
  set W : Subgroup G := (T' : Subgroup K).map K.subtype with hWdef
  have ha₀W : a₀ ∈ normalizer (W : Set G) := mem_normalizer_map_subtype ha₀T'
  have hWq : IsPGroup q W := T'.isPGroup'.map _
  have hWb : W ≠ ⊥ := fun hb =>
    T'.ne_bot_of_dvd_card hqK ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp hb)
  obtain ⟨S'', hS''⟩ := hWq.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G (h.symm.sylow hqB) S''
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mul x
  set W' : Subgroup G := W.comap (MulAut.conj a).toMonoidHom with hW'def
  have hmemW' : ∀ v, v ∈ W' ↔ a * v * a⁻¹ ∈ W := fun v => Iff.rfl
  have hW'B : W' ≤ sylowOf B q := by
    intro v hv
    rw [hmemW'] at hv
    have h1 := hS'' hv
    rw [← hx, Sylow.coe_subgroup_smul, mem_conj_smul_iff, h.symm.coe_sylow] at h1
    have h2 := (mem_normalizer_iff.mp (le_normalizer_sylowOf (A := B) (p := q) hb) _).mp h1
    have e : b * ((a * b)⁻¹ * (a * v * a⁻¹) * (a * b)) * b⁻¹ = v := by group
    rwa [e] at h2
  have hW'b : W' ≠ ⊥ := by
    intro hb'
    apply hWb
    rw [eq_bot_iff]
    intro w hw
    have hw' : a⁻¹ * w * a ∈ W' := by
      rw [hmemW']
      have : a * (a⁻¹ * w * a) * a⁻¹ = w := by group
      rw [this]
      exact hw
    rw [hb', mem_bot] at hw'
    rw [mem_bot]
    have : w = a * (a⁻¹ * w * a) * a⁻¹ := by group
    rw [this, hw']
    group
  have ha₀W' : a₀ ∈ normalizer (W' : Set G) := by
    rw [mem_normalizer_iff]
    intro v
    rw [hmemW', hmemW']
    have hca : Commute a₀ a := (mem_zOf.mp ha₀Z).2 a ha
    have e : a * (a₀ * v * a₀⁻¹) * a⁻¹ = a₀ * (a * v * a⁻¹) * a₀⁻¹ := by
      calc a * (a₀ * v * a₀⁻¹) * a⁻¹ = (a * a₀) * v * (a * a₀)⁻¹ := by group
        _ = (a₀ * a) * v * (a₀ * a)⁻¹ := by rw [hca.eq]
        _ = a₀ * (a * v * a⁻¹) * a₀⁻¹ := by group
    rw [e]
    exact mem_normalizer_iff.mp ha₀W (a * v * a⁻¹)
  obtain ⟨b₀, hb₀Z, hb₀o⟩ := h.symm.exists_mem_zOf_orderOf hqB
  have hb₀W' : b₀ ∈ normalizer (W' : Set G) := by
    apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro v hv
    exact ((mem_zOf.mp hb₀Z).2 v (sylowOf_le (hW'B hv))).eq.symm
  have ha₀1 : a₀ ≠ 1 := fun h1 => hp.one_lt.ne' (by rw [← ha₀o, h1, orderOf_one])
  have hb₀1 : b₀ ≠ 1 := fun h1 => hq.one_lt.ne' (by rw [← hb₀o, h1, orderOf_one])
  have htop := h.zpowers_sup_zpowers ha₀Z ha₀1 hb₀Z hb₀1
  exact h.normalizer_ne_top hW'b (Or.inr (hW'B.trans sylowOf_le))
    (top_le_iff.mp (htop ▸ sup_le (zpowers_le.mpr ha₀W') (zpowers_le.mpr hb₀W')))

end MinCounter

end CFSG.GroupTheory.WielandtProduct
