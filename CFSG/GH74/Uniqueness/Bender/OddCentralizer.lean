module

public import CFSG.GH74.Uniqueness.Bender.OddComplement

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section CartanCentralizer

variable {K : Type*} [Group K] {q i : ℕ} {P : Subgroup K} {t : K}

theorem BenderCore.eq_one_of_commute_cartan [Finite K] (h : BenderCore q i 1 P t)
    (hP : IsPGroup 2 P) {x p : K} (hx : x ∈ cartan P t) (hx1 : x ≠ 1) (hp : p ∈ P)
    (hpx : p * x = x * p) : p = 1 := by
  by_contra hp1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hpk : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hord : orderOf p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpk
  have hord1 : orderOf p ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hord1 (by simpa using hj)
  have h2 : 2 ∣ orderOf p := by
    rw [hj]
    exact dvd_pow_self 2 hj0
  have hpos : orderOf p ≠ 0 := (orderOf_pos p).ne'
  set z := p ^ (orderOf p / 2) with hzdef
  have hz : orderOf z = 2 := orderOf_pow_orderOf_div hpos h2
  have hz2 : z * z = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    omega
  have hzP : z ∈ P := P.pow_mem hp _
  have hzroot : z ∈ rootCenter P := h.mem_rootCenter_of_mul_self hzP hz2
  have hzx : x * z = z * x := ((Commute.pow_left hpx _) : Commute (p ^ (orderOf p / 2)) x).symm.eq
  have hmem : x ∈ cartan P t ⊓ centralizer ({z} : Set K) :=
    ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hzx⟩
  rw [h.cartan_inf_centralizer_eq hzroot hz1, h.fixCartan_eq_bot] at hmem
  exact hx1 (Subgroup.mem_bot.mp hmem)

theorem BenderCore.centralizer_cartan_eq [Finite K] (h : BenderCore q i 1 P t) (hP : IsPGroup 2 P)
    {x : K} (hx : x ∈ cartan P t) (hx1 : x ≠ 1) :
    centralizer ({x} : Set K) = cartan P t := by
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  have hxinv : t * x * t = x⁻¹ := by
    have hxc : x ∈ ⁅cartan P t, Subgroup.zpowers t⁆ := by
      rw [← h.cartan_eq_commutator rfl]
      exact hx
    exact (h.mem_commutator_cartan_iff.mp hxc).2
  have hxt : t * x * t ≠ x := by
    intro hxt
    rw [hxinv] at hxt
    have hsq : x * x = 1 := by
      calc x * x = x⁻¹ * x := by rw [hxt]
        _ = 1 := inv_mul_cancel x
    have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
    have h2 : orderOf x ∣ Nat.card (cartan P t) :=
      (Subgroup.orderOf_coe (⟨x, hx⟩ : cartan P t)) ▸ orderOf_dvd_natCard _
    have hcop : Nat.Coprime (orderOf x) 2 := by
      have := h.odd_card_cartan
      exact Nat.Coprime.coprime_dvd_left h2 ((Nat.coprime_two_right).mpr this)
    have : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd hcop h1
    exact hx1 (orderOf_eq_one_iff.mp this)
  have hDP : ∀ y : K, y ∈ cartan P t → y ∈ P → y = 1 := by
    intro y hyD hyP
    have : y ∈ P ⊓ cartan P t := ⟨hyP, hyD⟩
    rw [h.inf_eq, Subgroup.mem_bot] at this
    exact this
  have hnormP : ∀ y ∈ borel P, ∀ a ∈ P, y * a * y⁻¹ ∈ P := fun y hy a ha =>
    (Subgroup.mem_normalizer_iff.mp hy a).mp ha
  have hMdecomp : ∀ m ∈ borel P, ∃ p ∈ P, ∃ d ∈ cartan P t, m = p * d := by
    intro m hm
    have hset := Subgroup.coe_mul_of_right_le_normalizer_left P (cartan P t)
      (cartan_le_borel P t)
    have hm' : m ∈ ((P ⊔ cartan P t : Subgroup K) : Set K) := by rw [h.sup_eq]; exact hm
    rw [hset] at hm'
    obtain ⟨p, hp, d, hd, rfl⟩ := Set.mem_mul.mp hm'
    exact ⟨p, hp, d, hd, rfl⟩
  apply le_antisymm
  · intro c hc
    have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hcM : c ∈ borel P := by
      by_contra hcM
      obtain ⟨p, hpP, m, hmM, rfl⟩ := h.bruhat hcM
      have hconj : (p * t * m) * x * (p * t * m)⁻¹ = x := by
        rw [hcx]; group
      have hx'' : t * (m * x * m⁻¹) * t = p⁻¹ * x * p := by
        calc t * (m * x * m⁻¹) * t = t * (m * x * m⁻¹) * t⁻¹ := by rw [hti]
          _ = p⁻¹ * ((p * t * m) * x * (p * t * m)⁻¹) * p := by group
          _ = p⁻¹ * x * p := by rw [hconj]
      have hxM : x ∈ borel P := cartan_le_borel P t hx
      have hx''M : m * x * m⁻¹ ∈ borel P :=
        (borel P).mul_mem ((borel P).mul_mem hmM hxM) ((borel P).inv_mem hmM)
      have hconjM : t * (m * x * m⁻¹) * t⁻¹ ∈ borel P := by
        rw [hti, hx'']
        exact (borel P).mul_mem ((borel P).mul_mem ((borel P).inv_mem (le_borel P hpP)) hxM)
          (le_borel P hpP)
      have hx''D : m * x * m⁻¹ ∈ cartan P t :=
        Subgroup.mem_inf.mpr ⟨hx''M, mem_conjugate_iff_mul_inv.mpr hconjM⟩
      obtain ⟨q', hq', d, hd, rfl⟩ := hMdecomp m hmM
      have hxd : x * d = d * x := h.cartan_comm hx hd
      have hxq : q' * x * q'⁻¹ = x := by
        have h1 : q' * d * x * (q' * d)⁻¹ = q' * x * q'⁻¹ := by
          calc q' * d * x * (q' * d)⁻¹ = q' * (d * x * d⁻¹) * q'⁻¹ := by group
            _ = q' * x * q'⁻¹ := by rw [← hxd]; group
        rw [h1] at hx''D
        have hinvD : x⁻¹ * (q' * x * q'⁻¹) ∈ cartan P t :=
          (cartan P t).mul_mem ((cartan P t).inv_mem hx) hx''D
        have hinvP : x⁻¹ * (q' * x * q'⁻¹) ∈ P := by
          have := hnormP x⁻¹ ((borel P).inv_mem hxM) q' hq'
          have h3 : x⁻¹ * (q' * x * q'⁻¹) = (x⁻¹ * q' * x) * q'⁻¹ := by group
          rw [h3]
          have h4 : x⁻¹ * q' * x ∈ P := by
            have := hnormP x⁻¹ ((borel P).inv_mem hxM) q' hq'
            simpa using this
          exact P.mul_mem h4 (P.inv_mem hq')
        have h5 := hDP _ hinvD hinvP
        calc q' * x * q'⁻¹ = x * (x⁻¹ * (q' * x * q'⁻¹)) := by group
          _ = x := by rw [h5, mul_one]
      have hq1 : q' = 1 :=
        h.eq_one_of_commute_cartan hP hx hx1 hq' (by
          calc q' * x = (q' * x * q'⁻¹) * q' := by group
            _ = x * q' := by rw [hxq])
      subst hq1
      have hpx : p⁻¹ * x * p = t * x * t := by
        calc p⁻¹ * x * p = t * (d * x * d⁻¹) * t := by simpa using hx''.symm
          _ = t * x * t := by rw [← hxd]; group
      have hD1 : x⁻¹ * (p⁻¹ * x * p) ∈ cartan P t := by
        rw [hpx]
        exact (cartan P t).mul_mem ((cartan P t).inv_mem hx) (h.cartan_mul_mul hx)
      have hP1 : x⁻¹ * (p⁻¹ * x * p) ∈ P := by
        have h3 : x⁻¹ * (p⁻¹ * x * p) = (x⁻¹ * p⁻¹ * x) * p := by group
        rw [h3]
        have h4 : x⁻¹ * p⁻¹ * x ∈ P := by
          have := hnormP x⁻¹ ((borel P).inv_mem hxM) p⁻¹ (P.inv_mem hpP)
          simpa using this
        exact P.mul_mem h4 hpP
      have h6 := hDP _ hD1 hP1
      have h7 : p⁻¹ * x * p = x := by
        calc p⁻¹ * x * p = x * (x⁻¹ * (p⁻¹ * x * p)) := by group
          _ = x := by rw [h6, mul_one]
      apply hxt
      rw [← hpx, h7]
    obtain ⟨q', hq', d, hd, rfl⟩ := hMdecomp c hcM
    have hxd : x * d = d * x := h.cartan_comm hx hd
    have hq'x : q' * x = x * q' := by
      have h1 : q' * d * x = x * (q' * d) := hcx
      calc q' * x = q' * (d * x * d⁻¹) := by rw [← hxd]; group
        _ = (q' * d * x) * d⁻¹ := by group
        _ = x * (q' * d) * d⁻¹ := by rw [h1]
        _ = x * q' := by group
    have hq1 : q' = 1 := h.eq_one_of_commute_cartan hP hx hx1 hq' hq'x
    rw [hq1, one_mul]
    exact hd
  · intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h.cartan_comm hd hx

theorem BenderCore.exists_mul_of_mem_borel [Finite K] {e : ℕ} (h : BenderCore q i e P t) {m : K}
    (hm : m ∈ borel P) : ∃ p ∈ P, ∃ d ∈ cartan P t, m = p * d := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left P (cartan P t) (cartan_le_borel P t)
  have hm' : m ∈ ((P ⊔ cartan P t : Subgroup K) : Set K) := by rw [h.sup_eq]; exact hm
  rw [hset] at hm'
  obtain ⟨p, hp, d, hd, rfl⟩ := Set.mem_mul.mp hm'
  exact ⟨p, hp, d, hd, rfl⟩

theorem BenderCore.normalizer_cartan_le [Finite K] (h : BenderCore q i 1 P t) (hP : IsPGroup 2 P)
    {x : K} (hx : x ∈ cartan P t) (hx1 : x ≠ 1) {g : K}
    (hg : g ∈ normalizer (cartan P t : Set K)) : g ∈ cartan P t ∨ g * t ∈ cartan P t := by
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  have hDP : ∀ y : K, y ∈ cartan P t → y ∈ P → y = 1 := by
    intro y hyD hyP
    have : y ∈ P ⊓ cartan P t := ⟨hyP, hyD⟩
    rw [h.inf_eq, Subgroup.mem_bot] at this
    exact this
  have hnormP : ∀ y ∈ borel P, ∀ a ∈ P, y * a * y⁻¹ ∈ P := fun y hy a ha =>
    (Subgroup.mem_normalizer_iff.mp hy a).mp ha
  have hxM : x ∈ borel P := cartan_le_borel P t hx
  have hgx : g * x * g⁻¹ ∈ cartan P t := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgx1 : g * x * g⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hkey : ∀ y ∈ cartan P t, y ≠ 1 → ∀ q' ∈ P, q' * y * q'⁻¹ ∈ cartan P t → q' = 1 := by
    intro y hy hy1 q' hq' hqy
    have hinvD : y⁻¹ * (q' * y * q'⁻¹) ∈ cartan P t :=
      (cartan P t).mul_mem ((cartan P t).inv_mem hy) hqy
    have hyM : y ∈ borel P := cartan_le_borel P t hy
    have hinvP : y⁻¹ * (q' * y * q'⁻¹) ∈ P := by
      have h3 : y⁻¹ * (q' * y * q'⁻¹) = (y⁻¹ * q' * y) * q'⁻¹ := by group
      rw [h3]
      have h4 : y⁻¹ * q' * y ∈ P := by
        have := hnormP y⁻¹ ((borel P).inv_mem hyM) q' hq'
        simpa using this
      exact P.mul_mem h4 (P.inv_mem hq')
    have h5 := hDP _ hinvD hinvP
    have h6 : q' * y = y * q' := by
      calc q' * y = (q' * y * q'⁻¹) * q' := by group
        _ = (y * (y⁻¹ * (q' * y * q'⁻¹))) * q' := by group
        _ = y * q' := by rw [h5, mul_one]
    exact h.eq_one_of_commute_cartan hP hy hy1 hq' h6
  by_cases hgM : g ∈ borel P
  · left
    obtain ⟨p, hp, d, hd, rfl⟩ := h.exists_mul_of_mem_borel hgM
    have hxd : x * d = d * x := h.cartan_comm hx hd
    have h1 : p * d * x * (p * d)⁻¹ = p * x * p⁻¹ := by
      calc p * d * x * (p * d)⁻¹ = p * (d * x * d⁻¹) * p⁻¹ := by group
        _ = p * x * p⁻¹ := by rw [← hxd]; group
    rw [h1] at hgx
    have hp1 : p = 1 := hkey x hx hx1 p hp hgx
    rw [hp1, one_mul]
    exact hd
  · right
    obtain ⟨p, hpP, m, hmM, rfl⟩ := h.bruhat hgM
    obtain ⟨q', hq', d, hd, rfl⟩ := h.exists_mul_of_mem_borel hmM
    have hxd : x * d = d * x := h.cartan_comm hx hd
    set x' := p * t * (q' * d) * x * (p * t * (q' * d))⁻¹ with hx'
    have hx'eq : t * (q' * x * q'⁻¹) * t = p⁻¹ * x' * p := by
      calc t * (q' * x * q'⁻¹) * t = t * (q' * (d * x * d⁻¹) * q'⁻¹) * t⁻¹ := by
            rw [hti, ← hxd]; group
        _ = p⁻¹ * (p * t * (q' * d) * x * (p * t * (q' * d))⁻¹) * p := by group
    have hx'D : x' ∈ cartan P t := hgx
    have hx'M : x' ∈ borel P := cartan_le_borel P t hx'D
    have hconjM : t * (q' * x * q'⁻¹) * t⁻¹ ∈ borel P := by
      rw [hti, hx'eq]
      exact (borel P).mul_mem ((borel P).mul_mem ((borel P).inv_mem (le_borel P hpP)) hx'M)
        (le_borel P hpP)
    have hq'xM : q' * x * q'⁻¹ ∈ borel P :=
      (borel P).mul_mem ((borel P).mul_mem (le_borel P hq') hxM) ((borel P).inv_mem (le_borel P hq'))
    have hqxD : q' * x * q'⁻¹ ∈ cartan P t :=
      Subgroup.mem_inf.mpr ⟨hq'xM, mem_conjugate_iff_mul_inv.mpr hconjM⟩
    have hq1 : q' = 1 := hkey x hx hx1 q' hq' hqxD
    subst hq1
    have hpx'D : p⁻¹ * x' * p ∈ cartan P t := by
      rw [← hx'eq]
      simpa using h.cartan_mul_mul hx
    have hp1' : p⁻¹ = 1 := hkey x' hx'D hgx1 p⁻¹ (P.inv_mem hpP) (by simpa using hpx'D)
    have hp1 : p = 1 := inv_eq_one.mp hp1'
    subst hp1
    have h7 : (1 * t * (1 * d)) * t = t * d * t := by group
    rw [h7]
    exact h.cartan_mul_mul hd

theorem BenderCore.exists_conj_cartan_of_odd [Finite K] {e : ℕ} (h : BenderCore q i e P t)
    (hP : IsPGroup 2 P) {A : Subgroup K} (hAM : A ≤ borel P) (hA : Odd (Nat.card A)) :
    ∃ q' ∈ P, ∀ a ∈ A, q' * a * q'⁻¹ ∈ cartan P t := by
  classical
  have hnormP : ∀ y ∈ borel P, ∀ a ∈ P, y * a * y⁻¹ ∈ P := fun y hy a ha =>
    (Subgroup.mem_normalizer_iff.mp hy a).mp ha
  have hPM : P ≤ borel P := le_borel P
  have hDM : cartan P t ≤ borel P := cartan_le_borel P t
  have : ((P.subgroupOf (borel P))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    change (g : K) * (n : K) * (g : K)⁻¹ ∈ P
    exact hnormP g g.2 n hn
  have hNp : IsPGroup 2 (P.subgroupOf (borel P)) :=
    hP.of_injective (Subgroup.subgroupOfEquivOfLe hPM).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPM).injective
  have hND : P.subgroupOf (borel P) ⊓ (cartan P t).subgroupOf (borel P) = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨x, hxM⟩ ⟨h1, h2⟩
    have hx : x ∈ P ⊓ cartan P t := ⟨h1, h2⟩
    rw [h.inf_eq, Subgroup.mem_bot] at hx
    exact Subgroup.mem_bot.mpr (Subtype.ext hx)
  have hsup : P.subgroupOf (borel P) ⊔ (cartan P t).subgroupOf (borel P) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPM hDM, h.sup_eq, Subgroup.subgroupOf_self]
  have hA' : Odd (Nat.card (A.subgroupOf (borel P))) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]
  obtain ⟨n, hn, hconj⟩ := exists_conj_mem_of_odd_card (G := ↥(borel P))
    (N := P.subgroupOf (borel P)) (D := (cartan P t).subgroupOf (borel P))
    (D₃ := (cartan P t).subgroupOf (borel P)) (A := A.subgroupOf (borel P)) hNp hND hsup le_rfl
    (fun d hd _ => hd) hA'
  refine ⟨(n : K), hn, fun a ha => ?_⟩
  have := hconj ⟨a, hAM ha⟩ ha
  exact this

theorem BenderCore.card_normalizer_cartan [Finite K] (h : BenderCore q i 1 P t) (hP : IsPGroup 2 P)
    {x : K} (hx : x ∈ cartan P t) (hx1 : x ≠ 1) :
    Nat.card (normalizer (cartan P t : Set K)) = 2 * Nat.card (cartan P t) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := h.sq_eq_one
  have ht1 : t ≠ 1 := by
    intro h1
    apply h.not_mem
    rw [h1]
    exact (borel P).one_mem
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact htt) ht1
  have htN : t ∈ normalizer (cartan P t : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have := h.cartan_mul_mul hy
      rw [hti]
      exact this
    · intro hy
      rw [hti] at hy
      have h1 := h.cartan_mul_mul hy
      have h2 : t * (t * y * t) * t = y := by
        calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
          _ = y := by rw [htt, one_mul, mul_one]
      rwa [h2] at h1
  have htD : t ∉ cartan P t := fun ht => h.not_mem (cartan_le_borel P t ht)
  have hsub : normalizer (cartan P t : Set K) = cartan P t ⊔ zpowers t := by
    apply le_antisymm
    · intro g hg
      rcases h.normalizer_cartan_le hP hx hx1 hg with hgD | hgt
      · exact Subgroup.mem_sup_left hgD
      · have : g = (g * t) * t⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgt)
          (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)))
    · exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr htN)
  have hDt : cartan P t ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyD, hyt⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyt
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · have : t ^ (2 * m) = 1 := by
        rw [zpow_mul, show (t ^ (2 : ℤ)) = 1 by rw [zpow_two]; exact htt, one_zpow]
      rw [this]
      exact Subgroup.one_mem _
    · exfalso
      have : t ^ (2 * m + 1) = t := by
        rw [zpow_add_one, zpow_mul, show (t ^ (2 : ℤ)) = 1 by rw [zpow_two]; exact htt, one_zpow,
          one_mul]
      rw [this] at hyD
      exact htD hyD
  rw [hsub, card_sup_eq_mul_of_le_normalizer (Subgroup.zpowers_le.mpr htN) hDt]
  rw [Nat.card_zpowers, hord]
  ring

end CartanCentralizer

end CFSG.GH74.Uniqueness.Bender
