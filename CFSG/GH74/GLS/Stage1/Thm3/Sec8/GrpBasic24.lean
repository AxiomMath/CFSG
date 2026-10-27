module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic3
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup


theorem GQ.exists_invariant_cyc4 {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {z : G}
    (hQ : GQ Q z) (h8 : Nat.card ↥Q = 8) {T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTQ : ∀ x ∈ T, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) :
    ∃ M : Subgroup G, M ≤ Q ∧ IsCyclic ↥M ∧ Nat.card ↥M = 4 ∧
      ∀ x ∈ T, ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
  classical
  have hz2 := hQ.z_sq
  have hz1 := hQ.z_ne
  have hTz : ∀ t ∈ T, t * z * t⁻¹ = z := by
    intro t ht
    have hmem : t * z * t⁻¹ ∈ Q := hTQ t ht z hQ.z_mem
    have h2 : (t * z * t⁻¹) * (t * z * t⁻¹) = 1 := by
      calc (t * z * t⁻¹) * (t * z * t⁻¹) = t * (z * z) * t⁻¹ := by group
        _ = 1 := by rw [hz2]; group
    rcases hQ.uniq _ hmem h2 with h | h
    · exfalso
      apply hz1
      have : z = t⁻¹ * (t * z * t⁻¹) * t := by group
      rw [this, h]; group
    · exact h
  set X : Subgroup G := Q ⊔ T with hX
  have hQX : Q ≤ X := le_sup_left
  have hTX : T ≤ X := le_sup_right
  have hTnorm : T ≤ normalizer (Q : Set G) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hTQ t ht q hq, fun hq => ?_⟩
    have := hTQ t⁻¹ (inv_mem ht) _ hq
    simpa [mul_assoc] using this
  have hXnorm : X ≤ normalizer (Q : Set G) := sup_le Subgroup.le_normalizer hTnorm
  have hXz : ∀ x ∈ X, x * z = z * x := by
    have hle : X ≤ centralizer ({z} : Set G) := by
      refine sup_le (fun q hq => ?_) (fun t ht => ?_)
      · exact mem_centralizer_singleton_iff.2 (hQ.z_central hq)
      · refine mem_centralizer_singleton_iff.2 ?_
        have := hTz t ht
        calc t * z = t * z * t⁻¹ * t := by group
          _ = z * t := by rw [this]
    intro x hx
    exact mem_centralizer_singleton_iff.1 (hle hx)
  have hX2 : IsPGroup 2 ↥X := by
    have h1 := card_sup_mul_card_inf' (A := Q) (B := T) hTnorm
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hT
    have hdvd : Nat.card ↥X ∣ 2 ^ (3 + b) := by
      have : Nat.card ↥X ∣ Nat.card ↥Q * Nat.card ↥T := by
        rw [← h1]; exact Dvd.intro _ rfl
      have e : Nat.card ↥Q * Nat.card ↥T = 2 ^ (3 + b) := by rw [h8, hb, pow_add]; norm_num
      rwa [e] at this
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card hc
  have hXfin : Finite ↥X := inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z' : ↥X := ⟨z, hQX hQ.z_mem⟩ with hz'
  have hz'c : z' ∈ center ↥X := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hXz g g.2)
  have hNnorm : (zpowers z').Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    have : g * z' ^ k * g⁻¹ = z' ^ k := by
      have hc : g * z' = z' * g := (mem_center_iff.1 hz'c) g
      calc g * z' ^ k * g⁻¹ = (g * z' * g⁻¹) ^ k := (conj_zpow).symm
        _ = z' ^ k := by rw [hc]; simp
    rw [this]; exact zpow_mem (mem_zpowers z') k
  set Qt : Subgroup ↥X := Q.subgroupOf X with hQt
  have hQtn : Qt.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hQt, mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.1 (hXnorm g.2) (n : G)).1 hn
    simpa using this
  set Qb : Subgroup (↥X ⧸ zpowers z') := Qt.map (QuotientGroup.mk' (zpowers z')) with hQb
  have hQbn : Qb.Normal := hQtn.map _ (QuotientGroup.mk'_surjective _)
  have hXq2 : IsPGroup 2 (↥X ⧸ zpowers z') := hX2.to_quotient _
  have : Group.IsNilpotent (↥X ⧸ zpowers z') := hXq2.isNilpotent
  have hzcard : Nat.card ↥(zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [pow_two] using hz2) hz1
  obtain ⟨q₀, hq₀Q, hq₀z⟩ : ∃ q ∈ Q, q ∉ zpowers z := by
    by_contra hcon
    push Not at hcon
    have hle : Q ≤ zpowers z := fun q hq => hcon q hq
    have := Subgroup.card_le_of_le hle
    omega
  have hQbne : Qb ≠ ⊥ := by
    intro hbot
    have hmem : (QuotientGroup.mk' (zpowers z')) (⟨q₀, hQX hq₀Q⟩ : ↥X) ∈ Qb :=
      ⟨⟨q₀, hQX hq₀Q⟩, (show (⟨q₀, hQX hq₀Q⟩ : ↥X) ∈ Q.subgroupOf X from mem_subgroupOf.2 hq₀Q), rfl⟩
    rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    apply hq₀z
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    exact mem_zpowers_iff.2 ⟨k, by simpa [hz'] using congrArg Subtype.val hk⟩
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := Qb) hQbne
  obtain ⟨w, hw1⟩ := (ne_bot_iff_exists_ne_one).1 hc
  have hwQb : (w : ↥X ⧸ zpowers z') ∈ Qb := w.2.1
  have hwc : (w : ↥X ⧸ zpowers z') ∈ center (↥X ⧸ zpowers z') := w.2.2
  obtain ⟨n, hnQt, hnw⟩ := hwQb
  have hnQ : (n : G) ∈ Q := mem_subgroupOf.1 (show n ∈ Q.subgroupOf X from hnQt)
  set q : G := (n : G) with hq
  have hqz : q ∉ zpowers z := by
    intro hqz
    apply hw1
    apply Subtype.ext
    show (w : ↥X ⧸ zpowers z') = 1
    rw [← hnw, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hqz
    exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa [hz', hq] using hk)⟩
  have hconj : ∀ t ∈ T, t * q * t⁻¹ * q⁻¹ ∈ zpowers z := by
    intro t ht
    have h1 := (mem_center_iff.1 hwc) (QuotientGroup.mk' (zpowers z') ⟨t, hTX ht⟩)
    rw [← hnw] at h1
    have h2 : (QuotientGroup.mk' (zpowers z')) (⟨t, hTX ht⟩ * n * ⟨t, hTX ht⟩⁻¹ * n⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      have : ((QuotientGroup.mk' (zpowers z')) ⟨t, hTX ht⟩) * (QuotientGroup.mk' (zpowers z')) n =
          (QuotientGroup.mk' (zpowers z')) n * ((QuotientGroup.mk' (zpowers z')) ⟨t, hTX ht⟩) := by
        simpa [map_mul] using h1
      rw [this]; group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h2
    exact mem_zpowers_iff.2 ⟨k, by simpa [hz', hq] using congrArg Subtype.val hk⟩
  have hq8 : q ^ 8 = 1 := by
    have := pow_card_of_mem hnQ
    rwa [h8] at this
  have hq1 : q ≠ 1 := fun h => hqz (h ▸ one_mem _)
  have hqz' : q ≠ z := fun h => hqz (h ▸ mem_zpowers z)
  have hqq : q * q ≠ 1 := by
    intro h
    rcases hQ.uniq q hnQ h with h' | h'
    · exact hq1 h'
    · exact hqz' h'
  have hord : orderOf q = 4 := by
    have hdvd : orderOf q ∣ 8 := orderOf_dvd_of_pow_eq_one hq8
    have h8' : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8'] at hdvd
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    interval_cases i
    · exfalso
      have : q = 1 := orderOf_eq_one_iff.1 (by simpa using hio)
      exact hq1 this
    · exfalso
      apply hqq
      have h2 : q ^ 2 = 1 := by
        have := pow_orderOf_eq_one q
        rw [hio] at this
        simpa using this
      simpa [pow_two] using h2
    · simpa using hio
    · exfalso
      have hcyc : Q = zpowers q := by
        apply (Subgroup.eq_of_le_of_card_ge (H := zpowers q) (K := Q) ?_ ?_).symm
        · rw [zpowers_le]; exact hnQ
        · rw [Nat.card_zpowers, hio, h8]; norm_num
      apply hQ.not_isCyclic
      rw [hcyc]; exact isCyclic_zpowers q
  have hq2 : q * q = z := by
    have h4 : (q * q) * (q * q) = 1 := by
      have : q ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one q
      simpa [pow_four_eq] using this
    rcases hQ.uniq (q * q) (mul_mem hnQ hnQ) h4 with h | h
    · exact absurd h hqq
    · exact h
  refine ⟨zpowers q, (zpowers_le).2 hnQ, isCyclic_zpowers q, by rw [Nat.card_zpowers, hord], ?_⟩
  intro t ht m hm
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hm
  have hconj' : t * q * t⁻¹ ∈ zpowers q := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hconj t ht)
    have : t * q * t⁻¹ = z ^ k * q := by
      calc t * q * t⁻¹ = (t * q * t⁻¹ * q⁻¹) * q := by group
        _ = z ^ k * q := by rw [← hk]
    rw [this]
    refine mul_mem (zpow_mem ?_ k) (mem_zpowers q)
    rw [← hq2]
    exact mul_mem (mem_zpowers q) (mem_zpowers q)
  have : t * q ^ j * t⁻¹ = (t * q * t⁻¹) ^ j := conj_zpow.symm
  rw [this]
  exact zpow_mem hconj' j


theorem GQ.sq_of_orderOf_four {G : Type*} [Group G] {Q : Subgroup G} {z : G} (hQ : GQ Q z) {w : G}
    (hw : w ∈ Q) (h4 : orderOf w = 4) : w * w = z := by
  have hw4 : (w * w) * (w * w) = 1 := by
    have : w ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one w
    simpa [pow_four_eq] using this
  have hww : w * w ≠ 1 := by
    intro h
    have : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rcases hQ.uniq (w * w) (mul_mem hw hw) hw4 with h | h
  · exact absurd h hww
  · exact h

theorem eq_or_inv_of_mem_zpowers_of_orderOf_four {G : Type*} [Group G] {w w' : G}
    (hw : orderOf w = 4) (hw' : orderOf w' = 4) (hmem : w' ∈ Subgroup.zpowers w) :
    w' = w ∨ w' = w⁻¹ := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hmem
  have h4 : w ^ 4 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hmod := zpow_mod_orderOf w j
  rw [hw] at hmod
  have hj : j % ((4 : ℕ) : ℤ) = 0 ∨ j % ((4 : ℕ) : ℤ) = 1 ∨ j % ((4 : ℕ) : ℤ) = 2 ∨
      j % ((4 : ℕ) : ℤ) = 3 := by omega
  rcases hj with h | h | h | h
  · exfalso
    rw [h, zpow_zero] at hmod
    rw [← hmod, orderOf_one] at hw'
    omega
  · left
    rw [h, zpow_one] at hmod
    exact hmod.symm
  · exfalso
    rw [h] at hmod
    have h2 : (w ^ j) ^ 2 = 1 := by
      rw [← hmod]
      calc (w ^ (2 : ℤ)) ^ 2 = w ^ 4 := by
            rw [← zpow_natCast, ← zpow_mul]; norm_num
        _ = 1 := h4
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hw'] at this
    omega
  · right
    rw [h] at hmod
    rw [← hmod]
    have : w ^ (3 : ℤ) = w⁻¹ := by
      have : w ^ (3 : ℤ) * w = 1 := by
        calc w ^ (3 : ℤ) * w = w ^ 4 := by
              rw [← zpow_add_one]; norm_num
          _ = 1 := h4
      exact eq_inv_of_mul_eq_one_left this
    exact this

theorem exists_order_four {G : Type*} [Group G] [Finite G] {V : Subgroup G} (hV : IsCyclic ↥V)
    (hV2 : IsPGroup 2 ↥V) (h4 : 4 ≤ Nat.card ↥V) : ∃ w ∈ V, orderOf w = 4 := by
  obtain ⟨g, hgV, hgen⟩ := exists_generator_of_cyclic hV
  have hgo : orderOf g = Nat.card ↥V := by rw [hgen, Nat.card_zpowers]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hV2
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 4 ∣ orderOf g := by
    rw [hgo, hk]
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_dvd_pow 2 hk2
  have hpos : orderOf g ≠ 0 := by rw [hgo]; exact (Nat.card_pos).ne'
  exact ⟨g ^ (orderOf g / 4), pow_mem hgV _, orderOf_pow_orderOf_div hpos hdvd⟩

theorem GQ.maxCyclic_of_index_two {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {z : G}
    (hQ : GQ Q z) {W : Subgroup G} (hW : 2 * Nat.card ↥W = Nat.card ↥Q) :
    ∀ C : Subgroup G, W ≤ C → C ≤ Q → IsCyclic ↥C → C = W := by
  intro C hWC hCQ hCc
  have h1 : Nat.card ↥W ∣ Nat.card ↥C := Subgroup.card_dvd_of_le hWC
  have h2 : Nat.card ↥C ∣ Nat.card ↥Q := Subgroup.card_dvd_of_le hCQ
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hWpos : 0 < Nat.card ↥W := Nat.card_pos
  have hab : a * b = 2 := by
    have : Nat.card ↥W * (a * b) = Nat.card ↥W * 2 := by
      calc Nat.card ↥W * (a * b) = (Nat.card ↥W * a) * b := by ring
        _ = Nat.card ↥C * b := by rw [← ha]
        _ = Nat.card ↥Q := hb.symm
        _ = 2 * Nat.card ↥W := hW.symm
        _ = Nat.card ↥W * 2 := by ring
    exact Nat.eq_of_mul_eq_mul_left hWpos this
  have ha12 : a = 1 ∨ a = 2 := by
    have : a ∣ 2 := Dvd.intro b hab
    rcases (Nat.dvd_prime Nat.prime_two).1 this with h | h <;> simp [h]
  rcases ha12 with h | h
  · rw [h, mul_one] at ha
    exact (Subgroup.eq_of_le_of_card_ge hWC (by omega)).symm
  · exfalso
    have hCQ' : C = Q := by
      apply Subgroup.eq_of_le_of_card_ge hCQ
      rw [ha, h]; omega
    exact hQ.not_isCyclic (hCQ' ▸ hCc)

theorem GQ.exists_invariant_maxCyclic {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {z : G}
    (hQ : GQ Q z) (hQ2 : IsPGroup 2 ↥Q) {T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTQ : ∀ x ∈ T, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) :
    ∃ W : Subgroup G, W ≤ Q ∧ IsCyclic ↥W ∧
      (∀ C : Subgroup G, W ≤ C → C ≤ Q → IsCyclic ↥C → C = W) ∧
      (∀ x ∈ T, ∀ w ∈ W, x * w * x⁻¹ ∈ W) ∧ 2 * Nat.card ↥W = Nat.card ↥Q := by
  classical
  obtain ⟨M, hMQ, hMc, hzM, hM4, hMi, hM⟩ := hQ.ex
  have hMcard : 2 * Nat.card ↥M = Nat.card ↥Q := by
    have := card_mul_relIndex_of_le hMQ
    rw [hMi] at this
    omega
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ2
  have h8le := hQ.eight_le_card
  by_cases h8 : Nat.card ↥Q = 8
  · obtain ⟨W, hWQ, hWc, hW4, hWT⟩ := GQ.exists_invariant_cyc4 hQ h8 hT hTQ
    exact ⟨W, hWQ, hWc, GQ.maxCyclic_of_index_two hQ (by omega), hWT, by omega⟩
  · have h16 : 16 ≤ Nat.card ↥Q := by
      have hk3 : 4 ≤ k := by
        by_contra hlt
        have h1 : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at h1
        omega
      have h2 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      norm_num at h2
      omega
    refine ⟨M, hMQ, hMc, GQ.maxCyclic_of_index_two hQ hMcard, ?_, hMcard⟩
    intro x hx m hm
    set D : Subgroup G := M.comap (MulAut.conj x⁻¹).toMonoidHom with hD
    have hmemD : ∀ y, y ∈ D ↔ x⁻¹ * y * x ∈ M := by
      intro y
      simp [hD]
    have hDQ : D ≤ Q := by
      intro y hy
      have h1 := (hmemD y).1 hy
      have := hTQ x hx _ (hMQ h1)
      simpa [mul_assoc] using this
    have hDc : IsCyclic ↥D := cyclic_comap_conj M hMc x⁻¹
    have hDcard : 2 * Nat.card ↥D = Nat.card ↥Q := by
      rw [hD, card_comap_conj]; exact hMcard
    have hDM : D = M := GQ.cyclic_unique hQ h16 hDQ hDc hDcard hMQ hMc hMcard
    have : x * m * x⁻¹ ∈ D := by
      rw [hmemD]
      have e : x⁻¹ * (x * m * x⁻¹) * x = m := by group
      rw [e]; exact hm
    rwa [hDM] at this

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
