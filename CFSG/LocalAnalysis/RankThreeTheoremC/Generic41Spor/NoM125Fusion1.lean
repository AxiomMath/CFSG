module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125Struct
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

namespace IsM125

private theorem aux_finite_sub {S : Subgroup G} (h : IsM125 p S) {H : Subgroup G} (hH : H ≤ S) :
    Finite H := by
  apply Nat.finite_of_card_ne_zero
  intro h0
  have hd : Nat.card H ∣ Nat.card S := Subgroup.card_dvd_of_le hH
  rw [h0, h.card] at hd
  exact pow_ne_zero 3 h.prime.ne_zero (zero_dvd_iff.mp hd)

private theorem aux_pow_eq_one_of_mem_Z {S : Subgroup G} (h : IsM125 p S) {z : G}
    (hz : z ∈ centralizer (S : Set G) ⊓ S) : z ^ p = 1 := by
  have hc := card_Z h
  have := pow_card_eq_one' (G := ↥(centralizer (S : Set G) ⊓ S)) (x := ⟨z, hz⟩)
  rw [hc] at this
  simpa using congrArg Subtype.val this

private theorem aux_exists_pow_eq_of_mem_Z {S : Subgroup G} (h : IsM125 p S) {w z : G}
    (hw : w ∈ centralizer (S : Set G) ⊓ S) (hw1 : w ≠ 1)
    (hz : z ∈ centralizer (S : Set G) ⊓ S) : ∃ m : ℕ, z = w ^ m := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf w = p := orderOf_eq_prime (aux_pow_eq_one_of_mem_Z h hw) hw1
  have hle : Subgroup.zpowers w ≤ centralizer (S : Set G) ⊓ S := Subgroup.zpowers_le.2 hw
  haveI : Finite ↥(centralizer (S : Set G) ⊓ S) := aux_finite_sub h inf_le_right
  have hcard : Nat.card (Subgroup.zpowers w) = p := by rw [Nat.card_zpowers, hord]
  have heq : Subgroup.zpowers w = centralizer (S : Set G) ⊓ S :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcard, card_Z h]))
  have hz' : z ∈ Subgroup.zpowers w := by
    rw [heq]
    exact hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz'
  have hne : (orderOf w : ℤ) ≠ 0 := by
    rw [hord]
    exact_mod_cast hp.ne_zero
  have hnn : 0 ≤ k % (orderOf w : ℤ) := Int.emod_nonneg _ hne
  refine ⟨(k % (orderOf w : ℤ)).toNat, ?_⟩
  rw [← hk, ← zpow_mod_orderOf, ← zpow_natCast, Int.toNat_of_nonneg hnn]

private theorem aux_exists_mem_not_E {S : Subgroup G} (h : IsM125 p S) :
    ∃ a ∈ S, a ∉ h.E := by
  by_contra hcon
  push Not at hcon
  have hEq : h.E = S := le_antisymm (E_le h) (fun a ha => hcon a ha)
  have h1 := card_E h
  rw [hEq, h.card] at h1
  have := Nat.pow_lt_pow_right h.prime.one_lt (show 2 < 3 by norm_num)
  omega

private theorem aux_exists_mem_E_not_Z {S : Subgroup G} (h : IsM125 p S) :
    ∃ e ∈ h.E, e ∉ centralizer (S : Set G) ⊓ S := by
  by_contra hcon
  push Not at hcon
  have hle : h.E ≤ centralizer (S : Set G) ⊓ S := fun e he => hcon e he
  haveI : Finite ↥(centralizer (S : Set G) ⊓ S) := aux_finite_sub h inf_le_right
  have h1 : Nat.card h.E ≤ Nat.card ↥(centralizer (S : Set G) ⊓ S) :=
    Subgroup.card_le_of_le hle
  rw [card_E h, card_Z h] at h1
  have := Nat.pow_lt_pow_right h.prime.one_lt (show 1 < 2 by norm_num)
  rw [pow_one] at this
  omega

private theorem aux_sup_zpowers_eq_E {S : Subgroup G} (h : IsM125 p S) {b : G} (hbE : b ∈ h.E)
    (hbZ : b ∉ centralizer (S : Set G) ⊓ S) :
    Subgroup.zpowers b ⊔ (centralizer (S : Set G) ⊓ S) = h.E := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hKE : Subgroup.zpowers b ⊔ (centralizer (S : Set G) ⊓ S) ≤ h.E :=
    sup_le (Subgroup.zpowers_le.2 hbE) (Z_le_E h)
  haveI : Finite ↥(Subgroup.zpowers b ⊔ (centralizer (S : Set G) ⊓ S)) :=
    aux_finite_sub h (hKE.trans (E_le h))
  haveI : Finite h.E := aux_finite_sub h (E_le h)
  have hZlt : centralizer (S : Set G) ⊓ S < Subgroup.zpowers b ⊔ (centralizer (S : Set G) ⊓ S) := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro heq
    apply hbZ
    have hbK : b ∈ Subgroup.zpowers b ⊔ (centralizer (S : Set G) ⊓ S) :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
    rw [← heq] at hbK
    exact hbK
  have hlt := Subgroup.card_lt_of_lt hZlt
  rw [card_Z h] at hlt
  have hd : Nat.card ↥(Subgroup.zpowers b ⊔ (centralizer (S : Set G) ⊓ S)) ∣ p ^ 2 := by
    rw [← card_E h]
    exact Subgroup.card_dvd_of_le hKE
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hd
  have hk2 : k = 2 := by
    by_contra hne
    have hle : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    rw [pow_one] at hle
    omega
  exact Subgroup.eq_of_le_of_card_ge hKE (le_of_eq (by rw [card_E h, hk', hk2]))

private theorem aux_E_conj_mem {S : Subgroup G} (h : IsM125 p S) {s e : G} (hs : s ∈ S)
    (he : e ∈ h.E) : s * e * s⁻¹ ∈ h.E := by
  refine (mem_E h).2 ⟨S.mul_mem (S.mul_mem hs ((mem_E h).1 he).1) (S.inv_mem hs), ?_⟩
  rw [conj_pow, ((mem_E h).1 he).2, mul_one, mul_inv_cancel]

private theorem aux_inv_conj_mem {A : Subgroup G} [Finite A] {n : G}
    (hn : ∀ x ∈ A, n * x * n⁻¹ ∈ A) : ∀ x ∈ A, n⁻¹ * x * n ∈ A := by
  let f : A → A := fun y => ⟨n * y * n⁻¹, hn y y.2⟩
  have hf : Function.Injective f := by
    intro y z hyz
    have h1 : n * (y : G) * n⁻¹ = n * (z : G) * n⁻¹ := congrArg Subtype.val hyz
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  intro x hx
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hf ⟨x, hx⟩
  have h2 : n * (y : G) * n⁻¹ = x := congrArg Subtype.val hy
  rw [← h2, show n⁻¹ * (n * (y : G) * n⁻¹) * n = (y : G) by group]
  exact y.2

private theorem aux_finite_sylow (K : Type*) [Group K] [Finite K] : Finite (Sylow p K) :=
  Finite.of_injective (fun P : Sylow p K => (P : Set K)) SetLike.coe_injective

private theorem aux_mem_smul_sylow {K : Type*} [Group K] {P : Sylow p K} {g x : K} :
    x ∈ ((g • P : Sylow p K) : Subgroup K) ↔ g⁻¹ * x * g ∈ (P : Subgroup K) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

private def aux_sylow_subgroupOf {P : Sylow p G} {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) :
    Sylow p H where
  toSubgroup := (P : Subgroup G).subgroupOf H
  isPGroup' := P.isPGroup'.comap_of_injective H.subtype H.subtype_injective
  is_maximal' := by
    intro Q hQ hle
    have hmap : Q.map H.subtype = (P : Subgroup G) := by
      refine P.is_maximal' (hQ.map H.subtype) ?_
      intro x hx
      exact Subgroup.mem_map.2 ⟨⟨x, hPH hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    calc Q = Subgroup.comap H.subtype (Q.map H.subtype) :=
          (Subgroup.comap_map_eq_self_of_injective H.subtype_injective Q).symm
      _ = Subgroup.comap H.subtype (P : Subgroup G) := by rw [hmap]
      _ = (P : Subgroup G).subgroupOf H := rfl

private theorem aux_mem_sylow_subgroupOf {P : Sylow p G} {H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) (x : H) :
    x ∈ (aux_sylow_subgroupOf hPH : Subgroup H) ↔ (x : G) ∈ (P : Subgroup G) :=
  Iff.rfl

theorem map_conj {S : Subgroup G} (h : IsM125 p S) (g : G) :
    IsM125 p (S.map (MulAut.conj g).toMonoidHom) := by
  set φ : G →* G := (MulAut.conj g).toMonoidHom with hφ
  have hinj : Function.Injective φ := fun x y hxy => (MulAut.conj g).injective hxy
  refine ⟨h.prime, h.odd, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj]
    exact h.card
  · intro hc
    apply h.nonab
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have ha : φ (a : G) ∈ S.map φ := Subgroup.mem_map_of_mem φ a.2
    have hb : φ (b : G) ∈ S.map φ := Subgroup.mem_map_of_mem φ b.2
    have key : φ (a : G) * φ (b : G) = φ (b : G) * φ (a : G) :=
      congrArg Subtype.val (hc.is_comm.comm ⟨φ (a : G), ha⟩ ⟨φ (b : G), hb⟩)
    rw [← map_mul, ← map_mul] at key
    exact hinj key
  · intro s hs
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hs
    rw [← map_pow, h.exp x hx, map_one]
  · obtain ⟨x, hx, hxp⟩ := h.big
    refine ⟨φ x, Subgroup.mem_map_of_mem φ hx, ?_⟩
    rw [← map_pow]
    intro h1
    apply hxp
    apply hinj
    rw [h1, map_one]

theorem exists_mem_act {S : Subgroup G} (h : IsM125 p S) {g : G}
    (hgZ : ∀ z ∈ centralizer (S : Set G) ⊓ S, g * z * g⁻¹ = z)
    (hgE : ∀ e ∈ h.E, g * e * g⁻¹ * e⁻¹ ∈ centralizer (S : Set G) ⊓ S) :
    ∃ s ∈ S, ∀ e ∈ h.E, g * e * g⁻¹ = s * e * s⁻¹ := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, haS, haE⟩ := aux_exists_mem_not_E h
  obtain ⟨b, hbE, hbZ⟩ := aux_exists_mem_E_not_Z h
  have hbS : b ∈ S := E_le h hbE
  have hbZ' : b ∉ centralizer (S : Set G) := fun hb => hbZ (Subgroup.mem_inf.2 ⟨hb, hbS⟩)
  obtain ⟨z, hz⟩ : ∃ z : G, z = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
  have hzZ : z ∈ centralizer (S : Set G) ⊓ S := by
    rw [hz]
    exact commutator_mem_Z h haS hbS
  have hz1 : z ≠ 1 := by
    intro h1
    apply haE
    apply mem_E_of_commute h hbE hbZ' haS
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [← hz, h1, one_mul]
  have hcomm : Commute a z := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hzZ).1 a haS
  have hab : a * b * a⁻¹ = z * b := by
    rw [hz]
    group
  obtain ⟨m, hm⟩ := aux_exists_pow_eq_of_mem_Z h hzZ hz1 (hgE b hbE)
  have hpow : ∀ k : ℕ, a ^ k * b * (a ^ k)⁻¹ = z ^ k * b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hcz : a * z ^ k * a⁻¹ = z ^ k := by
        rw [(hcomm.pow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
      calc a ^ (k + 1) * b * (a ^ (k + 1))⁻¹ = a * (a ^ k * b * (a ^ k)⁻¹) * a⁻¹ := by
            rw [pow_succ']
            group
        _ = a * (z ^ k * b) * a⁻¹ := by rw [ih]
        _ = (a * z ^ k * a⁻¹) * (a * b * a⁻¹) := by group
        _ = z ^ k * (z * b) := by rw [hcz, hab]
        _ = z ^ (k + 1) * b := by rw [pow_succ, mul_assoc]
  have hgb : g * b * g⁻¹ = a ^ m * b * (a ^ m)⁻¹ := by
    rw [hpow m, ← hm]
    group
  obtain ⟨s, hs⟩ : ∃ s : G, s = a ^ m := ⟨_, rfl⟩
  have hsS : s ∈ S := by
    rw [hs]
    exact S.pow_mem haS m
  rw [← hs] at hgb
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, ∀ x, x ∈ K ↔ g * x * g⁻¹ = s * x * s⁻¹ := by
    refine ⟨{ carrier := {x | g * x * g⁻¹ = s * x * s⁻¹}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun x => Iff.rfl⟩
    · rintro x y (hx : g * x * g⁻¹ = s * x * s⁻¹) (hy : g * y * g⁻¹ = s * y * s⁻¹)
      show g * (x * y) * g⁻¹ = s * (x * y) * s⁻¹
      calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (s * x * s⁻¹) * (s * y * s⁻¹) := by rw [hx, hy]
        _ = s * (x * y) * s⁻¹ := by group
    · simp
    · rintro x (hx : g * x * g⁻¹ = s * x * s⁻¹)
      show g * x⁻¹ * g⁻¹ = s * x⁻¹ * s⁻¹
      calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        _ = (s * x * s⁻¹)⁻¹ := by rw [hx]
        _ = s * x⁻¹ * s⁻¹ := by group
  have hbK : b ∈ K := (hK b).2 hgb
  have hZK : centralizer (S : Set G) ⊓ S ≤ K := by
    intro x hx
    have hsx : s * x = x * s := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).1 s hsS
    rw [hK, hgZ x hx, hsx]
    group
  have hEK : h.E ≤ K := by
    intro e he
    have he' : e ∈ Subgroup.zpowers b ⊔ (centralizer (S : Set G) ⊓ S) := by
      rw [aux_sup_zpowers_eq_E h hbE hbZ]
      exact he
    exact sup_le (Subgroup.zpowers_le.2 hbK) hZK he'
  exact ⟨s, hsS, fun e he => (hK e).1 (hEK he)⟩

variable [Finite G]

theorem exists_normalizer_act [Fact p.Prime] {S : Sylow p G} (h : IsM125 p (S : Subgroup G))
    {n : G} (hnE : ∀ e ∈ h.E, n * e * n⁻¹ ∈ h.E)
    (hnZ : ∀ z ∈ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G),
      n * z * n⁻¹ ∈ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G)) :
    ∃ m ∈ normalizer ((S : Subgroup G) : Set G), ∀ e ∈ h.E, m * e * m⁻¹ = n * e * n⁻¹ := by
  have hinvE : ∀ e ∈ h.E, n⁻¹ * e * n ∈ h.E := aux_inv_conj_mem hnE
  have hinvZ : ∀ z ∈ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G),
      n⁻¹ * z * n ∈ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G) :=
    aux_inv_conj_mem hnZ
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, ∀ x, x ∈ H ↔
      ((∀ e ∈ h.E, x * e * x⁻¹ ∈ h.E) ∧
        ∃ s ∈ (S : Subgroup G), ∀ e ∈ h.E, x * e * x⁻¹ = s * e * s⁻¹) := by
    refine ⟨{ carrier := {x | (∀ e ∈ h.E, x * e * x⁻¹ ∈ h.E) ∧
                ∃ s ∈ (S : Subgroup G), ∀ e ∈ h.E, x * e * x⁻¹ = s * e * s⁻¹}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun x => Iff.rfl⟩
    · rintro x y ⟨hx1, s, hsS, hx2⟩ ⟨hy1, t, htS, hy2⟩
      refine ⟨fun e he => ?_, s * t, (S : Subgroup G).mul_mem hsS htS, fun e he => ?_⟩
      · rw [show x * y * e * (x * y)⁻¹ = x * (y * e * y⁻¹) * x⁻¹ by group]
        exact hx1 _ (hy1 e he)
      · rw [show x * y * e * (x * y)⁻¹ = x * (y * e * y⁻¹) * x⁻¹ by group, hx2 _ (hy1 e he),
          hy2 e he]
        group
    · refine ⟨fun e he => ?_, 1, (S : Subgroup G).one_mem, fun e _ => ?_⟩
      · simpa using he
      · simp
    · rintro x ⟨hx1, s, hsS, hx2⟩
      refine ⟨fun e he => ?_, s⁻¹, (S : Subgroup G).inv_mem hsS, fun e he => ?_⟩
      · simp only [inv_inv]
        exact aux_inv_conj_mem hx1 e he
      · have he' : x⁻¹ * e * x ∈ h.E := aux_inv_conj_mem hx1 e he
        have h2 := hx2 _ he'
        rw [show x * (x⁻¹ * e * x) * x⁻¹ = e by group] at h2
        simp only [inv_inv]
        calc x⁻¹ * e * x = s⁻¹ * (s * (x⁻¹ * e * x) * s⁻¹) * s := by group
          _ = s⁻¹ * e * s := by rw [← h2]
  have hSH : (S : Subgroup G) ≤ H := by
    intro x hx
    rw [hH]
    exact ⟨fun e he => aux_E_conj_mem h hx he, x, hx, fun e _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Sylow p G, T = n • S := ⟨_, rfl⟩
  have hTmem : ∀ x, x ∈ (T : Subgroup G) ↔ n⁻¹ * x * n ∈ (S : Subgroup G) := by
    intro x
    rw [hT]
    exact aux_mem_smul_sylow
  have hTH : (T : Subgroup G) ≤ H := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ (S : Subgroup G), x = n * s * n⁻¹ :=
      ⟨n⁻¹ * x * n, (hTmem x).1 hx, by group⟩
    have hgZ : ∀ z ∈ centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G),
        n * s * n⁻¹ * z * (n * s * n⁻¹)⁻¹ = z := by
      intro z hz
      have hz' := hinvZ z hz
      have hc : s * (n⁻¹ * z * n) = (n⁻¹ * z * n) * s :=
        Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz').1 s hs
      calc n * s * n⁻¹ * z * (n * s * n⁻¹)⁻¹
          = n * (s * (n⁻¹ * z * n) * s⁻¹) * n⁻¹ := by group
        _ = n * ((n⁻¹ * z * n) * s * s⁻¹) * n⁻¹ := by rw [hc]
        _ = z := by group
    have hgE : ∀ e ∈ h.E, n * s * n⁻¹ * e * (n * s * n⁻¹)⁻¹ * e⁻¹ ∈
        centralizer ((S : Subgroup G) : Set G) ⊓ (S : Subgroup G) := by
      intro e he
      have he' := hinvE e he
      have hc := commutator_mem_Z h hs (E_le h he')
      have := hnZ _ hc
      convert this using 1
      group
    obtain ⟨s'', hs'', hconj⟩ := exists_mem_act h (g := n * s * n⁻¹) hgZ hgE
    rw [hH]
    refine ⟨fun e he => ?_, s'', hs'', hconj⟩
    rw [show n * s * n⁻¹ * e * (n * s * n⁻¹)⁻¹ = n * (s * (n⁻¹ * e * n) * s⁻¹) * n⁻¹ by group]
    exact hnE _ (aux_E_conj_mem h hs (hinvE e he))
  haveI : Finite (Sylow p H) := aux_finite_sylow H
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq (↥H) (aux_sylow_subgroupOf hTH)
    (aux_sylow_subgroupOf hSH)
  have hw1 : ∀ x ∈ (T : Subgroup G), (w : G) * x * (w : G)⁻¹ ∈ (S : Subgroup G) := by
    intro x hx
    have hxH : x ∈ H := hTH hx
    have hy : (⟨x, hxH⟩ : H) ∈ (aux_sylow_subgroupOf hTH : Subgroup H) :=
      (aux_mem_sylow_subgroupOf hTH ⟨x, hxH⟩).2 hx
    have h1 : w * (⟨x, hxH⟩ : H) * w⁻¹ ∈
        ((w • aux_sylow_subgroupOf hTH : Sylow p H) : Subgroup H) := by
      rw [aux_mem_smul_sylow, show w⁻¹ * (w * (⟨x, hxH⟩ : H) * w⁻¹) * w = ⟨x, hxH⟩ by group]
      exact hy
    rw [hw] at h1
    exact (aux_mem_sylow_subgroupOf hSH _).1 h1
  have hw2 : ∀ z ∈ (S : Subgroup G), (w : G)⁻¹ * z * (w : G) ∈ (T : Subgroup G) := by
    intro z hz
    have hzH : z ∈ H := hSH hz
    have hy : (⟨z, hzH⟩ : H) ∈ (aux_sylow_subgroupOf hSH : Subgroup H) :=
      (aux_mem_sylow_subgroupOf hSH ⟨z, hzH⟩).2 hz
    rw [← hw, aux_mem_smul_sylow] at hy
    exact (aux_mem_sylow_subgroupOf hTH _).1 hy
  obtain ⟨-, s₀, hs₀, hw2'⟩ := (hH (w : G)).1 w.2
  refine ⟨s₀⁻¹ * (w : G) * n, ?_, ?_⟩
  · rw [mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      have ht : n * x * n⁻¹ ∈ (T : Subgroup G) :=
        (hTmem _).2 (by
          rw [show n⁻¹ * (n * x * n⁻¹) * n = x by group]
          exact hx)
      have hz := hw1 _ ht
      rw [show s₀⁻¹ * (w : G) * n * x * (s₀⁻¹ * (w : G) * n)⁻¹
          = s₀⁻¹ * ((w : G) * (n * x * n⁻¹) * (w : G)⁻¹) * s₀ by group]
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hs₀) hz)
        hs₀
    · intro hx
      have hz : (w : G) * (n * x * n⁻¹) * (w : G)⁻¹ ∈ (S : Subgroup G) := by
        rw [show (w : G) * (n * x * n⁻¹) * (w : G)⁻¹
            = s₀ * (s₀⁻¹ * (w : G) * n * x * (s₀⁻¹ * (w : G) * n)⁻¹) * s₀⁻¹ by group]
        exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs₀ hx)
          ((S : Subgroup G).inv_mem hs₀)
      have h4 : n * x * n⁻¹ ∈ (T : Subgroup G) := by
        have h5 := hw2 _ hz
        rwa [show (w : G)⁻¹ * ((w : G) * (n * x * n⁻¹) * (w : G)⁻¹) * (w : G) = n * x * n⁻¹ by
          group] at h5
      have h6 := (hTmem _).1 h4
      rwa [show n⁻¹ * (n * x * n⁻¹) * n = x by group] at h6
  · intro e he
    have hw_e := hw2' _ (hnE e he)
    calc s₀⁻¹ * (w : G) * n * e * (s₀⁻¹ * (w : G) * n)⁻¹
        = s₀⁻¹ * ((w : G) * (n * e * n⁻¹) * (w : G)⁻¹) * s₀ := by group
      _ = s₀⁻¹ * (s₀ * (n * e * n⁻¹) * s₀⁻¹) * s₀ := by rw [hw_e]
      _ = n * e * n⁻¹ := by group

end IsM125

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125
