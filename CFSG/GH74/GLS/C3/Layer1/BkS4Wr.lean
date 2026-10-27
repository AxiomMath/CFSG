module

public import CFSG.GH74.GLS.C3.Layer1.BkS4Core

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.GH74.GLS.C3.Layer1.Back

variable {G : Type} [Group G]

theorem IsD8.central_eq {P : Subgroup G} (h : IsD8 P) {z : G} (hzP : z ∈ P) (hz1 : z ≠ 1)
    (hzc : ∀ p ∈ P, p * z = z * p) : ∀ w ∈ P, (∀ p ∈ P, p * w = w * p) → w = 1 ∨ w = z := by
  obtain ⟨z₀, hz₀P, hz₀1, -, hz₀c, hz₀u⟩ := h.exists_z
  have hzz₀ : z = z₀ := (hz₀u z hzP hzc).resolve_left hz1
  rw [hzz₀]
  exact hz₀u

theorem eq_of_mul_eq_of_inf_eq_bot {A B : Subgroup G} (hd : A ⊓ B = ⊥) {a a' b b' : G} (ha : a ∈ A)
    (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem ha') ha, by rw [h1]; exact B.mul_mem hb' (B.inv_mem hb)⟩
  rw [hd, Subgroup.mem_bot] at h2
  have h3 : a = a' := by
    have := mul_eq_one_iff_eq_inv.1 h2
    exact (inv_injective this).symm
  refine ⟨h3, ?_⟩
  rw [h3] at h
  exact mul_left_cancel h

theorem IsD8.exists_four_containing [Finite G] {P : Subgroup G} (h : IsD8 P) {p : G} (hpP : p ∈ P)
    (hp2 : p * p = 1) :
    ∃ D : Subgroup G, D ≤ P ∧ CFSG.IsElementaryAbelian 2 ↥D ∧ Nat.card ↥D = 4 ∧ p ∈ D := by
  obtain ⟨z, hzP, hz1, hzz, hzc, hzu⟩ := h.exists_z
  obtain ⟨s, hsP, hs2, p0, hp0P, hsp0⟩ := h.exists_noncentral_involution
  have key : ∀ d ∈ P, d * d = 1 → d ≠ 1 → d ≠ z →
      zpowers d ⊔ zpowers z ≤ P ∧ CFSG.IsElementaryAbelian 2 ↥(zpowers d ⊔ zpowers z) ∧
        Nat.card ↥(zpowers d ⊔ zpowers z) = 4 := by
    intro d hdP hd2 hd1 hdz
    have hcomm : ∀ x ∈ zpowers d, ∀ y ∈ zpowers z, x * y = y * x := by
      intro x hx y hy
      rcases mem_zpowers_of_sq hd2 hx with rfl | rfl
      · simp
      · rcases mem_zpowers_of_sq hzz hy with rfl | rfl
        · simp
        · exact hzc _ hdP
    have hdisj : zpowers d ⊓ zpowers z = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rcases mem_zpowers_of_sq hd2 hy.1 with rfl | rfl
      · exact one_mem _
      · rcases mem_zpowers_of_sq hzz hy.2 with h1 | h1
        · exact absurd h1 hd1
        · exact absurd h1 hdz
    have hdcard : Nat.card ↥(zpowers d) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hd2) hd1]
    have hzcard : Nat.card ↥(zpowers z) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hzz) hz1]
    refine ⟨sup_le (zpowers_le.2 hdP) (zpowers_le.2 hzP),
      isElementaryAbelian_sup_of_commute (isElementaryAbelian_zpowers_of_sq hd2)
        (isElementaryAbelian_zpowers_of_sq hzz) hcomm, ?_⟩
    rw [card_sup_of_commute_of_disjoint hcomm hdisj, hdcard, hzcard]
  by_cases hp : p ≠ 1 ∧ p ≠ z
  · obtain ⟨h1, h2, h3⟩ := key p hpP hp2 hp.1 hp.2
    exact ⟨_, h1, h2, h3, Subgroup.mem_sup_left (mem_zpowers p)⟩
  · have hs1 : s ≠ 1 := by
      intro h1
      apply hsp0
      rw [h1]
      simp
    have hsz : s ≠ z := by
      intro h1
      apply hsp0
      rw [h1]
      exact (hzc p0 hp0P).symm
    obtain ⟨h1, h2, h3⟩ := key s hsP hs2 hs1 hsz
    refine ⟨_, h1, h2, h3, ?_⟩
    rw [not_and_or, not_not, not_not] at hp
    rcases hp with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_sup_right (mem_zpowers p)

theorem card_le_six_of_swap [Finite G] {P P' F : Subgroup G} (hP : IsD8 P)
    (hcomm : ∀ p ∈ P, ∀ q ∈ P', p * q = q * p) (hdisj : P ⊓ P' = ⊥) {e : G}
    (he1 : ∀ p ∈ P, e * p * e⁻¹ ∈ P') (he2 : ∀ q ∈ P', e * q * e⁻¹ ∈ P) (hF : F ≤ P ⊔ P')
    (hFe : ∀ c ∈ F, c * e = e * c) (hFsq : ∀ c ∈ F, c * c = 1) : Nat.card ↥F ≤ 6 := by
  obtain ⟨ε⟩ := hP
  have key : ∀ s : Finset (DihedralGroup 4), (∀ x ∈ s, x * x = 1) → s.card ≤ 6 := by
    decide +kernel
  have hdec : ∀ c : ↥F, ∃ p ∈ P, ∃ q ∈ P', (c : G) = p * q := fun c =>
    mem_sup_of_commute hcomm (hF c.2)
  choose pf hpf qf hqf hc using hdec
  have hswap : ∀ c : ↥F, pf c = e * qf c * e⁻¹ ∧ qf c = e * pf c * e⁻¹ := by
    intro c
    have h1 : e * (c : G) * e⁻¹ = c := by
      rw [← hFe c c.2]
      group
    have h2 : pf c * qf c = (e * qf c * e⁻¹) * (e * pf c * e⁻¹) := by
      calc pf c * qf c = c := (hc c).symm
        _ = e * (c : G) * e⁻¹ := h1.symm
        _ = e * (pf c * qf c) * e⁻¹ := by rw [← hc c]
        _ = (e * pf c * e⁻¹) * (e * qf c * e⁻¹) := by group
        _ = (e * qf c * e⁻¹) * (e * pf c * e⁻¹) :=
          (hcomm _ (he2 _ (hqf c)) _ (he1 _ (hpf c))).symm
    exact eq_of_mul_eq_of_inf_eq_bot hdisj (hpf c) (he2 _ (hqf c)) (hqf c) (he1 _ (hpf c)) h2
  have hsq : ∀ c : ↥F, pf c * pf c = 1 := by
    intro c
    have h1 : (c : G) * c = 1 := hFsq c c.2
    rw [hc c] at h1
    have h2 : pf c * pf c * (qf c * qf c) = 1 * 1 := by
      calc pf c * pf c * (qf c * qf c) = pf c * (pf c * qf c) * qf c := by group
        _ = pf c * (qf c * pf c) * qf c := by rw [hcomm _ (hpf c) _ (hqf c)]
        _ = pf c * qf c * (pf c * qf c) := by group
        _ = 1 * 1 := by rw [h1]; simp
    exact (eq_of_mul_eq_of_inf_eq_bot hdisj (P.mul_mem (hpf c) (hpf c)) (one_mem _)
      (P'.mul_mem (hqf c) (hqf c)) (one_mem _) h2).1
  let f : ↥F → DihedralGroup 4 := fun c => ε ⟨pf c, hpf c⟩
  have hf : Function.Injective f := by
    intro c c' hcc'
    have h1 : (⟨pf c, hpf c⟩ : ↥P) = ⟨pf c', hpf c'⟩ := ε.injective hcc'
    have h2 : pf c = pf c' := congrArg Subtype.val h1
    have h3 : qf c = qf c' := by rw [(hswap c).2, (hswap c').2, h2]
    apply Subtype.ext
    rw [hc c, hc c', h2, h3]
  have : Fintype ↥F := Fintype.ofFinite _
  have hk := key (Finset.univ.image f) (by
    intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    show ε ⟨pf c, hpf c⟩ * ε ⟨pf c, hpf c⟩ = 1
    rw [← map_mul]
    have : (⟨pf c, hpf c⟩ : ↥P) * ⟨pf c, hpf c⟩ = 1 := Subtype.ext (hsq c)
    rw [this, map_one])
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ] at hk
  simpa [Nat.card_eq_fintype_card] using hk

theorem mem_of_pow_three_mem {S T : Subgroup G} (hS : IsPGroup 2 ↥S) {n : G} (hn : n ∈ S)
    (h3 : n ^ 3 ∈ T) : n ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS) ⟨n, hn⟩
  have hk' : orderOf n = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (⟨n, hn⟩ : ↥S)
  have hcop : Nat.Coprime 3 (orderOf n) := by
    rw [hk']
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact T.pow_mem h3 m

namespace Sec4Core

variable {a : G} {P Q T S : Subgroup G}

theorem conj_fwd (h : Sec4Core a P Q T S) {X : Subgroup G}
    (hXn : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) {y : G} (hy : y ∈ X) :
    a * y * a⁻¹ ∈ conjugate X a := by
  rw [mem_conjugate_iff']
  have := hXn (a * a) h.a_sq_mem y hy
  have e : a * (a * y * a⁻¹) * a⁻¹ = a * a * y * (a * a)⁻¹ := by group
  rw [e]
  exact this

theorem central_T_cases [Finite G] (h : Sec4Core a P Q T S) (hTeq : T = P ⊔ conjugate P a)
    {z x : G} (hzP : z ∈ P) (hz1 : z ≠ 1) (hzc : ∀ p ∈ P, p * z = z * p)
    (hxPa : x ∈ conjugate P a) (hx1 : x ≠ 1) (hxc : ∀ g ∈ conjugate P a, g * x = x * g)
    {w : G} (hwT : w ∈ T) (hw1 : w ≠ 1) (hwc : ∀ t ∈ T, t * w = w * t) :
    w = z ∨ w = x ∨ w = z * x := by
  have hPaT : conjugate P a ≤ T := h.conj_le h.P_le
  have hcomm := h.comm_P_conj
  rw [hTeq] at hwT
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hcomm hwT
  have hpc : ∀ p' ∈ P, p' * p = p * p' := by
    intro p' hp'
    have h1 := hwc p' (h.P_le hp')
    have h2 : q * p' = p' * q := (hcomm p' hp' q hq).symm
    calc p' * p = (p' * (p * q)) * q⁻¹ := by group
      _ = ((p * q) * p') * q⁻¹ := by rw [h1]
      _ = p * (q * p') * q⁻¹ := by group
      _ = p * (p' * q) * q⁻¹ := by rw [h2]
      _ = p * p' := by group
  have hqc : ∀ g ∈ conjugate P a, g * q = q * g := by
    intro g hg
    have h1 := hwc g (hPaT hg)
    have h2 : g * p = p * g := (hcomm p hp g hg).symm
    have h3 : p * (g * q) = p * (q * g) := by
      calc p * (g * q) = (p * g) * q := by group
        _ = (g * p) * q := by rw [h2]
        _ = g * (p * q) := by group
        _ = (p * q) * g := h1
        _ = p * (q * g) := by group
    exact mul_left_cancel h3
  have hp' := IsD8.central_eq h.P_d8 hzP hz1 hzc p hp hpc
  have hq' := IsD8.central_eq (h.P_d8.conjugate a) hxPa hx1 hxc q hq hqc
  rcases hp' with h1 | h1 <;> rcases hq' with h2 | h2
  · exact (hw1 (by rw [h1, h2]; simp)).elim
  · right; left; rw [h1, h2]; simp
  · left; rw [h1, h2]; simp
  · right; right; rw [h1, h2]

theorem mem_T_or_of_normalizer [Finite G] (h : Sec4Core a P Q T S) (hTeq : T = P ⊔ conjugate P a)
    {z x : G} (hzP : z ∈ P) (hz1 : z ≠ 1) (hzc : ∀ p ∈ P, p * z = z * p)
    (hxPa : x ∈ conjugate P a) (hx1 : x ≠ 1) (hx2 : x * x = 1) (hxT : ∀ t ∈ T, x * t = t * x)
    (hza : a * x * a⁻¹ = z) (hcentx : ∀ s ∈ S, s * x = x * s → s ∈ T)
    {n : G} (hnS : n ∈ S) (hnN : n ∈ normalizer (T : Set G)) : n ∈ T ∨ a⁻¹ * n ∈ T := by
  have hPaT : conjugate P a ≤ T := h.conj_le h.P_le
  have hxT' : x ∈ T := hPaT hxPa
  have hzT : z ∈ T := h.P_le hzP
  have hcomm := h.comm_P_conj
  have hzcT : ∀ t ∈ T, t * z = z * t := by
    intro t ht
    rw [hTeq] at ht
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hcomm ht
    calc p * q * z = p * (q * z) := by group
      _ = p * (z * q) := by rw [← hcomm z hzP q hq]
      _ = (p * z) * q := by group
      _ = (z * p) * q := by rw [hzc p hp]
      _ = z * (p * q) := by group
  have hxc : ∀ g ∈ conjugate P a, g * x = x * g := fun g hg => (hxT g (hPaT hg)).symm
  have hzx : z * x = x * z := (hzcT x hxT').symm
  have hn_conj : ∀ u ∈ T, n * u * n⁻¹ ∈ T := fun u hu => (Subgroup.mem_normalizer_iff.1 hnN u).1 hu
  have hn_conj_inv : ∀ u ∈ T, n⁻¹ * u * n ∈ T := by
    intro u hu
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hnN) u).1 hu
    simpa using this
  have hcl_of : ∀ u ∈ T, u ≠ 1 → (∀ t ∈ T, t * u = u * t) →
      (n * u * n⁻¹ = z ∨ n * u * n⁻¹ = x ∨ n * u * n⁻¹ = z * x) := by
    intro u hu hu1 huc
    refine h.central_T_cases hTeq hzP hz1 hzc hxPa hx1 hxc (hn_conj u hu) ?_ ?_
    · intro h0
      apply hu1
      have : u = n⁻¹ * (n * u * n⁻¹) * n := by group
      rw [this, h0]
      group
    · intro t ht
      calc t * (n * u * n⁻¹) = n * ((n⁻¹ * t * n) * u) * n⁻¹ := by group
        _ = n * (u * (n⁻¹ * t * n)) * n⁻¹ := by rw [huc _ (hn_conj_inv t ht)]
        _ = (n * u * n⁻¹) * t := by group
  have hnS' : a⁻¹ * n ∈ S := S.mul_mem (S.inv_mem h.a_mem) hnS
  rcases hcl_of x hxT' hx1 (fun t ht => (hxT t ht).symm) with hw | hw | hw
  ·
    right
    have e1 : a⁻¹ * (n * x * n⁻¹) * a = x := by
      rw [hw, ← hza]
      group
    refine hcentx _ hnS' ?_
    calc a⁻¹ * n * x = (a⁻¹ * (n * x * n⁻¹) * a) * (a⁻¹ * n) := by group
      _ = x * (a⁻¹ * n) := by rw [e1]
  · left
    refine hcentx n hnS ?_
    calc n * x = (n * x * n⁻¹) * n := by group
      _ = x * n := by rw [hw]
  · exfalso
    have hnT : n ∈ T → False := by
      intro hnT
      have h1 : n * x * n⁻¹ = x := by
        rw [(hxT n hnT).symm]
        group
      rw [h1] at hw
      have h2 : z * x = 1 * x := by rw [← hw, one_mul]
      exact hz1 (mul_right_cancel h2)
    rcases hcl_of z hzT hz1 hzcT with hv | hv | hv
    ·
      apply hnT
      have e1 : a⁻¹ * n * a * x * (a⁻¹ * n * a)⁻¹ = x := by
        calc a⁻¹ * n * a * x * (a⁻¹ * n * a)⁻¹ = a⁻¹ * (n * (a * x * a⁻¹) * n⁻¹) * a := by group
          _ = a⁻¹ * (n * z * n⁻¹) * a := by rw [hza]
          _ = a⁻¹ * z * a := by rw [hv]
          _ = x := by rw [← hza]; group
      have hc : (a⁻¹ * n * a) * x = x * (a⁻¹ * n * a) := by
        calc (a⁻¹ * n * a) * x = (a⁻¹ * n * a * x * (a⁻¹ * n * a)⁻¹) * (a⁻¹ * n * a) := by group
          _ = x * (a⁻¹ * n * a) := by rw [e1]
      have hmem : a⁻¹ * n * a ∈ T :=
        hcentx _ (S.mul_mem hnS' h.a_mem) hc
      have := h.a_norm hmem
      have e : a * (a⁻¹ * n * a) * a⁻¹ = n := by group
      rwa [e] at this
    ·
      apply hnT
      have e2 : n * (n * x * n⁻¹) * n⁻¹ = z := by
        rw [hw]
        calc n * (z * x) * n⁻¹ = (n * z * n⁻¹) * (n * x * n⁻¹) := by group
          _ = x * (z * x) := by rw [hv, hw]
          _ = x * (x * z) := by rw [hzx]
          _ = (x * x) * z := by group
          _ = z := by rw [hx2, one_mul]
      have e3 : n * (n * (n * x * n⁻¹) * n⁻¹) * n⁻¹ = x := by
        rw [e2, hv]
      have hc : (n * (n * n)) * x = x * (n * (n * n)) := by
        calc (n * (n * n)) * x = (n * (n * (n * x * n⁻¹) * n⁻¹) * n⁻¹) * (n * (n * n)) := by group
          _ = x * (n * (n * n)) := by rw [e3]
      refine mem_of_pow_three_mem h.S_pgroup hnS ?_
      rw [pow_three]
      exact hcentx _ (S.mul_mem hnS (S.mul_mem hnS hnS)) hc
    ·
      have hzx' : z = x := by
        have h1 : n * z * n⁻¹ = n * x * n⁻¹ := by rw [hv, hw]
        exact mul_left_cancel (mul_right_cancel h1)
      have hxP : x ∈ P ⊓ conjugate P a := ⟨hzx' ▸ hzP, hxPa⟩
      rw [h.P_inf_conj, Subgroup.mem_bot] at hxP
      exact hx1 hxP

theorem le_T_of_elementary [Finite G] (h : Sec4Core a P Q T S) (hTeq : T = P ⊔ conjugate P a)
    (hS : ∀ n ∈ S, n ∈ normalizer (T : Set G) → n ∈ T ∨ a⁻¹ * n ∈ T)
    {E : Subgroup G} (hEN : ∀ e ∈ E, e ∈ S ∧ e ∈ normalizer (T : Set G))
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE16 : 13 ≤ Nat.card ↥E) : E ≤ T := by
  by_contra hnot
  obtain ⟨e, heE, heT⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  have hPaT : conjugate P a ≤ T := h.conj_le h.P_le
  obtain ⟨hEc, hEs⟩ := forall_of_isElementaryAbelian hEel
  have hae : a⁻¹ * e ∈ T := (hS e (hEN e heE).1 (hEN e heE).2).resolve_left heT
  have hEF : (E : Set G) ⊆ ((E ⊓ T : Subgroup G) : Set G) ∪
      ((fun c => c * e) '' ((E ⊓ T : Subgroup G) : Set G)) := by
    intro y hy
    rcases hS y (hEN y hy).1 (hEN y hy).2 with hyT | hyT
    · left
      exact ⟨hy, hyT⟩
    · right
      refine ⟨y * e⁻¹, ⟨E.mul_mem hy (E.inv_mem heE), ?_⟩, by simp⟩
      have h1 : (a⁻¹ * y) * (a⁻¹ * e)⁻¹ ∈ T := T.mul_mem hyT (T.inv_mem hae)
      have h2 := h.a_norm h1
      have e' : a * ((a⁻¹ * y) * (a⁻¹ * e)⁻¹) * a⁻¹ = y * e⁻¹ := by group
      rwa [e'] at h2
  have hcardE : Nat.card ↥E ≤ 2 * Nat.card ↥(E ⊓ T) := by
    have h1 : Nat.card ↥E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
    have h2 : Nat.card ↥(E ⊓ T) = ((E ⊓ T : Subgroup G) : Set G).ncard :=
      Nat.card_coe_set_eq ((E ⊓ T : Subgroup G) : Set G)
    have h3 : (E : Set G).ncard ≤ (((E ⊓ T : Subgroup G) : Set G) ∪
        ((fun c => c * e) '' ((E ⊓ T : Subgroup G) : Set G))).ncard :=
      Set.ncard_le_ncard hEF (Set.toFinite _)
    have h4 := Set.ncard_union_le ((E ⊓ T : Subgroup G) : Set G)
      ((fun c => c * e) '' ((E ⊓ T : Subgroup G) : Set G))
    have h5 : ((fun c => c * e) '' ((E ⊓ T : Subgroup G) : Set G)).ncard ≤
        ((E ⊓ T : Subgroup G) : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
    omega
  have hFle : Nat.card ↥(E ⊓ T) ≤ 6 := by
    refine card_le_six_of_swap h.P_d8 h.comm_P_conj h.P_inf_conj (e := e) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      have h1 : (a⁻¹ * e) * p * (a⁻¹ * e)⁻¹ ∈ P := h.P_norm _ hae p hp
      have h2 := h.conj_fwd h.P_norm h1
      have e' : a * ((a⁻¹ * e) * p * (a⁻¹ * e)⁻¹) * a⁻¹ = e * p * e⁻¹ := by group
      rwa [e'] at h2
    · intro q hq
      have h1 : (a⁻¹ * e) * q * (a⁻¹ * e)⁻¹ ∈ conjugate P a := h.conj_norm h.P_norm _ hae q hq
      have h2 := mem_conjugate_iff'.1 h1
      have e' : a * ((a⁻¹ * e) * q * (a⁻¹ * e)⁻¹) * a⁻¹ = e * q * e⁻¹ := by group
      rwa [e'] at h2
    · rw [← hTeq]
      exact inf_le_right
    · intro c hc
      exact hEc c hc.1 e heE
    · intro c hc
      exact hEs c hc.1
  omega

theorem exists_mem_normalizer_not_mem [Finite G] {S N : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hNS : N ≤ S) (hne : N ≠ S) :
    ∃ n ∈ S, n ∉ N ∧ ∀ y ∈ N, n * y * n⁻¹ ∈ N ∧ n⁻¹ * y * n ∈ N := by
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  have hH : N.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h0 => hne ?_
    exact le_antisymm hNS (Subgroup.subgroupOf_eq_top.1 h0)
  have hlt := Group.normalizerCondition_of_isNilpotent (N.subgroupOf S) hH
  obtain ⟨n, hn, hnH⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨(n : G), n.2, fun hnN => hnH hnN, fun y hy => ⟨?_, ?_⟩⟩
  · have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨y, hNS hy⟩).1 hy
    exact h1
  · have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) ⟨y, hNS hy⟩).1 hy
    have h2 := Subgroup.mem_subgroupOf.1 h1
    simpa using h2

theorem normalizer_T_eq [Finite G] (h : Sec4Core a P Q T S) (hTeq : T = P ⊔ conjugate P a)
    (hS : ∀ n ∈ S, n ∈ normalizer (T : Set G) → n ∈ T ∨ a⁻¹ * n ∈ T) :
    ∀ s ∈ S, s ∈ normalizer (T : Set G) := by
  have hPaT : conjugate P a ≤ T := h.conj_le h.P_le
  have hcomm := h.comm_P_conj
  by_contra hcon
  push Not at hcon
  obtain ⟨s0, hs0S, hs0N⟩ := hcon
  have hN₁S : S ⊓ normalizer (T : Set G) ≤ S := inf_le_left
  have hne : S ⊓ normalizer (T : Set G) ≠ S := by
    intro h0
    have : s0 ∈ S ⊓ normalizer (T : Set G) := by rw [h0]; exact hs0S
    exact hs0N this.2
  obtain ⟨n, hnS, hnN, hnnorm⟩ := exists_mem_normalizer_not_mem h.S_pgroup hN₁S hne
  apply hnN
  refine ⟨hnS, ?_⟩
  have hTN₁ : T ≤ S ⊓ normalizer (T : Set G) := le_inf h.T_le_S Subgroup.le_normalizer
  have hclos : T ≤ Subgroup.closure {u : G | u ∈ T ∧ u * u = 1} :=
    hTeq.le.trans (sup_le (h.P_d8.le_closure_involutions.trans
      (Subgroup.closure_mono (fun u hu => ⟨h.P_le hu.1, hu.2⟩)))
      ((h.P_d8.conjugate a).le_closure_involutions.trans
        (Subgroup.closure_mono (fun u hu => ⟨hPaT hu.1, hu.2⟩))))
  have hinv : ∀ m : G, (∀ y ∈ S ⊓ normalizer (T : Set G), m * y * m⁻¹ ∈ S ⊓ normalizer (T : Set G)) →
      ∀ t ∈ T, m * t * m⁻¹ ∈ T := by
    intro m hm
    have hinvol : ∀ u ∈ T, u * u = 1 → m * u * m⁻¹ ∈ T := by
      intro u huT hu2
      obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hcomm (hTeq ▸ huT)
      have hpq : p * p * (q * q) = 1 * 1 := by
        calc p * p * (q * q) = p * (p * q) * q := by group
          _ = p * (q * p) * q := by rw [hcomm p hp q hq]
          _ = p * q * (p * q) := by group
          _ = 1 * 1 := by rw [hu2]; simp
      obtain ⟨hpp, hqq⟩ := eq_of_mul_eq_of_inf_eq_bot h.P_inf_conj (P.mul_mem hp hp) (one_mem _)
        ((conjugate P a).mul_mem hq hq) (one_mem _) hpq
      obtain ⟨Dp, hDpP, hDpel, hDpcard, hpDp⟩ := h.P_d8.exists_four_containing hp hpp
      obtain ⟨Dq, hDqPa, hDqel, hDqcard, hqDq⟩ :=
        (h.P_d8.conjugate a).exists_four_containing hq hqq
      have hDcomm : ∀ d ∈ Dp, ∀ d' ∈ Dq, d * d' = d' * d := fun d hd d' hd' =>
        hcomm d (hDpP hd) d' (hDqPa hd')
      have hdisj : Dp ⊓ Dq = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have : y ∈ P ⊓ conjugate P a := ⟨hDpP hy.1, hDqPa hy.2⟩
        rw [h.P_inf_conj] at this
        exact this
      have hEel := isElementaryAbelian_sup_of_commute hDpel hDqel hDcomm
      have hEcard : Nat.card ↥(Dp ⊔ Dq) = 16 := by
        rw [card_sup_of_commute_of_disjoint hDcomm hdisj, hDpcard, hDqcard]
      have hET : Dp ⊔ Dq ≤ T := sup_le (hDpP.trans h.P_le) (hDqPa.trans hPaT)
      have hE' := h.le_T_of_elementary hTeq hS (E := conjugate (Dp ⊔ Dq) m⁻¹) (by
        intro y hy
        rw [mem_conjugate_iff'] at hy
        have hyN : y ∈ S ⊓ normalizer (T : Set G) := by
          have := hm _ (hTN₁ (hET hy))
          have e' : m * (m⁻¹ * y * m⁻¹⁻¹) * m⁻¹ = y := by group
          rwa [e'] at this
        exact hyN)
        (isElementaryAbelian_conjugate hEel m⁻¹) (by rw [card_conjugate', hEcard]; norm_num)
      have hu : p * q ∈ Dp ⊔ Dq :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hpDp) (Subgroup.mem_sup_right hqDq)
      have hmem : m * (p * q) * m⁻¹ ∈ conjugate (Dp ⊔ Dq) m⁻¹ := by
        rw [mem_conjugate_iff']
        have e' : m⁻¹ * (m * (p * q) * m⁻¹) * m⁻¹⁻¹ = p * q := by group
        rw [e']
        exact hu
      exact hE' hmem
    intro t ht
    have hle : Subgroup.closure {u : G | u ∈ T ∧ u * u = 1} ≤
        T.comap (MulAut.conj m).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro u hu
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      simpa [MulAut.conj_apply] using hinvol u hu.1 hu.2
    have := hle (hclos ht)
    rw [Subgroup.mem_comap] at this
    simpa [MulAut.conj_apply] using this
  have h1 : ∀ t ∈ T, n * t * n⁻¹ ∈ T := hinv n (fun y hy => (hnnorm y hy).1)
  have h2 : ∀ t ∈ T, n⁻¹ * t * n ∈ T := by
    have := hinv n⁻¹ (fun y hy => by simpa using (hnnorm y hy).2)
    intro t ht
    simpa using this t ht
  exact mem_normalizer_of_two_sided h1 h2

theorem S_cases [Finite G] (h : Sec4Core a P Q T S) (hTeq : T = P ⊔ conjugate P a)
    (hS : ∀ n ∈ S, n ∈ normalizer (T : Set G) → n ∈ T ∨ a⁻¹ * n ∈ T) :
    ∀ s ∈ S, s ∈ T ∨ a⁻¹ * s ∈ T := fun s hs => hS s hs (h.normalizer_T_eq hTeq hS s hs)

end Sec4Core


end CFSG.GH74.GLS.C3.Layer1.Bk
