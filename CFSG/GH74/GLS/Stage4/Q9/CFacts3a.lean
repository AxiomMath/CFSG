module

public import CFSG.GH74.GLS.Stage4.Q9.CFacts5b
public import CFSG.GH74.GLS.Stage4.Q9.Key3

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

section Model

variable {G : Type} [Group G] {z : G} {K : Subgroup G}

theorem eq_one_or_eq_of_mem_zpowers_involution (hz : orderOf z = 2) :
    ∀ s ∈ zpowers z, s = 1 ∨ s = z := by
  intro s hs
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
  have hk := zpow_mod_orderOf z k
  rw [hz] at hk
  have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h2 with h | h
  · left
    rw [← hk, h, zpow_zero]
  · right
    rw [← hk, h, zpow_one]

theorem exists_sq_eq_z (ψ : ↥K ≃* SL2) (hzK : z ∈ K) (hz : ψ ⟨z, hzK⟩ = minusOne) :
    ∃ k ∈ K, k * k = z := by
  obtain ⟨M, hM⟩ := exists_sq_minusOne
  refine ⟨((ψ.symm M : ↥K) : G), (ψ.symm M).2, ?_⟩
  have h : ψ.symm M * ψ.symm M = ⟨z, hzK⟩ := by
    apply ψ.injective
    rw [map_mul, MulEquiv.apply_symm_apply, hM, hz]
  exact congrArg Subtype.val h

theorem exists_sq_eq_z_inverting
    (ψ : ↥K ≃* SL2) (hzK : z ∈ K) (hz : ψ ⟨z, hzK⟩ = minusOne)
    {y : G} (hy : y ∈ K) (hy3 : orderOf y = 3) :
    ∃ k ∈ K, k * k = z ∧ k * y * k⁻¹ = y⁻¹ := by
  have hM : orderOf (ψ ⟨y, hy⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy3]
  obtain ⟨M, hM1, hM2⟩ := exists_inverting_order3 _ hM
  refine ⟨((ψ.symm M : ↥K) : G), (ψ.symm M).2, ?_, ?_⟩
  · have h : ψ.symm M * ψ.symm M = ⟨z, hzK⟩ := by
      apply ψ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, hM1, hz]
    exact congrArg Subtype.val h
  · have h : ψ.symm M * ⟨y, hy⟩ * (ψ.symm M)⁻¹ = ⟨y, hy⟩⁻¹ := by
      apply ψ.injective
      rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
      exact hM2
    simpa using congrArg Subtype.val h

@[expose] def imgSub (ψ : ↥K ≃* SL2) (T : Subgroup SL2) : Subgroup G :=
  T.map (K.subtype.comp ψ.symm.toMonoidHom)

theorem mem_imgSub {ψ : ↥K ≃* SL2} {T : Subgroup SL2} {g : G} :
    g ∈ imgSub ψ T ↔ ∃ t ∈ T, ((ψ.symm t : ↥K) : G) = g := by
  simp [imgSub, Subgroup.mem_map]

theorem imgSub_le (ψ : ↥K ≃* SL2) (T : Subgroup SL2) : imgSub ψ T ≤ K := by
  intro g hg
  obtain ⟨t, -, rfl⟩ := mem_imgSub.mp hg
  exact (ψ.symm t).2

theorem card_imgSub (ψ : ↥K ≃* SL2) (T : Subgroup SL2) : Nat.card (imgSub ψ T) = Nat.card T := by
  refine Subgroup.card_map_of_injective ?_
  intro a b h
  exact ψ.symm.injective (Subtype.ext h)

theorem exists_Q16_sub
    (ψ : ↥K ≃* SL2) (hzK : z ∈ K) (hz : ψ ⟨z, hzK⟩ = minusOne) :
    ∃ Q : Subgroup G, Q ≤ K ∧ Nat.card Q = 16 ∧ z ∈ Q ∧
      ∀ s ∈ Q, (∀ w ∈ Q, s * w = w * s) → s = 1 ∨ s = z := by
  obtain ⟨T, hT16, hTm, hTc, -⟩ := exists_Q16
  have hzsymm : ψ.symm minusOne = ⟨z, hzK⟩ := ψ.symm_apply_eq.mpr hz.symm
  refine ⟨imgSub ψ T, imgSub_le ψ T, by rw [card_imgSub, hT16], ?_, ?_⟩
  · refine mem_imgSub.mpr ⟨minusOne, hTm, ?_⟩
    rw [hzsymm]
  · intro s hs hsc
    obtain ⟨s₀, hs₀, rfl⟩ := mem_imgSub.mp hs
    have h := hTc s₀ hs₀ (by
      intro w hw
      have h1 := hsc ((ψ.symm w : ↥K) : G) (mem_imgSub.mpr ⟨w, hw, rfl⟩)
      have h2 : ψ.symm s₀ * ψ.symm w = ψ.symm w * ψ.symm s₀ := Subtype.ext h1
      have h3 : ψ.symm (s₀ * w) = ψ.symm (w * s₀) := by rw [map_mul, map_mul]; exact h2
      exact ψ.symm.injective h3)
    rcases h with h | h
    · left
      rw [h]
      simp
    · right
      rw [h, hzsymm]

end Model

namespace Q9Setting

section Plain

variable {G : Type} [Group G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
  (S : Q9Setting G z K₁ K₂ F₁ F₂)

include S

theorem z_ne_one : z ≠ 1 := by
  intro h
  have := S.z_ord
  rw [h, orderOf_one] at this
  omega

theorem not_sq_eq_z_of_mem_inter {k : G} (hk₁ : k ∈ K₁) (hk₂ : k ∈ K₂) : k * k ≠ z := by
  intro h
  have hk : k ∈ zpowers z := by rw [← S.inter_eq]; exact ⟨hk₁, hk₂⟩
  rcases eq_one_or_eq_of_mem_zpowers_involution S.z_ord k hk with h' | h'
  · rw [h', one_mul] at h
    exact S.z_ne_one h.symm
  · rw [h'] at h
    exact S.z_ne_one (mul_left_cancel (a := z) (by rw [mul_one]; exact h))

theorem u₁_basic {ka kb : G} (hka : ka ∈ K₁) (hkb : kb ∈ K₂) (hka2 : ka * ka = z)
    (hkb2 : kb * kb = z) :
    orderOf (ka * kb) = 2 ∧ ka * kb * z = z * (ka * kb) ∧ ka * kb ≠ z := by
  have hcomm : ka * kb = kb * ka := S.comm ka hka kb hkb
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [S.z_ord] at this
    simpa [pow_two] using this
  have hsq : (ka * kb) ^ 2 = 1 := by
    calc (ka * kb) ^ 2 = ka * (kb * ka) * kb := by rw [pow_two]; group
      _ = ka * (ka * kb) * kb := by rw [← hcomm]
      _ = (ka * ka) * (kb * kb) := by group
      _ = 1 := by rw [hka2, hkb2, hzz]
  have hne1 : ka * kb ≠ 1 := by
    intro h
    have hka' : ka = kb⁻¹ := eq_inv_of_mul_eq_one_left h
    exact S.not_sq_eq_z_of_mem_inter hka (by rw [hka']; exact inv_mem hkb) hka2
  have hnez : ka * kb ≠ z := by
    intro h
    have hka' : ka = z * kb⁻¹ := by rw [← h]; group
    exact S.not_sq_eq_z_of_mem_inter hka (by rw [hka']; exact mul_mem S.z_mem₂ (inv_mem hkb)) hka2
  refine ⟨orderOf_eq_prime hsq hne1, ?_, hnez⟩
  have hz1 : z * ka = ka * z := (S.comm ka hka z S.z_mem₂).symm
  have hz2 : z * kb = kb * z := S.comm z S.z_mem₁ kb hkb
  calc ka * kb * z = ka * (kb * z) := by group
    _ = ka * (z * kb) := by rw [hz2]
    _ = (ka * z) * kb := by group
    _ = (z * ka) * kb := by rw [hz1]
    _ = z * (ka * kb) := by group

theorem u₁_facts {ka kb y : G} (hka : ka ∈ K₁) (hkb : kb ∈ K₂) (hka2 : ka * ka = z)
    (hkb2 : kb * kb = z) (hy : y ∈ K₁) (hkay : ka * y * ka⁻¹ = y⁻¹) :
    orderOf (ka * kb) = 2 ∧ ka * kb * z = z * (ka * kb) ∧ ka * kb ≠ z ∧
      ka * kb * y * (ka * kb)⁻¹ = y⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := S.u₁_basic hka hkb hka2 hkb2
  refine ⟨h1, h2, h3, ?_⟩
  have hky : kb * y = y * kb := (S.comm y hy kb hkb).symm
  calc ka * kb * y * (ka * kb)⁻¹ = ka * (kb * y * kb⁻¹) * ka⁻¹ := by group
    _ = ka * (y * kb * kb⁻¹) * ka⁻¹ := by rw [hky]
    _ = ka * y * ka⁻¹ := by group
    _ = y⁻¹ := hkay

theorem card_K₁_inf_centralizer_three :
    ∀ y ∈ K₁, orderOf y = 3 →
    Nat.card ↥(K₁ ⊓ centralizer ({y} : Set G)) = 18 := by
  intro y hy hy3
  obtain ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩ := q9_link S
  rw [card_inf_centralizer_of_mulEquiv ψ₁ hy]
  apply card_centralizer_order3
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy3]

theorem card_sup_inf_centralizer_K₁ : ∀ y ∈ K₁,
    Nat.card ↥((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) * 2 =
      Nat.card ↥(K₁ ⊓ centralizer ({y} : Set G)) * 720 := by
  intro y hy
  have hK₂x : K₂ ≤ centralizer ({y} : Set G) := S.K₂_le_centralizer_of_mem₁ hy
  set H₁ : Subgroup G := K₁ ⊓ centralizer ({y} : Set G) with hH₁def
  set Kx : Subgroup G := (K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G) with hKxdef
  have hsup : H₁ ⊔ K₂ = Kx := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · exact inf_le_inf_right _ le_sup_left
      · exact le_inf le_sup_right hK₂x
    · intro g hg
      obtain ⟨hgK, hgx⟩ := hg
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Lemma82.mem_sup_of_commute S.comm hgK
      have hk₂x : k₂ ∈ centralizer ({y} : Set G) := hK₂x hk₂
      have hk₁x : k₁ ∈ centralizer ({y} : Set G) := by
        have : k₁ = k₁ * k₂ * k₂⁻¹ := by group
        rw [this]
        exact mul_mem hgx (inv_mem hk₂x)
      exact mul_mem (mem_sup_left ⟨hk₁, hk₁x⟩) (mem_sup_right hk₂)
  have hinf : H₁ ⊓ K₂ = zpowers z := by
    apply le_antisymm
    · intro g hg
      have : g ∈ K₁ ⊓ K₂ := ⟨hg.1.1, hg.2⟩
      rwa [S.inter_eq] at this
    · intro g hg
      have hgz : g ∈ K₁ ⊓ K₂ := by rwa [S.inter_eq]
      refine ⟨⟨hgz.1, ?_⟩, hgz.2⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine mem_centralizer_singleton_iff.mpr ?_
      have hyz : z * y = y * z := S.z_comm₁ hy
      exact ((Commute.zpow_left (show Commute z y from hyz) n).eq)
  have h := card_sup_mul_card_inf_of_commute (H₁ := H₁) (H₂ := K₂)
    (fun a ha b hb => S.comm a ha.1 b hb)
  rw [hsup, hinf, Nat.card_zpowers, S.z_ord, S.card_K₂] at h
  exact h

theorem inf_centralizer_le_sup_K₁ :
    ∀ y ∈ K₁, orderOf y = 3 →
    centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G) ≤ K₁ ⊔ K₂ := by
  intro y hy hy3 g hg
  obtain ⟨hgy, hgz⟩ := hg
  rcases S.mem_C_cases g hgz with h | ⟨k, hk, rfl⟩
  · exact h
  · exfalso
    obtain ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩ := q9_link S
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Lemma82.mem_sup_of_commute S.comm hk
    have h1 : k₁ * k₂ * S.t * y = y * (k₁ * k₂ * S.t) := mem_centralizer_singleton_iff.mp hgy
    have hy' : S.t * y * S.t⁻¹ ∈ K₁ := S.normal₁ S.t S.t_mem y hy
    have e1 : k₁ * (S.t * y * S.t⁻¹) * (k₂ * S.t) = y * k₁ * (k₂ * S.t) := by
      have hc : (S.t * y * S.t⁻¹) * k₂ = k₂ * (S.t * y * S.t⁻¹) := S.comm _ hy' k₂ hk₂
      calc k₁ * (S.t * y * S.t⁻¹) * (k₂ * S.t) = k₁ * ((S.t * y * S.t⁻¹) * k₂) * S.t := by group
        _ = k₁ * (k₂ * (S.t * y * S.t⁻¹)) * S.t := by rw [hc]
        _ = k₁ * k₂ * S.t * y := by group
        _ = y * (k₁ * k₂ * S.t) := h1
        _ = y * k₁ * (k₂ * S.t) := by group
    have e2 : k₁ * (S.t * y * S.t⁻¹) = y * k₁ := mul_right_cancel e1
    have e3 : k₁ * (S.t * y * S.t⁻¹) * k₁⁻¹ = y := by rw [e2]; group
    have hM : orderOf (ψ₁ ⟨y, hy⟩) = 3 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy3]
    apply sigma_not_conj_order3 _ hM (ψ₁ ⟨k₁, hk₁⟩)
    have hσ : ψ₁ ⟨S.t * y * S.t⁻¹, hy'⟩ = sigmaAut (ψ₁ ⟨y, hy⟩) := ht₁ ⟨y, hy⟩ ⟨_, hy'⟩ rfl
    have hsub : (⟨k₁, hk₁⟩ * ⟨S.t * y * S.t⁻¹, hy'⟩ * ⟨k₁, hk₁⟩⁻¹ : ↥K₁) = ⟨y, hy⟩ :=
      Subtype.ext (by simpa using e3)
    have := congrArg ψ₁ hsub
    rw [map_mul, map_mul, map_inv, hσ] at this
    exact this

theorem card_C_inf_centralizer_three :
    ∀ y ∈ K₁, orderOf y = 3 →
    Nat.card ↥(centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G)) = 6480 := by
  intro y hy hy3
  have hcard := S.card_sup_inf_centralizer_K₁ y hy
  rw [S.card_K₁_inf_centralizer_three y hy hy3] at hcard
  have hBeq : centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G) =
      (K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G) := by
    apply le_antisymm
    · intro g hg
      exact ⟨S.inf_centralizer_le_sup_K₁ y hy hy3 hg, hg.1⟩
    · intro g hg
      exact ⟨hg.2, sup_le S.le_centralizer₁ S.le_centralizer₂ hg.1⟩
  rw [hBeq]
  omega

end Plain

section Fin

variable {G : Type} [Group G] [Finite G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁]
  [Field F₂] (S : Q9Setting G z K₁ K₂ F₁ F₂)

include S

theorem oddC_le_K₁ : ∀ y ∈ K₁, ∀ M : Subgroup G,
    M ≤ centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G) →
    (∀ c ∈ centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G), ∀ m ∈ M, c * m * c⁻¹ ∈ M) →
    Odd (Nat.card M) → M ≤ K₁ := by
  intro y hy M hMle hMnorm hodd
  have hK₂B : K₂ ≤ centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G) :=
    le_inf (S.K₂_le_centralizer_of_mem₁ hy) (fun k hk =>
      mem_centralizer_singleton_iff.mpr (S.comm z S.z_mem₁ k hk).symm)
  have hMK₂ : ∀ k ∈ K₂, ∀ m ∈ M, k * m * k⁻¹ ∈ M := fun k hk m hm => hMnorm k (hK₂B hk) m hm
  have htriv := S.K₂_odd_normal M hMK₂ hodd
  intro m hm
  have hmC : m ∈ centralizer ({z} : Set G) := (hMle hm).2
  have hcomm : ∀ k ∈ K₂, m * k = k * m := by
    intro k hk
    have h1 : m * k * m⁻¹ ∈ K₂ := S.normal₂ m hmC k hk
    have h2 : k * m⁻¹ * k⁻¹ ∈ M := hMK₂ k hk m⁻¹ (inv_mem hm)
    have h3 : (m * k * m⁻¹) * k⁻¹ ∈ M := by
      have : (m * k * m⁻¹) * k⁻¹ = m * (k * m⁻¹ * k⁻¹) := by group
      rw [this]
      exact mul_mem hm h2
    have h4 : (m * k * m⁻¹) * k⁻¹ ∈ K₂ := mul_mem h1 (inv_mem hk)
    have h5 : (m * k * m⁻¹) * k⁻¹ = 1 := htriv _ h4 h3
    have h6 : m * k * m⁻¹ = k := mul_inv_eq_one.mp h5
    calc m * k = (m * k * m⁻¹) * m := by group
      _ = k * m := by rw [h6]
  exact S.centralizer_K₂_le_K₁ m hmC hcomm

theorem oddC_three
    : ∀ y ∈ K₁, orderOf y = 3 → ∀ M : Subgroup G,
    M ≤ centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G) →
    (∀ c ∈ centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G), ∀ m ∈ M, c * m * c⁻¹ ∈ M) →
    Odd (Nat.card M) → ∀ m ∈ M, ∃ n : ℕ, orderOf m = 3 ^ n := by
  intro y hy hy3 M hMle hMnorm hodd m hm
  obtain ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩ := q9_link S
  have hm₁ : m ∈ K₁ := S.oddC_le_K₁ y hy M hMle hMnorm hodd hm
  have hmy : m ∈ centralizer ({y} : Set G) := (hMle hm).1
  have hmodd : Odd (orderOf m) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard M hm)
  have hM₀ : orderOf (ψ₁ ⟨y, hy⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy3]
  have hN : ψ₁ ⟨m, hm₁⟩ ∈ centralizer ({ψ₁ ⟨y, hy⟩} : Set SL2) := by
    refine mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hmy)
  have hNodd : Odd (orderOf (ψ₁ ⟨m, hm₁⟩)) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hmodd
  obtain ⟨n, hn⟩ := centralizer_order3_odd _ hM₀ _ hN hNodd
  refine ⟨n, ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk] at hn
  exact hn

theorem key3_K₁ :
    ∀ y ∈ K₁, orderOf y = 3 →
    centralizer ({y} : Set G) ≤ centralizer ({z} : Set G) ∧
      ∀ e : G, orderOf e = 2 → e ∈ centralizer ({y} : Set G) → e = z := by
  intro y hy hy3
  obtain ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩ := q9_link S
  have hz₁' : ψ₁ ⟨z, S.z_mem₁⟩ = minusOne := hz₁ _ rfl
  have hz₂' : ψ₂ ⟨z, S.z_mem₂⟩ = minusOne := hz₂ _ rfl
  obtain ⟨ka, hka, hka2, hkay⟩ := exists_sq_eq_z_inverting ψ₁ S.z_mem₁ hz₁' hy hy3
  obtain ⟨kb, hkb, hkb2⟩ := exists_sq_eq_z ψ₂ S.z_mem₂ hz₂'
  obtain ⟨hu₁, hu₁z, hu₁ne, hu₁y⟩ := S.u₁_facts hka hkb hka2 hkb2 hy hkay
  obtain ⟨Q, hQK, hQ16, hzQ, hQc⟩ := exists_Q16_sub ψ₂ S.z_mem₂ hz₂'
  have : Finite F₂ := Nat.finite_of_card_ne_zero (by rw [S.card₂]; norm_num)
  obtain ⟨Pb, hPbK, hPb3, hPb9⟩ := S.sylow3_K₂
  have hQy : ∀ s ∈ Q, s * y = y * s := fun s hs => (S.comm y hy s (hQK hs)).symm
  have hQz : ∀ s ∈ Q, s * z = z * s := fun s hs => (S.comm z S.z_mem₁ s (hQK hs)).symm
  have hQB : Q ≤ centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G) := fun s hs =>
    ⟨mem_centralizer_singleton_iff.mpr (hQy s hs), mem_centralizer_singleton_iff.mpr (hQz s hs)⟩
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 4) (by rw [hQ16]; norm_num)
  have hQinv : ∀ s ∈ Q, orderOf s = 2 → s = z := fun s hs h2 => S.K₂_involution s (hQK hs) h2
  have hQyl : ¬ 2 ∣ Q.relIndex (centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G)) := by
    have h := Subgroup.relIndex_mul_card Q (centralizer ({y} : Set G) ⊓ centralizer ({z} : Set G))
    rw [inf_eq_left.mpr hQB, hQ16, S.card_C_inf_centralizer_three y hy hy3] at h
    omega
  exact key3k_inv S.z_ord hy3 (S.z_comm₁ hy) hu₁ hu₁z hu₁ne hu₁y S.one_class S.card_C_prime_dvd
    S.card_C_five.le S.card_G_three.le S.sylow5.1.le Q hQy hQ2 hzQ hQz hQc hQinv hQyl
    (S.oddC_three y hy hy3) K₂ (fun k hk => (S.comm y hy k hk).symm) S.z_mem₂
    (fun k hk => S.comm z S.z_mem₁ k hk) Pb hPbK hPb3 hPb9 S.card₂ S.φ₂

theorem key3_K₂ :
    ∀ y ∈ K₂, orderOf y = 3 →
    centralizer ({y} : Set G) ≤ centralizer ({z} : Set G) ∧
      ∀ e : G, orderOf e = 2 → e ∈ centralizer ({y} : Set G) → e = z :=
  S.swap.key3_K₁

end Fin

end Q9Setting

end CFSG.GH74.GLS.Stage4.Q9
