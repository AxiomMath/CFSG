module

public import CFSG.GH74.GLS.Stage4.Q9.CFacts3a

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

section Model

variable {G : Type} [Group G]

theorem mem_of_mul_self_mem_of_odd {H : Subgroup G} {c : G} (hodd : Odd (orderOf c))
    (h : c * c ∈ H) : c ∈ H := by
  obtain ⟨j, hj⟩ := hodd
  have h1 : c ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one c
  have e2 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
  have e : (c * c) ^ (j + 1) = c := by
    calc (c * c) ^ (j + 1) = c ^ (2 * (j + 1)) := by rw [pow_mul, pow_two]
      _ = c ^ ((2 * j + 1) + 1) := by rw [e2]
      _ = c ^ (2 * j + 1) * c := pow_succ c _
      _ = c := by rw [h1, one_mul]
  rw [← e]
  exact pow_mem h (j + 1)

theorem exists_sylow3_containing {K : Subgroup G} (hK : Nat.card K = 720) {y : G} (hy : y ∈ K)
    (hy3 : orderOf y = 3) :
    ∃ P : Subgroup G, P ≤ K ∧ y ∈ P ∧ IsPGroup 3 P ∧ Nat.card P = 9 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy' : orderOf (⟨y, hy⟩ : K) = 3 := by rw [Subgroup.orderOf_mk]; exact hy3
  have hp : IsPGroup 3 (zpowers (⟨y, hy⟩ : K)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy']; simp)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hP9 : Nat.card P = 9 := by
    rw [P.card_eq_multiplicity, hK, fac720_three]
    norm_num
  refine ⟨(P : Subgroup K).map K.subtype, Subgroup.map_subtype_le _, ?_,
    P.isPGroup'.map K.subtype, ?_⟩
  · exact ⟨⟨y, hy⟩, hP (mem_zpowers _), rfl⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hP9

theorem comm_of_card_nine {P : Subgroup G} (hP : Nat.card P = 9) :
    ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have hc : IsMulCommutative P :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hP]; norm_num)
  intro a ha b hb
  exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem mul_self_mem_of_card {H P : Subgroup G} (hPH : P ≤ H) (hP : Nat.card P = 9)
    (hH : Nat.card H = 18) : ∀ a ∈ H, a * a ∈ P := by
  intro a ha
  have h := Subgroup.relIndex_mul_card P H
  rw [inf_eq_left.mpr hPH, hP, hH] at h
  have hrel : P.relIndex H = 2 := by omega
  have hidx : (P.subgroupOf H).index = 2 := hrel
  exact Subgroup.mem_subgroupOf.mp (Subgroup.mul_self_mem_of_index_two hidx ⟨a, ha⟩)

end Model

namespace Q9Setting

section Plain

variable {G : Type} [Group G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
  (S : Q9Setting G z K₁ K₂ F₁ F₂)

include S

theorem mem_inter_cases {k : G} (hk₁ : k ∈ K₁) (hk₂ : k ∈ K₂) : k = 1 ∨ k = z :=
  eq_one_or_eq_of_mem_zpowers_involution S.z_ord k (by rw [← S.inter_eq]; exact ⟨hk₁, hk₂⟩)

theorem conj_mixed {g₁ g₂ a b : G} (hg₁ : g₁ ∈ K₁) (hg₂ : g₂ ∈ K₂) (ha : a ∈ K₁) (hb : b ∈ K₂) :
    (g₁ * g₂) * (a * b) * (g₁ * g₂)⁻¹ = (g₁ * a * g₁⁻¹) * (g₂ * b * g₂⁻¹) := by
  have e1 : g₂ * a * g₂⁻¹ = a := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (S.comm a ha g₂ hg₂).symm
  have hb' : g₂ * b * g₂⁻¹ ∈ K₂ := mul_mem (mul_mem hg₂ hb) (inv_mem hg₂)
  have e2 : g₁ * (g₂ * b * g₂⁻¹) * g₁⁻¹ = g₂ * b * g₂⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact S.comm g₁ hg₁ _ hb'
  calc (g₁ * g₂) * (a * b) * (g₁ * g₂)⁻¹
      = (g₁ * (g₂ * a * g₂⁻¹) * g₁⁻¹) * (g₁ * (g₂ * b * g₂⁻¹) * g₁⁻¹) := by group
    _ = (g₁ * a * g₁⁻¹) * (g₂ * b * g₂⁻¹) := by rw [e1, e2]

theorem mixed_eq {y₁ y₂ a b : G} (hy₁ : y₁ ∈ K₁) (hy₂ : y₂ ∈ K₂) (ha : a ∈ K₁) (hb : b ∈ K₂)
    (ha3 : a ^ 3 = 1) (ho : orderOf y₁ = 3) (h : a * b = y₁ * y₂) : a = y₁ ∧ b = y₂ := by
  have h1 : y₁⁻¹ * a * b = y₂ := by
    calc y₁⁻¹ * a * b = y₁⁻¹ * (a * b) := by group
      _ = y₁⁻¹ * (y₁ * y₂) := by rw [h]
      _ = y₂ := by group
  have hcomm : y₁⁻¹ * a = y₂ * b⁻¹ := by
    calc y₁⁻¹ * a = y₁⁻¹ * a * b * b⁻¹ := by group
      _ = y₂ * b⁻¹ := by rw [h1]
  have hK₁ : y₁⁻¹ * a ∈ K₁ := mul_mem (inv_mem hy₁) ha
  have hK₂ : y₁⁻¹ * a ∈ K₂ := by rw [hcomm]; exact mul_mem hy₂ (inv_mem hb)
  rcases S.mem_inter_cases hK₁ hK₂ with h0 | h0
  · have hay : a = y₁ := by
      calc a = y₁ * (y₁⁻¹ * a) := by group
        _ = y₁ := by rw [h0, mul_one]
    refine ⟨hay, ?_⟩
    rw [h0] at hcomm
    exact (mul_inv_eq_one.mp hcomm.symm).symm
  · exfalso
    have hay : a = y₁ * z := by
      calc a = y₁ * (y₁⁻¹ * a) := by group
        _ = y₁ * z := by rw [h0]
    have hcom : Commute y₁ z := (S.z_comm₁ hy₁).symm
    have hy3 : y₁ ^ 3 = 1 := by
      have := pow_orderOf_eq_one y₁
      rwa [ho] at this
    have hzz : z ^ 2 = 1 := by
      have := pow_orderOf_eq_one z
      rwa [S.z_ord] at this
    have h3 : (y₁ * z) ^ 3 = z := by
      rw [hcom.mul_pow, hy3, one_mul]
      calc z ^ 3 = z ^ 2 * z := by rw [pow_succ]
        _ = z := by rw [hzz, one_mul]
    rw [hay, h3] at ha3
    exact S.z_ne_one ha3

theorem orderOf_mixed {y₁ y₂ : G} (h₁ : y₁ ∈ K₁) (h₂ : y₂ ∈ K₂) (o₁ : orderOf y₁ = 3)
    (o₂ : orderOf y₂ = 3) : orderOf (y₁ * y₂) = 3 := by
  have hcom : Commute y₁ y₂ := S.comm y₁ h₁ y₂ h₂
  have h13 : y₁ ^ 3 = 1 := by
    have := pow_orderOf_eq_one y₁
    rwa [o₁] at this
  have h23 : y₂ ^ 3 = 1 := by
    have := pow_orderOf_eq_one y₂
    rwa [o₂] at this
  have hcube : (y₁ * y₂) ^ 3 = 1 := by rw [hcom.mul_pow, h13, h23, one_mul]
  have hne : y₁ * y₂ ≠ 1 := by
    intro h
    have : y₁ = y₂⁻¹ := eq_inv_of_mul_eq_one_left h
    rcases S.mem_inter_cases h₁ (by rw [this]; exact inv_mem h₂) with h' | h'
    · rw [h', orderOf_one] at o₁
      omega
    · rw [h', S.z_ord] at o₁
      omega
  exact orderOf_eq_prime hcube hne

theorem card_sup_sylow {P₁ P₂ : Subgroup G} (h₁ : P₁ ≤ K₁) (h₂ : P₂ ≤ K₂) (c₁ : Nat.card P₁ = 9)
    (c₂ : Nat.card P₂ = 9) : Nat.card ↥(P₁ ⊔ P₂) = 81 := by
  have hcomm : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb => S.comm a (h₁ ha) b (h₂ hb)
  have h := card_sup_mul_card_inf_of_commute hcomm
  have hbot : P₁ ⊓ P₂ = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rcases S.mem_inter_cases (h₁ hg.1) (h₂ hg.2) with h0 | h0
    · rw [h0]
      exact one_mem _
    · exfalso
      have hzP : z ∈ P₁ := h0 ▸ hg.1
      have h2 := Subgroup.orderOf_dvd_natCard P₁ hzP
      rw [S.z_ord, c₁] at h2
      omega
  rw [hbot, Subgroup.card_bot, c₁, c₂] at h
  omega

theorem mem_K_of_odd_order : ∀ c ∈ centralizer ({z} : Set G), Odd (orderOf c) → c ∈ K₁ ⊔ K₂ := by
  intro c hc hodd
  have hidx : ((K₁ ⊔ K₂).subgroupOf (centralizer ({z} : Set G))).index = 2 := S.index_two
  have h2 := Subgroup.mul_self_mem_of_index_two hidx (⟨c, hc⟩ : centralizer ({z} : Set G))
  exact mem_of_mul_self_mem_of_odd hodd (Subgroup.mem_subgroupOf.mp h2)

theorem exists_cube_one_decomp {a b : G} (ha : a ∈ K₁) (hb : b ∈ K₂) (h3 : (a * b) ^ 3 = 1) :
    ∃ a' ∈ K₁, ∃ b' ∈ K₂, a' * b' = a * b ∧ a' ^ 3 = 1 ∧ b' ^ 3 = 1 := by
  have hcom : Commute a b := S.comm a ha b hb
  have hcube : a ^ 3 * b ^ 3 = 1 := by rw [← hcom.mul_pow]; exact h3
  have hmem : a ^ 3 ∈ K₂ := by
    have : a ^ 3 = (b ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hcube
    rw [this]
    exact inv_mem (pow_mem hb 3)
  rcases S.mem_inter_cases (pow_mem ha 3) hmem with h | h
  · refine ⟨a, ha, b, hb, rfl, h, ?_⟩
    rw [h, one_mul] at hcube
    exact hcube
  · have hzz : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rw [S.z_ord] at this
      simpa [pow_two] using this
    have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hzz
    have hz4 : z * z ^ 3 = 1 := by
      calc z * z ^ 3 = z ^ 4 := (pow_succ' z 3).symm
        _ = (z ^ 2) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [hz2, one_pow]
    have hz1 : Commute a z := (S.z_comm₁ ha).symm
    have hz3 : Commute z b := S.comm z S.z_mem₁ b hb
    have hb3 : b ^ 3 = z := by
      rw [h] at hcube
      have := eq_inv_of_mul_eq_one_right hcube
      rw [this]
      exact inv_eq_of_mul_eq_one_right hzz
    refine ⟨a * z, mul_mem ha S.z_mem₁, b * z, mul_mem hb S.z_mem₂, ?_, ?_, ?_⟩
    · calc a * z * (b * z) = a * (z * b) * z := by group
        _ = a * (b * z) * z := by rw [hz3.eq]
        _ = a * b * (z * z) := by group
        _ = a * b := by rw [hzz, mul_one]
    · rw [hz1.mul_pow, h, hz4]
    · have hbz : Commute b z := hz3.symm
      rw [hbz.mul_pow, hb3, hz4]

theorem inf_centralizer_le_sup_mixed
    {y₁ y₂ : G} (h₁ : y₁ ∈ K₁) (h₂ : y₂ ∈ K₂)
    (o₁ : orderOf y₁ = 3) :
    centralizer ({y₁ * y₂} : Set G) ⊓ centralizer ({z} : Set G) ≤ K₁ ⊔ K₂ := by
  intro g hg
  obtain ⟨hgy, hgz⟩ := hg
  rcases S.mem_C_cases g hgz with h | ⟨k, hk, rfl⟩
  · exact h
  · exfalso
    obtain ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩ := q9_link S
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Lemma82.mem_sup_of_commute S.comm hk
    have h1 : k₁ * k₂ * S.t * (y₁ * y₂) = (y₁ * y₂) * (k₁ * k₂ * S.t) :=
      mem_centralizer_singleton_iff.mp hgy
    have hy₁' : S.t * y₁ * S.t⁻¹ ∈ K₁ := S.normal₁ S.t S.t_mem y₁ h₁
    have hy₂' : S.t * y₂ * S.t⁻¹ ∈ K₂ := S.normal₂ S.t S.t_mem y₂ h₂
    have e : (k₁ * k₂) * ((S.t * y₁ * S.t⁻¹) * (S.t * y₂ * S.t⁻¹)) * (k₁ * k₂)⁻¹ = y₁ * y₂ := by
      calc (k₁ * k₂) * ((S.t * y₁ * S.t⁻¹) * (S.t * y₂ * S.t⁻¹)) * (k₁ * k₂)⁻¹
          = (k₁ * k₂ * S.t * (y₁ * y₂)) * (k₁ * k₂ * S.t)⁻¹ := by group
        _ = (y₁ * y₂ * (k₁ * k₂ * S.t)) * (k₁ * k₂ * S.t)⁻¹ := by rw [h1]
        _ = y₁ * y₂ := by group
    rw [S.conj_mixed hk₁ hk₂ hy₁' hy₂'] at e
    have ha1 : k₁ * (S.t * y₁ * S.t⁻¹) * k₁⁻¹ ∈ K₁ := mul_mem (mul_mem hk₁ hy₁') (inv_mem hk₁)
    have hb1 : k₂ * (S.t * y₂ * S.t⁻¹) * k₂⁻¹ ∈ K₂ := mul_mem (mul_mem hk₂ hy₂') (inv_mem hk₂)
    have hy13 : y₁ ^ 3 = 1 := by
      have := pow_orderOf_eq_one y₁
      rwa [o₁] at this
    have ha3 : (k₁ * (S.t * y₁ * S.t⁻¹) * k₁⁻¹) ^ 3 = 1 := by
      rw [conj_pow, conj_pow, hy13]
      group
    obtain ⟨hae, -⟩ := S.mixed_eq h₁ h₂ ha1 hb1 ha3 o₁ e
    have hM : orderOf (ψ₁ ⟨y₁, h₁⟩) = 3 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, o₁]
    apply sigma_not_conj_order3 _ hM (ψ₁ ⟨k₁, hk₁⟩)
    have hσ : ψ₁ ⟨S.t * y₁ * S.t⁻¹, hy₁'⟩ = sigmaAut (ψ₁ ⟨y₁, h₁⟩) := ht₁ ⟨y₁, h₁⟩ ⟨_, hy₁'⟩ rfl
    have hsub : (⟨k₁, hk₁⟩ * ⟨S.t * y₁ * S.t⁻¹, hy₁'⟩ * ⟨k₁, hk₁⟩⁻¹ : ↥K₁) = ⟨y₁, h₁⟩ :=
      Subtype.ext (by simpa using hae)
    have := congrArg ψ₁ hsub
    rw [map_mul, map_mul, map_inv, hσ] at this
    exact this

theorem inf_centralizer_mixed_eq
    {y₁ y₂ : G} (h₁ : y₁ ∈ K₁) (h₂ : y₂ ∈ K₂) (o₁ : orderOf y₁ = 3) :
    centralizer ({y₁ * y₂} : Set G) ⊓ centralizer ({z} : Set G) =
      (K₁ ⊓ centralizer ({y₁} : Set G)) ⊔ (K₂ ⊓ centralizer ({y₂} : Set G)) := by
  apply le_antisymm
  · intro g hg
    have hgK : g ∈ K₁ ⊔ K₂ := S.inf_centralizer_le_sup_mixed h₁ h₂ o₁ hg
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Lemma82.mem_sup_of_commute S.comm hgK
    have hgy : k₁ * k₂ * (y₁ * y₂) = (y₁ * y₂) * (k₁ * k₂) :=
      mem_centralizer_singleton_iff.mp hg.1
    have hconj : (k₁ * k₂) * (y₁ * y₂) * (k₁ * k₂)⁻¹ = y₁ * y₂ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hgy
    rw [S.conj_mixed hk₁ hk₂ h₁ h₂] at hconj
    have ha1 : k₁ * y₁ * k₁⁻¹ ∈ K₁ := mul_mem (mul_mem hk₁ h₁) (inv_mem hk₁)
    have hb1 : k₂ * y₂ * k₂⁻¹ ∈ K₂ := mul_mem (mul_mem hk₂ h₂) (inv_mem hk₂)
    have hy13 : y₁ ^ 3 = 1 := by
      have := pow_orderOf_eq_one y₁
      rwa [o₁] at this
    have ha3 : (k₁ * y₁ * k₁⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hy13]
      group
    obtain ⟨hae, hbe⟩ := S.mixed_eq h₁ h₂ ha1 hb1 ha3 o₁ hconj
    refine mul_mem (mem_sup_left ⟨hk₁, ?_⟩) (mem_sup_right ⟨hk₂, ?_⟩)
    · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hae)
    · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hbe)
  · refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨hgK, hgy⟩ := hg
      have h1 : g * y₁ = y₁ * g := mem_centralizer_singleton_iff.mp hgy
      have h2 : g * y₂ = y₂ * g := S.comm g hgK y₂ h₂
      refine ⟨mem_centralizer_singleton_iff.mpr ?_, S.le_centralizer₁ hgK⟩
      exact ((show Commute g y₁ from h1).mul_right (show Commute g y₂ from h2)).eq
    · intro g hg
      obtain ⟨hgK, hgy⟩ := hg
      have h1 : g * y₂ = y₂ * g := mem_centralizer_singleton_iff.mp hgy
      have h2 : g * y₁ = y₁ * g := (S.comm y₁ h₁ g hgK).symm
      refine ⟨mem_centralizer_singleton_iff.mpr ?_, S.le_centralizer₂ hgK⟩
      exact ((show Commute g y₁ from h2).mul_right (show Commute g y₂ from h1)).eq

theorem card_C_inf_centralizer_mixed
    {y₁ y₂ : G} (h₁ : y₁ ∈ K₁) (h₂ : y₂ ∈ K₂)
    (o₁ : orderOf y₁ = 3) (o₂ : orderOf y₂ = 3) :
    Nat.card ↥(centralizer ({y₁ * y₂} : Set G) ⊓ centralizer ({z} : Set G)) = 162 := by
  rw [S.inf_centralizer_mixed_eq h₁ h₂ o₁]
  have hc₁ := S.card_K₁_inf_centralizer_three y₁ h₁ o₁
  have hc₂ := S.swap.card_K₁_inf_centralizer_three y₂ h₂ o₂
  have hinf : (K₁ ⊓ centralizer ({y₁} : Set G)) ⊓ (K₂ ⊓ centralizer ({y₂} : Set G)) = zpowers z := by
    apply le_antisymm
    · intro g hg
      have : g ∈ K₁ ⊓ K₂ := ⟨hg.1.1, hg.2.1⟩
      rwa [S.inter_eq] at this
    · intro g hg
      have hgz : g ∈ K₁ ⊓ K₂ := by rwa [S.inter_eq]
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨⟨hgz.1, ?_⟩, ⟨hgz.2, ?_⟩⟩
      · exact mem_centralizer_singleton_iff.mpr
          (Commute.zpow_left (show Commute z y₁ from S.z_comm₁ h₁) n).eq
      · exact mem_centralizer_singleton_iff.mpr
          (Commute.zpow_left (show Commute z y₂ from S.comm z S.z_mem₁ y₂ h₂) n).eq
  have h := card_sup_mul_card_inf_of_commute
    (H₁ := K₁ ⊓ centralizer ({y₁} : Set G)) (H₂ := K₂ ⊓ centralizer ({y₂} : Set G))
    (fun a ha b hb => S.comm a ha.1 b hb.1)
  rw [hinf, Nat.card_zpowers, S.z_ord, hc₁, hc₂] at h
  omega

end Plain

section Fin

variable {G : Type} [Group G] [Finite G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁]
  [Field F₂] (S : Q9Setting G z K₁ K₂ F₁ F₂)

include S

theorem key3_mixed
    {y₁ y₂ : G} (h₁ : y₁ ∈ K₁) (h₂ : y₂ ∈ K₂) (o₁ : orderOf y₁ = 3)
    (o₂ : orderOf y₂ = 3) :
    centralizer ({y₁ * y₂} : Set G) ≤ centralizer ({z} : Set G) ∧
      ∀ e : G, orderOf e = 2 → e ∈ centralizer ({y₁ * y₂} : Set G) → e = z := by
  obtain ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩ := q9_link S
  have hy3 := S.orderOf_mixed h₁ h₂ o₁ o₂
  have hcom : Commute y₁ y₂ := S.comm y₁ h₁ y₂ h₂
  have hyz : z * (y₁ * y₂) = (y₁ * y₂) * z :=
    ((show Commute z y₁ from S.z_comm₁ h₁).mul_right
      (show Commute z y₂ from S.comm z S.z_mem₁ y₂ h₂)).eq
  obtain ⟨ka, hka, hka2, hkay⟩ := exists_sq_eq_z_inverting ψ₁ S.z_mem₁ (hz₁ _ rfl) h₁ o₁
  obtain ⟨kb, hkb, hkb2, hkby⟩ := exists_sq_eq_z_inverting ψ₂ S.z_mem₂ (hz₂ _ rfl) h₂ o₂
  obtain ⟨hu, huz, hune⟩ := S.u₁_basic hka hkb hka2 hkb2
  have huy : ka * kb * (y₁ * y₂) * (ka * kb)⁻¹ = (y₁ * y₂)⁻¹ := by
    rw [S.conj_mixed hka hkb h₁ h₂, hkay, hkby, mul_inv_rev]
    exact (Commute.inv_inv hcom).eq
  obtain ⟨P₁, hP₁K, hy₁P, -, hP₁9⟩ := exists_sylow3_containing S.card_K₁ h₁ o₁
  obtain ⟨P₂, hP₂K, hy₂P, -, hP₂9⟩ := exists_sylow3_containing S.card_K₂ h₂ o₂
  have hP81 : Nat.card ↥(P₁ ⊔ P₂) = 81 := S.card_sup_sylow hP₁K hP₂K hP₁9 hP₂9
  have hP3 : IsPGroup 3 ↥(P₁ ⊔ P₂) := IsPGroup.of_card (n := 4) (by rw [hP81]; norm_num)
  have hcommP : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb =>
    S.comm a (hP₁K ha) b (hP₂K hb)
  have hPy : ∀ p ∈ P₁ ⊔ P₂, p * (y₁ * y₂) = (y₁ * y₂) * p := by
    intro p hp
    obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := Lemma82.mem_sup_of_commute hcommP hp
    have c1 : Commute p₁ y₁ := comm_of_card_nine hP₁9 p₁ hp₁ y₁ hy₁P
    have c2 : Commute p₁ y₂ := S.comm p₁ (hP₁K hp₁) y₂ h₂
    have c3 : Commute p₂ y₁ := (S.comm y₁ h₁ p₂ (hP₂K hp₂)).symm
    have c4 : Commute p₂ y₂ := comm_of_card_nine hP₂9 p₂ hp₂ y₂ hy₂P
    exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq
  have hKC : K₁ ⊔ K₂ ≤ centralizer ({z} : Set G) := sup_le S.le_centralizer₁ S.le_centralizer₂
  have hPz : ∀ p ∈ P₁ ⊔ P₂, p * z = z * p := fun p hp =>
    mem_centralizer_singleton_iff.mp (hKC (sup_le_sup hP₁K hP₂K hp))
  have hC2 : (Nat.card ↥(centralizer ({y₁ * y₂} : Set G) ⊓ centralizer ({z} : Set G))).factorization 2
      = 1 := by
    rw [S.card_C_inf_centralizer_mixed h₁ h₂ o₁ o₂]
    norm_num [Nat.factorization]
  have hH₁ := S.card_K₁_inf_centralizer_three y₁ h₁ o₁
  have hH₂ := S.swap.card_K₁_inf_centralizer_three y₂ h₂ o₂
  have hP₁H : P₁ ≤ K₁ ⊓ centralizer ({y₁} : Set G) := fun p hp =>
    ⟨hP₁K hp, mem_centralizer_singleton_iff.mpr (comm_of_card_nine hP₁9 p hp y₁ hy₁P)⟩
  have hP₂H : P₂ ≤ K₂ ⊓ centralizer ({y₂} : Set G) := fun p hp =>
    ⟨hP₂K hp, mem_centralizer_singleton_iff.mpr (comm_of_card_nine hP₂9 p hp y₂ hy₂P)⟩
  have hoddC : ∀ c ∈ centralizer ({y₁ * y₂} : Set G) ⊓ centralizer ({z} : Set G),
      Odd (orderOf c) → c ∈ P₁ ⊔ P₂ := by
    intro c hc hodd
    rw [S.inf_centralizer_mixed_eq h₁ h₂ o₁] at hc
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := Lemma82.mem_sup_of_commute
      (K₁ := K₁ ⊓ centralizer ({y₁} : Set G)) (K₂ := K₂ ⊓ centralizer ({y₂} : Set G))
      (fun a ha b hb => S.comm a ha.1 b hb.1) hc
    have hs₁ := mul_self_mem_of_card hP₁H hP₁9 hH₁ c₁ hc₁
    have hs₂ := mul_self_mem_of_card hP₂H hP₂9 hH₂ c₂ hc₂
    have hcc : c₂ * c₁ = c₁ * c₂ := (S.comm c₁ hc₁.1 c₂ hc₂.1).symm
    have hsq : c₁ * c₂ * (c₁ * c₂) = (c₁ * c₁) * (c₂ * c₂) := by
      calc c₁ * c₂ * (c₁ * c₂) = c₁ * (c₂ * c₁) * c₂ := by group
        _ = c₁ * (c₁ * c₂) * c₂ := by rw [hcc]
        _ = (c₁ * c₁) * (c₂ * c₂) := by group
    refine mem_of_mul_self_mem_of_odd hodd ?_
    rw [hsq]
    exact mul_mem (mem_sup_left hs₁) (mem_sup_right hs₂)
  exact key3m_inv S.z_ord hy3 hyz hu huz hune huy S.one_class S.card_C_prime_dvd S.card_C_five.le
    S.card_G_three.le S.sylow5.1.le S.h27 (P₁ ⊔ P₂) hP3 hP81 hPy hPz hC2 hoddC

theorem hK3
    : ∀ y : G, y ∈ centralizer ({z} : Set G) → orderOf y = 3 →
    centralizer ({y} : Set G) ≤ centralizer ({z} : Set G) ∧
      ∀ e : G, orderOf e = 2 → e ∈ centralizer ({y} : Set G) → e = z := by
  intro y hyC hy3
  have hyK : y ∈ K₁ ⊔ K₂ := S.mem_K_of_odd_order y hyC (by rw [hy3]; exact ⟨1, rfl⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := Lemma82.mem_sup_of_commute S.comm hyK
  have h3 : (a * b) ^ 3 = 1 := by
    rw [hab]
    have := pow_orderOf_eq_one y
    rwa [hy3] at this
  obtain ⟨a', ha', b', hb', hab', ha3, hb3⟩ := S.exists_cube_one_decomp ha hb h3
  rw [hab] at hab'
  subst hab'
  by_cases hA : a' = 1
  · subst hA
    rw [one_mul] at hy3 ⊢
    exact S.key3_K₂ b' hb' hy3
  · by_cases hB : b' = 1
    · subst hB
      rw [mul_one] at hy3 ⊢
      exact S.key3_K₁ a' ha' hy3
    · exact S.key3_mixed ha' hb' (orderOf_eq_prime ha3 hA) (orderOf_eq_prime hb3 hB)

end Fin

end Q9Setting

end CFSG.GH74.GLS.Stage4.Q9
