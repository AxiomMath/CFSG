module

public import CFSG.GF2Type.CenterFour.CaseBFusion
public import CFSG.GF2Type.CenterFour.CaseBParity

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

theorem CaseB.centralizes_center_of_odd (hC : Config z n) {y : G}
    (hyH : y ∈ centralizer ({z} : Set G)) (hodd : Odd (orderOf y)) :
    y ∈ centralizer (centerAt z : Set G) := by
  by_contra hK
  obtain ⟨t, ht⟩ := hodd
  have h2 : y * y ∈ centralizer (centerAt z : Set G) :=
    hC.mul_mem_centralizer hyH hyH hK hK
  have hy : (y * y) ^ (t + 1) = y := by
    rw [← sq, ← pow_mul, show 2 * (t + 1) = orderOf y + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have h3 := pow_mem h2 (t + 1)
  rw [hy] at h3
  exact hK h3

theorem Config.eq_one_of_odd_mem_core (hC : Config z n) {y : G} (hy : y ∈ coreAt z)
    (hodd : Odd (orderOf y)) : y = 1 := by
  have hdvd : orderOf (⟨y, hy⟩ : coreAt z) ∣ Nat.card (coreAt z) := orderOf_dvd_natCard _
  rw [hC.card_core, Subgroup.orderOf_mk] at hdvd
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hyone : orderOf y = 1 := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [hi, h0, pow_zero]
    · exfalso
      have h2 : 2 ∣ orderOf y := by
        rw [hi]
        exact dvd_pow_self 2 hpos.ne'
      obtain ⟨t, ht⟩ := hodd
      omega
  exact orderOf_eq_one_iff.mp hyone

theorem CaseB.d_commute (hC : Config z n) {y q r : G} (hyz : y * z = z * y)
    (hyr : r * y = y * r) (hq : q ∈ coreAt z) (hr : r ∈ coreAt z) :
    (q⁻¹ * (y * q * y⁻¹)) * r = r * (q⁻¹ * (y * q * y⁻¹)) := by
  have hyc : ∀ c : G, (c = 1 ∨ c = z) → y * c * y⁻¹ = c := by
    rintro c (h | h) <;> rw [h]
    · group
    · rw [hyz]
      group
  have hyr' : y * r * y⁻¹ = r := by
    rw [← hyr]
    group
  have h1 : q * r = ⁅q, r⁆ * r * q := by
    rw [commutatorElement_def]
    group
  have h4 : q⁻¹ * ⁅q, r⁆ * r = r * q⁻¹ := by
    rw [commutatorElement_def]
    group
  have hc := hyc _ (hC.comm_eq q hq r hr)
  have h3 : y * q * y⁻¹ * r = ⁅q, r⁆ * r * (y * q * y⁻¹) := by
    calc y * q * y⁻¹ * r = y * q * y⁻¹ * (y * r * y⁻¹) := by rw [hyr']
      _ = y * (q * r) * y⁻¹ := by group
      _ = y * (⁅q, r⁆ * r * q) * y⁻¹ := by rw [h1]
      _ = (y * ⁅q, r⁆ * y⁻¹) * (y * r * y⁻¹) * (y * q * y⁻¹) := by group
      _ = ⁅q, r⁆ * r * (y * q * y⁻¹) := by rw [hc, hyr']
  calc (q⁻¹ * (y * q * y⁻¹)) * r = q⁻¹ * (y * q * y⁻¹ * r) := by group
    _ = q⁻¹ * (⁅q, r⁆ * r * (y * q * y⁻¹)) := by rw [h3]
    _ = (q⁻¹ * ⁅q, r⁆ * r) * (y * q * y⁻¹) := by group
    _ = (r * q⁻¹) * (y * q * y⁻¹) := by rw [h4]
    _ = r * (q⁻¹ * (y * q * y⁻¹)) := by group

theorem CaseB.commute_pow_four {y q d : G} (hyz : y * z = z * y) (hyq : y * q = q * d * y)
    (hyd : y * d = d * y) (hw : d ^ 2 = 1 ∨ d ^ 2 = z) (hzsq : z ^ 2 = 1) :
    y ^ 4 * q = q * y ^ 4 := by
  have hw' : d * d = 1 ∨ d * d = z := by
    rw [← sq]
    exact hw
  have hzsq' : z * z = 1 := by
    rw [← sq]
    exact hzsq
  have h4 : y ^ 4 = y * y * y * y := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h4]
  have hyd2 : y * (d * d) = (d * d) * y := by
    rcases hw' with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]
      exact hyz
  have hyy : y * y * (d * d) = (d * d) * (y * y) := by
    calc y * y * (d * d) = y * (y * (d * d)) := by simp only [mul_assoc]
      _ = y * ((d * d) * y) := by rw [hyd2]
      _ = (y * (d * d)) * y := by simp only [mul_assoc]
      _ = ((d * d) * y) * y := by rw [hyd2]
      _ = (d * d) * (y * y) := by simp only [mul_assoc]
  have hd4 : (d * d) * (d * d) = 1 := by
    rcases hw' with h | h
    · rw [h, one_mul]
    · rw [h]
      exact hzsq'
  have e1 : y * y * q = q * (d * d) * (y * y) := by
    calc y * y * q = y * (y * q) := by simp only [mul_assoc]
      _ = y * (q * d * y) := by rw [hyq]
      _ = (y * q) * d * y := by simp only [mul_assoc]
      _ = q * d * y * d * y := by rw [hyq]
      _ = q * d * (y * d) * y := by simp only [mul_assoc]
      _ = q * d * (d * y) * y := by rw [hyd]
      _ = q * (d * d) * (y * y) := by simp only [mul_assoc]
  calc y * y * y * y * q = y * y * (y * y * q) := by simp only [mul_assoc]
    _ = y * y * (q * (d * d) * (y * y)) := by rw [e1]
    _ = (y * y * q) * (d * d) * (y * y) := by simp only [mul_assoc]
    _ = q * (d * d) * (y * y) * (d * d) * (y * y) := by rw [e1]
    _ = q * (d * d) * ((y * y) * (d * d)) * (y * y) := by simp only [mul_assoc]
    _ = q * (d * d) * ((d * d) * (y * y)) * (y * y) := by rw [hyy]
    _ = q * ((d * d) * (d * d)) * (y * y * y * y) := by simp only [mul_assoc]
    _ = q * (y * y * y * y) := by rw [hd4, mul_one]

theorem CaseB.commute_of_pow_four {y q : G} (hodd : Odd (orderOf y))
    (h : Commute (y ^ 4) q) : Commute y q := by
  obtain ⟨t, ht⟩ := hodd
  have h1 : (y ^ 4) ^ (t + 1) = y ^ 2 := by
    rw [← pow_mul, show 4 * (t + 1) = orderOf y + orderOf y + 2 by omega, pow_add, pow_add,
      pow_orderOf_eq_one]
    simp
  have h2 : (y ^ 2) ^ (t + 1) = y := by
    rw [← pow_mul, show 2 * (t + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have h3 : Commute (y ^ 2) q := by
    rw [← h1]
    exact h.pow_left (t + 1)
  rw [← h2]
  exact h3.pow_left (t + 1)

theorem CaseB.centralizer_sup_le {H K : Subgroup G} {y : G}
    (hH : y ∈ centralizer (H : Set G)) (hK : y ∈ centralizer (K : Set G)) :
    H ⊔ K ≤ centralizer ({y} : Set G) := by
  refine sup_le ?_ ?_
  · intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hH x hx)
  · intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hK x hx)

theorem CaseB.d_mem_sup (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {y : G}
    (hyz : y * z = z * y)
    (hy : y ∈ centralizer (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Set G))
    {q : G} (hq : q ∈ coreAt z) :
    q⁻¹ * (y * q * y⁻¹) ∈ (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z := by
  have hyH : y ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hyz
  have hd : q⁻¹ * (y * q * y⁻¹) ∈ coreAt z := mul_mem (inv_mem hq) (hC.conj_mem_core hyH hq)
  refine CaseB.mem_sup_of_commute hC hH hK hd (fun r hr => ?_)
  exact CaseB.d_commute hC hyz (Subgroup.mem_centralizer_iff.mp hy r hr) hq
    (Subgroup.mem_inf.mp hr).1

theorem CaseB.commute_core_of_odd (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {y : G}
    (hyz : y * z = z * y)
    (hy : y ∈ centralizer (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Set G))
    (hyH : y ∈ centralizer ({z} : Set G))
    (hyZ : y ∈ centralizer (centerAt z : Set G)) (hodd : Odd (orderOf y))
    {q : G} (hq : q ∈ coreAt z) : y * q = q * y := by
  have hsup : (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z ≤
      centralizer ({y} : Set G) :=
    CaseB.centralizer_sup_le hy hyZ
  have hdsup := CaseB.d_mem_sup hC hH hK hyz hy hq
  have hdQ : q⁻¹ * (y * q * y⁻¹) ∈ coreAt z :=
    mul_mem (inv_mem hq) (hC.conj_mem_core hyH hq)
  have hyd : y * (q⁻¹ * (y * q * y⁻¹)) = (q⁻¹ * (y * q * y⁻¹)) * y :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hsup hdsup)).symm
  have hyq : y * q = q * (q⁻¹ * (y * q * y⁻¹)) * y := by group
  have hzsq : z ^ 2 = 1 := by
    rw [← hC.orderOf_eq]
    exact pow_orderOf_eq_one z
  have h4 := CaseB.commute_pow_four hyz hyq hyd (hC.sq_eq _ hdQ) hzsq
  exact CaseB.commute_of_pow_four hodd h4

theorem CaseB.eq_one_of_odd (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {y : G}
    (hy : y ∈ centralizer (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Set G))
    (hodd : Odd (orderOf y)) : y = 1 := by
  have hzR : z ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) := CaseB.mem hC hH
  have hyz : y * z = z * y := (Subgroup.mem_centralizer_iff.mp hy z hzR).symm
  have hyH : y ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hyz
  have hyZ : y ∈ centralizer (centerAt z : Set G) := CaseB.centralizes_center_of_odd hC hyH hodd
  have hyQ : y ∈ coreAt z :=
    hC.selfCentralizing y hyH
      (fun q hq => CaseB.commute_core_of_odd hC hH hK hyz hy hyH hyZ hodd hq)
  exact hC.eq_one_of_odd_mem_core hyQ hodd

theorem CaseB.conj_mul_self_eq_one (hC : Config z n) (g : G) :
    (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
  have hz2 : z * z = 1 := by
    rw [← sq, ← hC.orderOf_eq]
    exact pow_orderOf_eq_one z
  calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
    _ = 1 := by rw [hz2]; group

theorem CaseB.mul_psi_eq (hC : Config z n) (g q : G) :
    (g⁻¹ * z * g) * psi (g⁻¹ * z * g) q = q * (g⁻¹ * z * g) * q⁻¹ := by
  unfold psi
  calc (g⁻¹ * z * g) * ((g⁻¹ * z * g) * (q * (g⁻¹ * z * g) * q⁻¹))
      = ((g⁻¹ * z * g) * (g⁻¹ * z * g)) * (q * (g⁻¹ * z * g) * q⁻¹) := by group
    _ = q * (g⁻¹ * z * g) * q⁻¹ := by rw [CaseB.conj_mul_self_eq_one hC g, one_mul]

theorem CaseB.fused_of_mem_R₁ (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G))
    (hall : ∀ q ∈ coreAt z, psi (g⁻¹ * z * g) q ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G))
    {r : G} (hr : r ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) (hr1 : r ≠ 1) :
    Fused z r := by
  obtain ⟨q, hq, rfl⟩ := CaseB.exists_psi_eq hC hH hK hall hr
  refine CaseB.fused_of_fused_mul hC hH hK (hall q hq) hr1 ?_
  refine ⟨g * q⁻¹, ?_⟩
  rw [CaseB.mul_psi_eq hC g q]
  group

theorem CaseB.le_core_of_normal_two {N : Subgroup G}
    (hN : N ≤ centralizer ({z} : Set G))
    (hnorm : ∀ h ∈ centralizer ({z} : Set G), ∀ x ∈ N, h * x * h⁻¹ ∈ N)
    (hp : IsPGroup 2 N) : N ≤ coreAt z := by
  have hnormal : (N.subgroupOf (centralizer ({z} : Set G))).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hnorm (g : G) g.2 a ha
  have hp' : IsPGroup 2 (N.subgroupOf (centralizer ({z} : Set G))) := by
    intro g
    obtain ⟨k, hk⟩ := hp ⟨(g : G), Subgroup.mem_subgroupOf.mp g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hle : N.subgroupOf (centralizer ({z} : Set G)) ≤
      CFSG.pCore 2 (centralizer ({z} : Set G)) :=
    le_sSup ⟨hnormal, hp'⟩
  intro x hx
  have hmem : (⟨x, hN hx⟩ : ↥(centralizer ({z} : Set G))) ∈
      N.subgroupOf (centralizer ({z} : Set G)) :=
    Subgroup.mem_subgroupOf.mpr hx
  unfold coreAt CFSG.inSubgroup
  exact Subgroup.mem_map.mpr ⟨⟨x, hN hx⟩, hle hmem, rfl⟩

theorem CaseB.isPGroup_centralizer_R1 (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) :
    IsPGroup 2 (centralizer (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Set G)) := by
  rw [IsPGroup.iff_card]
  have hne : Nat.card (centralizer (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Set G)) ≠ 0 :=
    Nat.card_pos.ne'
  have hprime : ∀ {d : ℕ}, d.Prime →
      d ∣ Nat.card (centralizer (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Set G)) →
      d = 2 := by
    intro d hd hdvd
    by_contra hd2
    haveI : Fact d.Prime := ⟨hd⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' d hdvd
    have hodd : Odd (orderOf (y : G)) := by
      rw [Subgroup.orderOf_coe, hy]
      exact hd.odd_of_ne_two hd2
    have h2 : (y : G) = 1 := CaseB.eq_one_of_odd hC hH hK y.2 hodd
    have h3 : y = 1 := Subtype.ext h2
    rw [h3, orderOf_one] at hy
    have := hd.two_le
    omega
  exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hne (fun hd hdvd => hprime hd hdvd)⟩

theorem CaseB.not_normal_R1 (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) :
    ¬ (∀ h ∈ centralizer ({z} : Set G),
      ∀ x ∈ (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G),
        h * x * h⁻¹ ∈ (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G)) := by
  intro hnorm
  have hzR : z ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) := CaseB.mem hC hH
  have hNH : centralizer ((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) :
      Set G) ≤ centralizer ({z} : Set G) := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hy z hzR).symm
  have hNnorm : ∀ h ∈ centralizer ({z} : Set G),
      ∀ y ∈ centralizer ((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) : Set G),
        h * y * h⁻¹ ∈ centralizer ((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) :
          Set G) := by
    intro h hh y hy
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : r ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) := hr
    have hr'' : h⁻¹ * r * h ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) := by
      have := hnorm h⁻¹ (inv_mem hh) r hr'
      rwa [inv_inv] at this
    have key := Subgroup.mem_centralizer_iff.mp hy (h⁻¹ * r * h) hr''
    calc r * (h * y * h⁻¹) = h * ((h⁻¹ * r * h) * y) * h⁻¹ := by group
      _ = h * (y * (h⁻¹ * r * h)) * h⁻¹ := by rw [key]
      _ = (h * y * h⁻¹) * r := by group
  have hcore := CaseB.le_core_of_normal_two hNH hNnorm
    (CaseB.isPGroup_centralizer_R1 hC hH hK)
  have hz1 : g⁻¹ * z * g ∈ centralizer ((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) :
      Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : r ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) := hr
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hr').2
  exact CaseB.not_mem_core hC hK (hcore hz1)

theorem CaseB.exists_fused_outside (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G))
    (hall : ∀ q ∈ coreAt z,
      psi (g⁻¹ * z * g) q ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) :
    ∃ x ∈ coreAt z, Fused z x ∧ x ∉ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) := by
  by_contra hcon
  push_neg at hcon
  apply CaseB.not_normal_R1 hC hH hK
  intro h hh r hr
  by_cases hr1 : r = 1
  · subst hr1
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  · have hF : Fused z r := CaseB.fused_of_mem_R₁ hC hH hK hall hr hr1
    have hQ : r ∈ coreAt z := (Subgroup.mem_inf.mp hr).1
    have hconjQ : h * r * h⁻¹ ∈ coreAt z := hC.conj_mem_core hh hQ
    apply hcon _ hconjQ
    obtain ⟨k, hk⟩ := hF
    refine ⟨k * h⁻¹, ?_⟩
    rw [← hk]
    group

theorem CaseB.mem_core_iff_centerAt_le {u : G} (hu : Config u n) {w x : G}
    (hx : w⁻¹ * u * w = x) :
    x ∈ coreAt u ↔ centerAt x ≤ centralizer ({u} : Set G) := by
  subst hx
  rw [centerAt_conj]
  exact (hu.center_le_iff w).symm

theorem CaseB.card_le_two_mul_inf (J K : Subgroup G)
    (hA : ∀ x ∈ J, ∀ y ∈ J, x ∉ K → y ∉ K → x * y ∈ K) :
    Nat.card J ≤ 2 * Nat.card (J ⊓ K : Subgroup G) := by
  classical
  by_cases hJK : J ≤ K
  · rw [inf_eq_left.mpr hJK]
    omega
  obtain ⟨x₀, hx₀J, hx₀K⟩ := SetLike.not_le_iff_exists.mp hJK
  have hinvJ : x₀⁻¹ ∈ J := J.inv_mem hx₀J
  have hinvK : x₀⁻¹ ∉ K := fun h => hx₀K (by simpa using K.inv_mem h)
  let F : J → Bool × (J ⊓ K : Subgroup G) := fun x =>
    if hx : (x : G) ∈ K then (true, ⟨x, Subgroup.mem_inf.mpr ⟨x.2, hx⟩⟩)
    else (false, ⟨x₀⁻¹ * x, Subgroup.mem_inf.mpr ⟨J.mul_mem hinvJ x.2, hA _ hinvJ _ x.2 hinvK hx⟩⟩)
  have hF : Function.Injective F := by
    intro x y hxy
    by_cases hx : (x : G) ∈ K <;> by_cases hy : (y : G) ∈ K <;> simp [F, hx, hy] at hxy
    · exact hxy
    · exact hxy
  have h := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h

theorem CaseB.mul_mem_centralizer_of_core (hC : Config z n) {t x y : G} (ht : t ∈ coreAt z)
    (hx : x ∈ coreAt z) (hy : y ∈ coreAt z) (hxt : x ∉ centralizer ({t} : Set G))
    (hyt : y ∉ centralizer ({t} : Set G)) : x * y ∈ centralizer ({t} : Set G) := by
  have hz2 : z * z = 1 := by
    rw [← sq, ← hC.orderOf_eq]
    exact pow_orderOf_eq_one z
  have key : ∀ w ∈ coreAt z, w ∉ centralizer ({t} : Set G) → ⁅t, w⁆ = z := by
    intro w hw hwt
    rcases hC.comm_eq t ht w hw with h | h
    · exact absurd (Subgroup.mem_centralizer_singleton_iff.mpr
        (commutatorElement_eq_one_iff_mul_comm.mp h).symm) hwt
    · exact h
  have h1 : ⁅t, x * y⁆ = 1 := by
    rw [hC.commutator_mul ht hx hy, key x hx hxt, key y hy hyt, hz2]
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

theorem CaseB.card_le_two_of_subset {T : Subgroup G} {c : G} (h : ∀ j ∈ T, j = 1 ∨ j = c) :
    Nat.card T ≤ 2 := by
  have hsub : (T : Set G) ⊆ {1, c} := fun j hj => h j hj
  calc Nat.card T = (T : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, c} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({c} : Set G).ncard + 1 := Set.ncard_insert_le 1 {c}
    _ = 2 := by rw [Set.ncard_singleton]

theorem CaseB.eq_comm_of_mem_K (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G))
    (hall : ∀ q ∈ coreAt z,
      psi (g⁻¹ * z * g) q ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G))
    {x : G} (hxF : Fused z x) (hxc : x ∉ centralizer ({g⁻¹ * z * g} : Set G)) {j : G}
    (hjR : j ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G))
    (hjK1 : j ∈ centralizer (centerAt (g⁻¹ * z * g) : Set G))
    (hjK2 : j ∈ centralizer (centerAt x : Set G)) : j = 1 ∨ j = ⁅g⁻¹ * z * g, x⁆ := by
  by_cases hj1 : j = 1
  · exact Or.inl hj1
  right
  have hFj : Fused z j := CaseB.fused_of_mem_R₁ hC hH hK hall hjR hj1
  have hCj : Config j n := by
    obtain ⟨h, hh⟩ := hFj
    rw [← hh]
    exact hC.conj h
  have hle : ∀ {u : G}, j ∈ centralizer (centerAt u : Set G) →
      centerAt u ≤ centralizer ({j} : Set G) := fun hu y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hu y hy)
  obtain ⟨w₁, hw₁⟩ := hFj.symm.trans (fused_conj z g)
  obtain ⟨w₂, hw₂⟩ := hFj.symm.trans hxF
  have hz1Q : g⁻¹ * z * g ∈ coreAt j :=
    (CaseB.mem_core_iff_centerAt_le hCj hw₁).mpr (hle hjK1)
  have hxQ : x ∈ coreAt j := (CaseB.mem_core_iff_centerAt_le hCj hw₂).mpr (hle hjK2)
  rcases hCj.comm_eq _ hz1Q _ hxQ with h | h
  · exact absurd (show x ∈ centralizer ({g⁻¹ * z * g} : Set G) from
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commutatorElement_eq_one_iff_mul_comm.mp h).symm) hxc
  · exact h.symm

theorem CaseB.false_of_forall_mem (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G))
    (hall : ∀ q ∈ coreAt z,
      psi (g⁻¹ * z * g) q ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) : False := by
  obtain ⟨x, hxQ, hxF, hxR⟩ := CaseB.exists_fused_outside hC hH hK hall
  have hxc : x ∉ centralizer ({g⁻¹ * z * g} : Set G) := fun h =>
    hxR (Subgroup.mem_inf.mpr ⟨hxQ, h⟩)
  have hCx : Config x n := by
    obtain ⟨k, hk⟩ := hxF
    rw [← hk]
    exact hC.conj k
  have h1 := CaseB.card_le_two_mul_inf (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G))
    (centralizer ({x} : Set G)) (fun a ha b hb haK hbK =>
      CaseB.mul_mem_centralizer_of_core hC hxQ (Subgroup.mem_inf.mp ha).1
        (Subgroup.mem_inf.mp hb).1 haK hbK)
  have h2 := CaseB.card_le_two_mul_inf
    (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊓ centralizer ({x} : Set G))
    (centralizer (centerAt (g⁻¹ * z * g) : Set G)) (fun a ha b hb haK hbK =>
      (hC.conj g).mul_mem_centralizer (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).1).2
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).2 haK hbK)
  have h3 := CaseB.card_le_two_mul_inf
    (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊓ centralizer ({x} : Set G) ⊓
      centralizer (centerAt (g⁻¹ * z * g) : Set G))
    (centralizer (centerAt x : Set G)) (fun a ha b hb haK hbK =>
      hCx.mul_mem_centralizer (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).1).2
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).2 haK hbK)
  have h4 : Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊓
      centralizer ({x} : Set G) ⊓ centralizer (centerAt (g⁻¹ * z * g) : Set G) ⊓
      centralizer (centerAt x : Set G) : Subgroup G) ≤ 2 := by
    refine CaseB.card_le_two_of_subset (c := ⁅g⁻¹ * z * g, x⁆) (fun j hj => ?_)
    obtain ⟨hj', hjK2⟩ := Subgroup.mem_inf.mp hj
    obtain ⟨hj'', hjK1⟩ := Subgroup.mem_inf.mp hj'
    exact CaseB.eq_comm_of_mem_K hC hH hK hall hxF hxc (Subgroup.mem_inf.mp hj'').1 hjK1 hjK2
  have hR := CaseB.card hC hH hK
  have hn3 : n ≤ 3 := by
    by_contra hn
    have h32 : 32 ≤ 2 ^ (n + 1) := by
      calc (32 : ℕ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨m, hm⟩ := CaseB.even_of_forall_mem hC hH hK hall
  have := hC.three_le
  omega

end CFSG.GF2Type.CenterFour
