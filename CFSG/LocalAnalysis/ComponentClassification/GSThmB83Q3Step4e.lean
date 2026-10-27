module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step4d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step4b
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step4c

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

namespace Q3Data

variable (d : Q3Data H)
include d

theorem b_mem_R0 : d.b ∈ d.R0 :=
  ⟨mem_sup_right (d.B_eq ▸ mem_zpowers d.b), mem_centralizer_singleton_iff.mpr d.b_comm_z⟩

theorem R0_le_centralizer_b : d.R0 ≤ centralizer ({d.b} : Set X) := fun _ hr =>
  d.R_le_centralizer_b hr.1

theorem b_comm_of_mem_M3 {m : X} (hm : m ∈ h.M3) : m * d.b = d.b * m :=
  mem_centralizer_iff.mp d.b_mem_centralizer_M3 m hm

theorem card_le_two_subgroup_bz {A : Subgroup X} (hA : IsPGroup 2 A)
    (hAb : A ≤ centralizer ({d.b} : Set X))
    (hAz : A ≤ centralizer ({d.z} : Set X)) : Nat.card A ≤ 128 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAN : A ≤ normalizer (h.K : Set X) := hAb.trans d.centralizer_b_le
  let φ : A →* MulAut (h.K ⧸ pPrimeCore 2 h.K) := (Eight.oddBarAction h.K).comp (inclusion hAN)
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hzN : d.z ∈ normalizer (h.K : Set X) :=
    Eight.sup_zpowers_le_normalizer H.a_mem_normalizer_K (H.D_le_M3 d.z_D)
  have hcz : d.c.z = Eight.oddBarAction h.K ⟨d.z, hzN⟩ := d.c_z
  have hrange : Nat.card φ.range ≤ 64 := by
    have hle : φ.range ≤ centralizer ({d.c.z} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K))) := by
      rintro _ ⟨y, rfl⟩
      rw [mem_centralizer_singleton_iff, hcz]
      change Eight.oddBarAction h.K ⟨(y : X), hAN y.2⟩ * _ =
        _ * Eight.oddBarAction h.K ⟨(y : X), hAN y.2⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (hAz y.2))
    have h2 : IsPGroup 2 φ.range := by
      rw [MonoidHom.range_eq_map]
      exact (hA.to_subgroup ⊤).map φ
    have h3 := card_le_of_sylow_subgroupOf d.c_props.R0_sylow.2 hle h2
    rwa [d.c_props.R0_sylow.1] at h3
  have hker : Nat.card φ.ker ≤ 2 := by
    have hk : φ.ker.map A.subtype ≤ coreActionKernel h.V := by
      rintro _ ⟨y, hy, rfl⟩
      rw [H.V_eq_K]
      exact Eight.mem_ker_oddBarAction.mp hy
    have h2 := card_le_of_sylow_subgroupOf H.B_sylow_kernel.2 hk
      ((hA.to_subgroup φ.ker).map A.subtype)
    rw [card_map_of_injective A.subtype_injective, d.card_B] at h2
    exact h2
  have h3 : Nat.card A ≤ 2 * 64 := by
    rw [← h1]
    exact Nat.mul_le_mul hker hrange
  omega

theorem mem_center_R0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {y : X}
    (hy : y ∈ d.R0) (hc : ∀ r ∈ d.R0, y * r = r * y) :
    ∃ m : X, (m = 1 ∨ m = d.z ∨ m = d.tau ∨ m = d.tau * d.z) ∧ (y = m ∨ y = m * d.b) := by
  rw [d.R0_eq, d.B_eq] at hy
  have hbN : d.b ∈ normalizer (d.R0M : Set X) :=
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      d.b_comm_of_mem_M3 (d.RM_le hr.1))
  obtain ⟨m, hm, hym⟩ := Eight.mem_sup_zpowers_cases hbN d.b_mul_self hy
  refine ⟨m, d.mem_center_R0M hCF1 hCF2 hm fun r hr => ?_, hym⟩
  have hr0 : r ∈ d.R0 := by
    rw [d.R0_eq]
    exact mem_sup_left hr
  have h1 := hc r hr0
  have hrb := d.b_comm_of_mem_M3 (d.RM_le hr.1)
  rcases hym with rfl | rfl
  · exact h1
  · have h2 : m * r * d.b = r * m * d.b := by
      calc m * r * d.b = m * (r * d.b) := by group
        _ = m * (d.b * r) := by rw [hrb]
        _ = m * d.b * r := by group
        _ = r * (m * d.b) := h1
        _ = r * m * d.b := by group
    exact mul_right_cancel h2

theorem bz_conj_xgx (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    (h.x * d.g * h.x)⁻¹ * (d.b * d.z) * (h.x * d.g * h.x) = d.tau * d.b := by
  have key : ∀ s u v : X, s⁻¹ * (u * v) * s = (s⁻¹ * u * s) * (s⁻¹ * v * s) := fun s u v => by
    group
  have hgb : d.g⁻¹ * d.b * d.g = d.b := by
    have := mem_centralizer_singleton_iff.mp (d.K_le_centralizer_b d.g_K)
    rw [mul_assoc, ← this, inv_mul_cancel_left]
  have hxz := d.z_x hq hF.simple hF.inner hF.l0 hF.sylowCent
  have hzg := d.z_g hF.simple hF.inner
  have e1 : h.x⁻¹ * (d.b * d.z) * h.x = h.a * d.b * d.z := by rw [key, d.xbx, hxz]
  have e2 : d.g⁻¹ * (h.a * d.b * d.z) * d.g = h.a * d.tau * d.b * d.z := by
    rw [key, key, d.a_g, hgb, hzg]
  have e3 : h.x⁻¹ * (h.a * d.tau * d.b * d.z) * h.x =
      h.a * (d.tau * d.z) * (h.a * d.b) * d.z := by
    rw [key, key, key, H.a_x, d.tz_eq_conj hq hF, d.xbx, hxz]
  have hta := d.tau_comm_a
  have hza := d.z_comm_a
  have h1 : h.a * (d.tau * d.z) = d.tau * d.z * h.a := by
    rw [← mul_assoc, ← hta, mul_assoc, ← hza, ← mul_assoc]
  rw [show (h.x * d.g * h.x)⁻¹ * (d.b * d.z) * (h.x * d.g * h.x) =
      h.x⁻¹ * (d.g⁻¹ * (h.x⁻¹ * (d.b * d.z) * h.x) * d.g) * h.x by group, e1, e2, e3]
  calc h.a * (d.tau * d.z) * (h.a * d.b) * d.z = d.tau * d.z * h.a * (h.a * d.b) * d.z := by
        rw [h1]
    _ = d.tau * (d.z * (h.a * h.a) * d.b) * d.z := by group
    _ = d.tau * (d.z * d.b) * d.z := by rw [Six.a_mul_a_self h, mul_one]
    _ = d.tau * (d.b * d.z) * d.z := by rw [← d.b_comm_z]
    _ = d.tau * d.b := by
        rw [mul_assoc d.tau (d.b * d.z) d.z, mul_assoc d.b d.z d.z, d.z_sq, mul_one]

theorem conj_b_cases (hq : h.IsQ3) (hF : Cat8.Q3Facts) {n : X}
    (hn : n ∈ normalizer (d.R0 : Set X)) :
    n * d.b * n⁻¹ = d.b ∨ n * d.b * n⁻¹ = d.tau * d.z * d.b := by
  have hbR := d.b_mem_R0
  have hnb : n * d.b * n⁻¹ ∈ d.R0 := (mem_normalizer_iff.mp hn d.b).mp hbR
  have hcen : ∀ r ∈ d.R0, n * d.b * n⁻¹ * r = r * (n * d.b * n⁻¹) := by
    intro r hr
    have hr' : n⁻¹ * r * n ∈ d.R0 := by
      have := (mem_normalizer_iff.mp (inv_mem hn) r).mp hr
      rwa [inv_inv] at this
    have h1 := mem_centralizer_singleton_iff.mp (d.R0_le_centralizer_b hr')
    calc n * d.b * n⁻¹ * r = n * (d.b * (n⁻¹ * r * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * r * n) * d.b) * n⁻¹ := by rw [h1]
      _ = r * (n * d.b * n⁻¹) := by group
  have hntz := d.b_not_conj_tz hq hF.simple hF.inner hF.out
  have hnbz := d.b_not_conj_bz hq hF.simple hF.inner hF.innerInv hF.noNilp
  have hconj : n⁻¹⁻¹ * d.b * n⁻¹ = n * d.b * n⁻¹ := by rw [inv_inv]
  obtain ⟨c, hc⟩ := d.exists_z_conj_tz hq hF
  obtain ⟨m, hm, hym⟩ := d.mem_center_R0 hF.simple hF.inner hnb hcen
  rcases hym with hym | hym <;> rcases hm with rfl | rfl | rfl | rfl
  · exfalso
    have : d.b = 1 := by
      calc d.b = n⁻¹ * (n * d.b * n⁻¹) * n := by group
        _ = 1 := by rw [hym]; group
    have h2 := d.b_ord
    rw [this, orderOf_one] at h2
    norm_num at h2
  · exfalso
    apply hntz (n⁻¹ * c)
    rw [show (n⁻¹ * c)⁻¹ * d.b * (n⁻¹ * c) = c⁻¹ * (n * d.b * n⁻¹) * c by group, hym, hc]
  · exfalso
    apply hntz (n⁻¹ * h.x)
    rw [show (n⁻¹ * h.x)⁻¹ * d.b * (n⁻¹ * h.x) = h.x⁻¹ * (n * d.b * n⁻¹) * h.x by group, hym,
      d.tz_eq_conj hq hF]
  · exact absurd (hconj.trans hym) (hntz n⁻¹)
  · left
    rw [hym, one_mul]
  · exfalso
    apply hnbz n⁻¹
    rw [hconj, hym, d.b_comm_z]
  · exfalso
    apply hnbz (n⁻¹ * (h.x * d.g * h.x)⁻¹)
    have h2 := d.bz_conj_xgx hq hF
    rw [show (n⁻¹ * (h.x * d.g * h.x)⁻¹)⁻¹ * d.b * (n⁻¹ * (h.x * d.g * h.x)⁻¹) =
      (h.x * d.g * h.x) * (n * d.b * n⁻¹) * (h.x * d.g * h.x)⁻¹ by group, hym, ← h2]
    group
  · right
    exact hym

theorem mem_R0_of_conj_b (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    {T : Subgroup X} (hT : IsPGroup 2 T) (hR0T : d.R0 ≤ T)
    (hTC : T ≤ centralizer ({d.b * d.z} : Set X)) {n : X} (hn : n ∈ T)
    (hnb : n * d.b * n⁻¹ = d.b) : n ∈ d.R0 := by
  have hnb' : n * d.b = d.b * n := by
    calc n * d.b = n * d.b * n⁻¹ * n := by group
      _ = d.b * n := by rw [hnb]
  have hnz : n * d.z = d.z * n := by
    have h1 := mem_centralizer_singleton_iff.mp (hTC hn)
    have h2 : d.b * (n * d.z) = d.b * (d.z * n) := by
      calc d.b * (n * d.z) = n * d.b * d.z := by rw [← mul_assoc, hnb']
        _ = n * (d.b * d.z) := by group
        _ = d.b * d.z * n := h1
        _ = d.b * (d.z * n) := by group
    exact mul_left_cancel h2
  set U := d.R0 ⊔ zpowers n with hU
  have hUT : U ≤ T := sup_le hR0T (zpowers_le.mpr hn)
  have hUb : U ≤ centralizer ({d.b} : Set X) :=
    sup_le d.R0_le_centralizer_b (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hnb'))
  have hUz : U ≤ centralizer ({d.z} : Set X) :=
    sup_le inf_le_right (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hnz))
  have h1 := d.card_le_two_subgroup_bz (hT.to_le hUT) hUb hUz
  have h2 : U = d.R0 := (eq_of_le_of_card_ge le_sup_left (by
    rw [d.card_R0 hCF1 hCF2]
    exact h1)).symm
  rw [← h2]
  exact mem_sup_right (mem_zpowers n)

variable {T : Subgroup X}

abbrev NT (T : Subgroup X) : Subgroup X := T ⊓ normalizer (d.R0 : Set X)

theorem conj_of_not_mem (hq : h.IsQ3) (hF : Cat8.Q3Facts) (hT : IsPGroup 2 T)
    (hR0T : d.R0 ≤ T) (hTC : T ≤ centralizer ({d.b * d.z} : Set X)) {u : X} (hu : u ∈ d.NT T)
    (huR : u ∉ d.R0) : u * d.b * u⁻¹ = d.tau * d.z * d.b ∧ u * d.z * u⁻¹ = d.tau := by
  have hub : u * d.b * u⁻¹ = d.tau * d.z * d.b := by
    rcases d.conj_b_cases hq hF hu.2 with h1 | h1
    · exact absurd (d.mem_R0_of_conj_b hF.simple hF.inner hT hR0T hTC hu.1 h1) huR
    · exact h1
  refine ⟨hub, ?_⟩
  have h1 := mem_centralizer_singleton_iff.mp (hTC hu.1)
  have hubz : u * (d.b * d.z) * u⁻¹ = d.b * d.z := by rw [h1, mul_inv_cancel_right]
  have hbt := d.b_comm_of_mem_M3 d.tau_mem.2
  have htz := d.tau_comm_z hF.simple hF.inner
  calc u * d.z * u⁻¹ = (u * d.b * u⁻¹)⁻¹ * (u * (d.b * d.z) * u⁻¹) := by group
    _ = (d.tau * d.z * d.b)⁻¹ * (d.b * d.z) := by rw [hub, hubz]
    _ = d.b⁻¹ * (d.z⁻¹ * (d.tau⁻¹ * d.b) * d.z) := by group
    _ = d.b⁻¹ * (d.z⁻¹ * (d.tau * d.b) * d.z) := by
        rw [inv_eq_of_mul_eq_one_right d.tau_sq]
    _ = d.b⁻¹ * (d.z⁻¹ * (d.b * d.tau) * d.z) := by rw [hbt]
    _ = d.b⁻¹ * d.z⁻¹ * d.b * (d.tau * d.z) := by group
    _ = d.b⁻¹ * d.z⁻¹ * d.b * (d.z * d.tau) := by rw [htz]
    _ = d.b⁻¹ * (d.z⁻¹ * d.b * d.z) * d.tau := by group
    _ = d.b⁻¹ * (d.z⁻¹ * (d.z * d.b)) * d.tau := by rw [mul_assoc d.z⁻¹, d.b_comm_z]
    _ = d.tau := by group

theorem card_N_le (hq : h.IsQ3) (hF : Cat8.Q3Facts) (hT : IsPGroup 2 T) (hR0T : d.R0 ≤ T)
    (hTC : T ≤ centralizer ({d.b * d.z} : Set X)) : Nat.card (d.NT T) ≤ 256 := by
  have h1 := Eight.card_conjOrbit_mul (d.NT T) d.b
  have horb : Cat8.conjOrbit (d.NT T) d.b ⊆ {d.b, d.tau * d.z * d.b} := by
    rintro _ ⟨n, hn, rfl⟩
    have := d.conj_b_cases hq hF (inv_mem hn.2)
    rw [inv_inv] at this
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have h2 : (Cat8.conjOrbit (d.NT T) d.b).ncard ≤ 2 := by
    calc (Cat8.conjOrbit (d.NT T) d.b).ncard ≤ ({d.b, d.tau * d.z * d.b} : Set X).ncard :=
          Set.ncard_le_ncard horb
      _ ≤ ({d.tau * d.z * d.b} : Set X).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have h3 : Nat.card ↥(d.NT T ⊓ centralizer ({d.b} : Set X)) ≤ 128 := by
    rw [← d.card_R0 hF.simple hF.inner]
    refine card_le_of_le fun n hn => d.mem_R0_of_conj_b hF.simple hF.inner hT hR0T hTC hn.1.1 ?_
    rw [mem_centralizer_singleton_iff.mp hn.2, mul_inv_cancel_right]
  rw [← h1]
  calc (Cat8.conjOrbit (d.NT T) d.b).ncard * Nat.card ↥(d.NT T ⊓ centralizer ({d.b} : Set X))
      ≤ 2 * 128 := Nat.mul_le_mul h2 h3
    _ = 256 := by norm_num

theorem E32_le_R0 (hq : h.IsQ3) (hF : Cat8.Q3Facts) (hT : IsPGroup 2 T) (hR0T : d.R0 ≤ T)
    (hTC : T ≤ centralizer ({d.b * d.z} : Set X)) {A : Subgroup X} (hAN : A ≤ d.NT T)
    (hA2 : ∀ y ∈ A, y * y = 1) (hAc : Nat.card A = 32) : A ≤ d.R0 := by
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  by_contra hAR
  obtain ⟨u, huA, huR⟩ := Set.not_subset.mp hAR
  obtain ⟨hub, huz⟩ := d.conj_of_not_mem hq hF hT hR0T hTC (hAN huA) huR
  have hu2 := hA2 u huA
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hut : u * d.tau * u⁻¹ = d.z := by
    calc u * d.tau * u⁻¹ = u * (u * d.z * u⁻¹) * u⁻¹ := by rw [huz]
      _ = (u * u) * d.z * (u * u)⁻¹ := by group
      _ = d.z := by rw [hu2, inv_one, one_mul, mul_one]
  have hcard1 : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ d.R0) := by
    refine Eight.card_le_two_mul_card_inf fun y hy y' hy' hyR hy'R => ?_
    have h1 := (d.conj_of_not_mem hq hF hT hR0T hTC (hAN hy) hyR).1
    have h2 := (d.conj_of_not_mem hq hF hT hR0T hTC (hAN hy') hy'R).1
    refine d.mem_R0_of_conj_b hCF1 hCF2 hT hR0T hTC
      (mul_mem (inv_mem (hAN hy).1) (hAN hy').1) ?_
    calc y⁻¹ * y' * d.b * (y⁻¹ * y')⁻¹ = y⁻¹ * (y' * d.b * y'⁻¹) * y := by group
      _ = y⁻¹ * (y * d.b * y⁻¹) * y := by rw [h1, h2]
      _ = d.b := by group
  have hbN : d.b ∈ normalizer (d.R0M : Set X) :=
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      d.b_comm_of_mem_M3 (d.RM_le hr.1))
  have hcard2 : Nat.card ↥(A ⊓ d.R0) ≤ 2 * Nat.card ↥(A ⊓ d.R0 ⊓ d.R0M) := by
    refine Eight.card_le_two_mul_card_inf fun y hy y' hy' hyR hy'R => ?_
    have hy0 : y ∈ d.R0M ⊔ zpowers d.b := by
      rw [← d.B_eq, ← d.R0_eq]
      exact hy.2
    have hy0' : y' ∈ d.R0M ⊔ zpowers d.b := by
      rw [← d.B_eq, ← d.R0_eq]
      exact hy'.2
    obtain ⟨m, hm, hym⟩ := Eight.mem_sup_zpowers_cases hbN d.b_mul_self hy0
    obtain ⟨m', hm', hym'⟩ := Eight.mem_sup_zpowers_cases hbN d.b_mul_self hy0'
    rcases hym with rfl | rfl
    · exact absurd hm hyR
    rcases hym' with rfl | rfl
    · exact absurd hm' hy'R
    have hb1 := d.b_comm_of_mem_M3 (d.RM_le (mul_mem (inv_mem hm) hm').1)
    have h3 : (m * d.b)⁻¹ * (m' * d.b) = m⁻¹ * m' := by
      calc (m * d.b)⁻¹ * (m' * d.b) = d.b⁻¹ * ((m⁻¹ * m') * d.b) := by group
        _ = d.b⁻¹ * (d.b * (m⁻¹ * m')) := by rw [hb1]
        _ = m⁻¹ * m' := by group
    rw [h3]
    exact mul_mem (inv_mem hm) hm'
  set A₀ := A ⊓ d.R0 ⊓ d.R0M with hA₀
  have hA₀R : A₀ ≤ d.R0M := inf_le_right
  have hA₀A : A₀ ≤ A := inf_le_left.trans inf_le_left
  have hA₀8 : 8 ≤ Nat.card A₀ := by omega
  have hA₀Z : ∀ m ∈ A₀, (∀ r ∈ d.R0M, m * r = r * m) → m = 1 ∨ m = d.tau * d.z := by
    intro m hm hmc
    have hmu : u * m * u⁻¹ = m := by
      rw [Eight.comm_of_mul_self hA2 huA (hA₀A hm), mul_inv_cancel_right]
    rcases d.mem_center_R0M hCF1 hCF2 (hA₀R hm) hmc with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exfalso
      rw [h1, huz] at hmu
      exact d.tau_ne_z hq hCF1 hCF2 hF.l0 hmu
    · exfalso
      rw [h1, hut] at hmu
      exact d.tau_ne_z hq hCF1 hCF2 hF.l0 hmu.symm
    · exact Or.inr h1
  obtain ⟨y, hy, ⟨r₀, hr₀, hyr₀⟩, hcomm⟩ :=
    d.exists_noncentral_comm_z hCF1 hCF2 hA₀R (fun y hy => hA2 y (hA₀A hy)) hA₀8 hA₀Z
  have hyr : y⁻¹ * r₀⁻¹ * y * r₀ = d.z := by
    rcases hcomm r₀ hr₀ with h1 | h1
    · exfalso
      apply hyr₀
      calc y * r₀ = r₀ * y * (y⁻¹ * r₀⁻¹ * y * r₀) := by group
        _ = r₀ * y := by rw [h1, mul_one]
    · exact h1
  have hyu : u * y * u⁻¹ = y := by
    rw [Eight.comm_of_mul_self hA2 huA (hA₀A hy), mul_inv_cancel_right]
  have hr' : u * r₀ * u⁻¹ ∈ d.R0 := by
    have hr0 : r₀ ∈ d.R0 := by
      rw [d.R0_eq]
      exact mem_sup_left hr₀
    exact (mem_normalizer_iff.mp (hAN huA).2 r₀).mp hr0
  have h2 : y⁻¹ * (u * r₀ * u⁻¹)⁻¹ * y * (u * r₀ * u⁻¹) = d.tau := by
    rw [← huz, ← hyr]
    conv_rhs => rw [show u * (y⁻¹ * r₀⁻¹ * y * r₀) * u⁻¹ =
      (u * y * u⁻¹)⁻¹ * (u * r₀ * u⁻¹)⁻¹ * (u * y * u⁻¹) * (u * r₀ * u⁻¹) by group, hyu]
  have hr'' : u * r₀ * u⁻¹ ∈ d.R0M ⊔ zpowers d.b := by
    rw [← d.B_eq, ← d.R0_eq]
    exact hr'
  obtain ⟨m, hm, hrm⟩ := Eight.mem_sup_zpowers_cases hbN d.b_mul_self hr''
  have hym : y⁻¹ * m⁻¹ * y * m = d.tau := by
    rcases hrm with hrm | hrm
    · rw [hrm] at h2
      exact h2
    · rw [hrm] at h2
      have hyM : y⁻¹ ∈ h.M3 := d.RM_le (inv_mem (hA₀R hy).1)
      have hk : y⁻¹ * m⁻¹ * y * m ∈ h.M3 := d.RM_le (mul_mem (mul_mem (mul_mem
        (inv_mem (hA₀R hy).1) (inv_mem hm.1)) (hA₀R hy).1) hm.1)
      have e : y⁻¹ * d.b⁻¹ = d.b⁻¹ * y⁻¹ :=
        mem_centralizer_iff.mp (inv_mem d.b_mem_centralizer_M3) y⁻¹ hyM
      have hkb := d.b_comm_of_mem_M3 hk
      calc y⁻¹ * m⁻¹ * y * m = d.b⁻¹ * (d.b * (y⁻¹ * m⁻¹ * y * m)) := by group
        _ = d.b⁻¹ * ((y⁻¹ * m⁻¹ * y * m) * d.b) := by rw [hkb]
        _ = (d.b⁻¹ * y⁻¹) * m⁻¹ * y * m * d.b := by group
        _ = (y⁻¹ * d.b⁻¹) * m⁻¹ * y * m * d.b := by rw [e]
        _ = y⁻¹ * (m * d.b)⁻¹ * y * (m * d.b) := by group
        _ = d.tau := h2
  rcases hcomm m hm with h3 | h3 <;> rw [hym] at h3
  · exact d.tau_ne_one h3
  · exact d.tau_ne_z hq hCF1 hCF2 hF.l0 h3

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
