module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115cB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115cA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11c_KD_le_K0 {t z : G} {E : Subgroup G} (h : zpowers t ⊔ zpowers z ≤ E) :
    secKD E ≤ secK0 t z := by
  unfold secKD secK0
  rw [← sec11c_cent_pair]
  exact sec11c_oTwoRes_mono (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 h))

theorem sec11c_KD_pair (t z : G) : secKD (zpowers t ⊔ zpowers z) = secK0 t z := by
  unfold secKD secK0
  rw [sec11c_cent_pair]

theorem sec11c_conj_cent {E : Subgroup G} {r : G} (hr : r ∈ normalizer (E : Set G)) {x : G}
    (hx : x ∈ centralizer (E : Set G)) : r * x * r⁻¹ ∈ centralizer (E : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro e he
  have he' : r⁻¹ * e * r ∈ E := by
    refine (Subgroup.mem_normalizer_iff.mp hr (r⁻¹ * e * r)).mpr ?_
    have h : r * (r⁻¹ * e * r) * r⁻¹ = e := by group
    rw [h]
    exact he
  have hxe := hx _ he'
  calc e * (r * x * r⁻¹) = r * ((r⁻¹ * e * r) * x) * r⁻¹ := by group
    _ = r * (x * (r⁻¹ * e * r)) * r⁻¹ := by rw [hxe]
    _ = (r * x * r⁻¹) * e := by group

theorem sec11c_normalizer_KD {E : Subgroup G} {r : G} (hr : r ∈ normalizer (E : Set G)) :
    r ∈ normalizer (secKD E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => sec11c_conj_mem_oTwoRes (fun x hx => sec11c_conj_cent hr hx) hh
  · intro hh
    have h1 := sec11c_conj_mem_oTwoRes (fun x hx => sec11c_conj_cent (Subgroup.inv_mem _ hr) hx) hh
    have h2 : r⁻¹ * (r * h * r⁻¹) * r⁻¹⁻¹ = h := by group
    rw [h2] at h1
    exact h1

namespace Sec11cSplit

variable {t z : G} {K1 K2 : Subgroup G}

theorem comm_mod [Finite G] (hS : Sec11cSplit t z K1 K2) {E : Subgroup G}
    (hE : secKD E ≤ secK0 t z) {d : G} (hdQ : ∀ q ∈ secQ K1 K2, d * q = q * d)
    (hdK : ∀ x ∈ secKD E, d * x * d⁻¹ ∈ secKD E) :
    ∀ g ∈ secKD E, g⁻¹ * (d * g * d⁻¹) ∈ oddCoreIn (secK0 t z) := by
  intro g hg
  have hg' : g ∈ Subgroup.closure {x : G | x ∈ centralizer (E : Set G) ∧ Odd (orderOf x)} := hg
  clear hg
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    have hxK : x ∈ secKD E := sec11c_mem_oTwoRes hx.1 hx.2
    have hxK0 : x ∈ secK0 t z := hE hxK
    have hk'K0 : d * x * d⁻¹ ∈ secK0 t z := hE (hdK x hxK)
    refine hS.quot_mem hxK0 hk'K0 hx.2 (by rw [sec11c_orderOf_conj]; exact hx.2) ?_
    intro q hq
    have hp : x * q * x⁻¹ ∈ secQ K1 K2 := hS.conj_K0_Q hxK0 hq
    have h1 : d * q = q * d := hdQ q hq
    have h2 : d * (x * q * x⁻¹) = (x * q * x⁻¹) * d := hdQ _ hp
    have hq' : d⁻¹ * q * d = q := by
      calc d⁻¹ * q * d = d⁻¹ * (q * d) := by group
        _ = d⁻¹ * (d * q) := by rw [h1]
        _ = q := by group
    have hp' : d * (x * q * x⁻¹) * d⁻¹ = x * q * x⁻¹ := by rw [h2]; group
    have hmain : d * x * d⁻¹ * q * (d * x * d⁻¹)⁻¹ = x * q * x⁻¹ := by
      calc d * x * d⁻¹ * q * (d * x * d⁻¹)⁻¹ = d * x * (d⁻¹ * q * d) * x⁻¹ * d⁻¹ := by group
        _ = d * x * q * x⁻¹ * d⁻¹ := by rw [hq']
        _ = d * (x * q * x⁻¹) * d⁻¹ := by group
        _ = x * q * x⁻¹ := hp'
    calc x⁻¹ * (d * x * d⁻¹) * q
        = x⁻¹ * (d * x * d⁻¹ * q * (d * x * d⁻¹)⁻¹) * (d * x * d⁻¹) := by group
      _ = x⁻¹ * (x * q * x⁻¹) * (d * x * d⁻¹) := by rw [hmain]
      _ = q * (x⁻¹ * (d * x * d⁻¹)) := by group
  | one => simpa using Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    have hyK0 : y ∈ secK0 t z := hE hy
    have e : (x * y)⁻¹ * (d * (x * y) * d⁻¹) =
        (y⁻¹ * (x⁻¹ * (d * x * d⁻¹)) * y) * (y⁻¹ * (d * y * d⁻¹)) := by group
    rw [e]
    refine Subgroup.mul_mem _ ?_ ihy
    have h := sec11_conj_mem_oddCoreIn (Subgroup.le_normalizer (Subgroup.inv_mem _ hyK0)) ihx
    simpa only [inv_inv] using h
  | inv x hx ihx =>
    have hxK0 : x ∈ secK0 t z := hE hx
    have e : x⁻¹⁻¹ * (d * x⁻¹ * d⁻¹) = x * (x⁻¹ * (d * x * d⁻¹))⁻¹ * x⁻¹ := by group
    rw [e]
    exact sec11_conj_mem_oddCoreIn (Subgroup.le_normalizer hxK0) (Subgroup.inv_mem _ ihx)

theorem inf_le_oddCore [Finite G] (hS : Sec11cSplit t z K1 K2) {E : Subgroup G}
    (hE : secKD E ≤ secK0 t z) :
    secKD E ⊓ oddCoreIn (secK0 t z) ≤ oddCoreIn (secKD E) := by
  have hN : ((secKD E ⊓ oddCoreIn (secK0 t z)).subgroupOf (secKD E)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro a b ha hb
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hb ha.1) (Subgroup.inv_mem _ hb),
      sec11_conj_mem_oddCoreIn (Subgroup.le_normalizer (hE hb)) ha.2⟩
  exact le_oddCoreIn_of_normal inf_le_left hN
    (Odd.of_dvd_nat (odd_card_oddCoreIn (secK0 t z)) (Subgroup.card_dvd_of_le inf_le_right))

theorem odd_mul_z [Finite G] (hS : Sec11cSplit t z K1 K2) {n e : G}
    (hn : n ∈ oddCoreIn (secK0 t z)) (he : e ∈ zpowers z) (ho : Odd (orderOf (n * e))) :
    e = 1 := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 he
  have hnK0 : n ∈ secK0 t z := (oddCoreIn_normal _).1 hn
  have hnz : Commute n z := hS.z_comm n hnK0
  have hcomm : Commute n e := by
    rw [← hj]
    exact hnz.zpow_right j
  have he2 : e ^ 2 = 1 := by
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hS.z_sq
    simp [hz2]
  have hno : Odd (orderOf n) := odd_orderOf_of_mem_oddCoreIn hn
  have hB : Odd (orderOf (n * e) * orderOf n) := ho.mul hno
  have h1 : (n * e) ^ (orderOf (n * e) * orderOf n) = 1 := by
    rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have h2 : n ^ (orderOf (n * e) * orderOf n) = 1 := by
    rw [mul_comm (orderOf (n * e)) (orderOf n), pow_mul, pow_orderOf_eq_one, one_pow]
  rw [hcomm.mul_pow, h2, one_mul] at h1
  exact sec11c_two_odd he2 hB h1

theorem oddCore_le [Finite G] (hS : Sec11cSplit t z K1 K2) {E : Subgroup G}
    (hE : secKD E ≤ secK0 t z) (hEQ : ∀ e ∈ E, ∀ q ∈ secQ K1 K2, e * q = q * e) :
    oddCoreIn (secKD E) ≤ oddCoreIn (secK0 t z) := by
  intro x hx
  have hxK : x ∈ secKD E := (oddCoreIn_normal _).1 hx
  have hxK0 : x ∈ secK0 t z := hE hxK
  have hxo : Odd (orderOf x) := odd_orderOf_of_mem_oddCoreIn hx
  have hcomm : ∀ q ∈ secQ K1 K2, x * q = q * x := by
    intro q hq
    have hqC : q ∈ centralizer (E : Set G) :=
      Subgroup.mem_centralizer_iff.2 (fun e he => hEQ e he q hq)
    have hqN : q ∈ normalizer (secKD E : Set G) :=
      sec11c_normalizer_KD (Subgroup.centralizer_le_normalizer (E : Set G) hqC)
    have hxi : x⁻¹ ∈ oddCoreIn (secKD E) := Subgroup.inv_mem _ hx
    have h1 : q * x⁻¹ * q⁻¹ ∈ oddCoreIn (secKD E) := sec11_conj_mem_oddCoreIn hqN hxi
    have hcO : x * (q * x⁻¹ * q⁻¹) ∈ oddCoreIn (secKD E) := Subgroup.mul_mem _ hx h1
    have hcQ : x * q * x⁻¹ * q⁻¹ ∈ secQ K1 K2 :=
      Subgroup.mul_mem _ (hS.conj_K0_Q hxK0 hq) (Subgroup.inv_mem _ hq)
    have hc1 : x * q * x⁻¹ * q⁻¹ = 1 := by
      have e : x * q * x⁻¹ * q⁻¹ = x * (q * x⁻¹ * q⁻¹) := by group
      exact sec11_Q_inf_oddCore hcQ (e ▸ hcO)
    calc x * q = x * q * x⁻¹ * q⁻¹ * q * x := by group
      _ = q * x := by rw [hc1]; group
  obtain ⟨n, hn, e, he, hxe⟩ := hS.cent x hxK0 hcomm
  have he1 : e = 1 := hS.odd_mul_z hn he (hxe ▸ hxo)
  rw [hxe, he1, mul_one]
  exact hn

theorem odd_mul [Finite G] (hS : Sec11cSplit t z K1 K2) {g m : G} (hg : g ∈ secK0 t z)
    (hm : m ∈ oddCoreIn (secK0 t z)) (hgo : Odd (orderOf g)) : Odd (orderOf (g * m)) := by
  obtain ⟨n, hn, κ, hκ, rfl⟩ := hS.split.dec g hg
  have hκb : κ ^ orderOf (n * κ) = 1 := hS.proj_pow hn hκ (pow_orderOf_eq_one _)
  have hnm : n * m ∈ oddCoreIn (secK0 t z) := Subgroup.mul_mem _ hn hm
  have hcomm : Commute (n * m) κ := hS.split.comm _ hnm κ hκ
  have e : n * κ * m = (n * m) * κ := by
    have h1 : κ * m = m * κ := hS.comm' hm hκ
    calc n * κ * m = n * (κ * m) := by group
      _ = n * (m * κ) := by rw [h1]
      _ = (n * m) * κ := by group
  rw [e]
  set b := orderOf (n * κ) with hb
  have hu : ((n * m) * κ) ^ b = (n * m) ^ b := by rw [hcomm.mul_pow, hκb, mul_one]
  have huN : (n * m) ^ b ∈ oddCoreIn (secK0 t z) := Subgroup.pow_mem _ hnm b
  have huo : Odd (orderOf ((n * m) ^ b)) := odd_orderOf_of_mem_oddCoreIn huN
  have h1 : ((n * m) * κ) ^ (b * orderOf ((n * m) ^ b)) = 1 := by
    rw [pow_mul, hu, pow_orderOf_eq_one]
  exact Odd.of_dvd_nat (hgo.mul huo) (orderOf_dvd_of_pow_eq_one h1)

end Sec11cSplit

end CFSG.OddStandard.SmallF3.Omega
