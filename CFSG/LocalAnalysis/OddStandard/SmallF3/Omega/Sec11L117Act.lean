module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Q8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Qg

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

@[expose] def sec11Y (p : G) (Q : Subgroup G) : Subgroup G :=
  centralizer ({p} : Set G) ⊓ Q

theorem mem_sec11Y_iff {p y : G} {Q : Subgroup G} : y ∈ sec11Y p Q ↔ y ∈ Q ∧ y * p = p * y := by
  rw [sec11Y, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

private theorem sec11_zp_comm {z q u : G} (hqz : q * z = z * q) (hu : u ∈ zpowers z) :
    q * u = u * q := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact (show Commute q z from hqz).zpow_right k

private theorem sec11_zp_mul_comm {z a b : G} (ha : a ∈ zpowers z) (hb : b ∈ zpowers z) :
    a * b = b * a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← zpow_add, ← zpow_add, add_comm]

private theorem sec11_zp_le_Y {z p : G} {Q : Subgroup G} (hzQ : z ∈ Q)
    (hzp : z * p = p * z) : zpowers z ≤ sec11Y p Q :=
  Subgroup.zpowers_le_of_mem (by rw [mem_sec11Y_iff]; exact ⟨hzQ, hzp⟩)

private theorem sec11_mem_Y_self {p : G} {Q : Subgroup G} (hp : p ∈ Q) : p ∈ sec11Y p Q := by
  rw [mem_sec11Y_iff]; exact ⟨hp, rfl⟩

theorem Sec11Q8.card_Y [Finite G] {z : G} {Q : Subgroup G} (h : Sec11Q8 G z Q) {p : G}
    (hp : p ∈ Q) (hpz : p ∉ zpowers z) : Nat.card ↥(sec11Y p Q) = 4 := by
  have hZY : zpowers z ≤ sec11Y p Q := sec11_zp_le_Y h.z_mem (h.z_cent p hp).symm
  have hpY : p ∈ sec11Y p Q := sec11_mem_Y_self hp
  have hZYlt : zpowers z < sec11Y p Q :=
    lt_of_le_of_ne hZY (by intro heq; exact hpz (heq.symm ▸ hpY))
  have hYQ : sec11Y p Q ≤ Q := by rw [sec11Y]; exact inf_le_right
  have hYQne : sec11Y p Q ≠ Q := by
    intro heq
    apply hpz
    apply h.center p hp
    intro q hq
    have hqY : q ∈ sec11Y p Q := heq.symm ▸ hq
    exact (mem_sec11Y_iff.mp hqY).2.symm
  have hYQlt : sec11Y p Q < Q := lt_of_le_of_ne hYQ hYQne
  have hcardQ : Nat.card ↥Q = 8 := h.card
  have hcardZ : Nat.card ↥(zpowers z) = 2 := Sec11Q8.card_zpowers h
  have hlt : Nat.card ↥(sec11Y p Q) < Nat.card ↥Q := Subgroup.card_lt_of_lt hYQlt
  have hgt : Nat.card ↥(zpowers z) < Nat.card ↥(sec11Y p Q) := Subgroup.card_lt_of_lt hZYlt
  have hdvd : Nat.card ↥(sec11Y p Q) ∣ 8 := by
    rw [← h.card]; exact Subgroup.card_dvd_of_le hYQ
  have hge : 2 < Nat.card ↥(sec11Y p Q) := by rw [← hcardZ]; exact hgt
  have hlt8 : Nat.card ↥(sec11Y p Q) < 8 := by rw [← hcardQ]; exact hlt
  have hdvd' : Nat.card ↥(sec11Y p Q) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
    exact hdvd
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two).mp hdvd'
  have hk2 : k = 2 := by
    have h1 : 2 < 2 ^ k := by rw [← hk]; exact hge
    have h2 : 2 ^ k < 8 := by rw [← hk]; exact hlt8
    interval_cases k
    · norm_num at h1
    · norm_num at h1
    · rfl
    · norm_num at h2
  rw [hk, hk2]; norm_num

theorem Sec11Q8.inv_mul_mem_of_mem_Y [Finite G] {z : G} {Q : Subgroup G} (h : Sec11Q8 G z Q)
    {p : G} (hp : p ∈ Q) (hpz : p ∉ zpowers z) {c c' : G} (hc : c ∈ sec11Y p Q)
    (hc' : c' ∈ sec11Y p Q) (hcz : c ∉ zpowers z) (hc'z : c' ∉ zpowers z) :
    c⁻¹ * c' ∈ zpowers z := by
  have hZY : zpowers z ≤ sec11Y p Q := sec11_zp_le_Y h.z_mem (h.z_cent p hp).symm
  have hcardZ : Nat.card ↥(zpowers z) = 2 := Sec11Q8.card_zpowers h
  have hcardY : Nat.card ↥(sec11Y p Q) = 4 := Sec11Q8.card_Y h hp hpz
  have hrel : (zpowers z).relIndex (sec11Y p Q) = 2 := by
    have hh := Subgroup.relIndex_mul_card (H := zpowers z) (K := sec11Y p Q)
    rw [show zpowers z ⊓ sec11Y p Q = zpowers z from inf_eq_left.mpr hZY, hcardZ, hcardY] at hh
    omega
  have hindex : ((zpowers z).subgroupOf (sec11Y p Q)).index = 2 := by
    simpa [Subgroup.relIndex] using hrel
  have hiff : (⟨c, hc⟩ : sec11Y p Q)⁻¹ ∈ (zpowers z).subgroupOf (sec11Y p Q) ↔
      (⟨c', hc'⟩ : sec11Y p Q) ∈ (zpowers z).subgroupOf (sec11Y p Q) := by
    refine iff_of_false ?_ ?_
    · intro hmem
      apply hcz
      have hz1 : c⁻¹ ∈ zpowers z := Subgroup.mem_subgroupOf.mp hmem
      simpa using (zpowers z).inv_mem hz1
    · intro hmem
      exact hc'z (Subgroup.mem_subgroupOf.mp hmem)
  have hprod : (⟨c, hc⟩ : sec11Y p Q)⁻¹ * (⟨c', hc'⟩ : sec11Y p Q) ∈
      (zpowers z).subgroupOf (sec11Y p Q) :=
    (Subgroup.mul_mem_iff_of_index_two hindex).mpr hiff
  simpa using Subgroup.mem_subgroupOf.mp hprod

theorem Sec11Q8.comm_mem_zpowers_of_mem_Y [Finite G] {z : G} {Q : Subgroup G}
    (h : Sec11Q8 G z Q) {p : G} (hp : p ∈ Q) (hpz : p ∉ zpowers z) {u : G} (huz : u * z = z * u)
    (hup : u * p * u⁻¹ * p⁻¹ ∈ zpowers z) {y : G} (hy : y ∈ sec11Y p Q) :
    u * y * u⁻¹ * y⁻¹ ∈ zpowers z := by
  by_cases hyZ : y ∈ zpowers z
  · have huy : u * y = y * u := sec11_zp_comm huz hyZ
    have h1 : u * y * u⁻¹ * y⁻¹ = 1 := by rw [huy]; group
    rw [h1]; exact (zpowers z).one_mem
  · have hpY : p ∈ sec11Y p Q := sec11_mem_Y_self hp
    set w : G := p⁻¹ * y with hw
    have hwZ : w ∈ zpowers z := by
      rw [hw]
      exact Sec11Q8.inv_mul_mem_of_mem_Y h hp hpz hpY hy hpz hyZ
    have huw : u * w = w * u := sec11_zp_comm huz hwZ
    have hy_eq : y = p * w := by rw [hw]; group
    have h_eq : u * y * u⁻¹ * y⁻¹ = u * p * u⁻¹ * p⁻¹ := by
      calc u * y * u⁻¹ * y⁻¹
          = u * (p * w) * u⁻¹ * (p * w)⁻¹ := by rw [hy_eq]
        _ = u * p * (w * u⁻¹) * (p * w)⁻¹ := by group
        _ = u * p * (u⁻¹ * w) * (p * w)⁻¹ := by
              rw [show w * u⁻¹ = u⁻¹ * w from (show Commute u w from huw).symm.inv_right]
        _ = u * p * u⁻¹ * p⁻¹ := by rw [mul_inv_rev]; group
    rw [h_eq]; exact hup

theorem Sec11Q8.comm_mem_Y [Finite G] {z : G} {Q : Subgroup G} (h : Sec11Q8 G z Q) {p : G}
    (hp : p ∈ Q) (hpz : p ∉ zpowers z) {u : G} (hun : ∀ q ∈ Q, u * q * u⁻¹ ∈ Q)
    (huz : u * z = z * u) (hup : u * p * u⁻¹ * p⁻¹ ∈ zpowers z) {q : G} (hq : q ∈ Q) :
    u * q * u⁻¹ * q⁻¹ ∈ sec11Y p Q := by
  set q' : G := u * q * u⁻¹ with hq'
  set c : G := q' * q⁻¹ with hc
  set e : G := u * p * u⁻¹ * p⁻¹ with he
  set w : G := q * p * q⁻¹ * p⁻¹ with hw
  have hq'Q : q' ∈ Q := by rw [hq']; exact hun q hq
  have heZ : e ∈ zpowers z := by rw [he]; exact hup
  have hwZ : w ∈ zpowers z := by rw [hw]; exact (h.el q hq p hp).1
  have hue : u * e = e * u := sec11_zp_comm huz heZ
  have hqe : q * e = e * q := sec11_zp_comm (h.z_cent q hq) heZ
  have huw : u * w = w * u := sec11_zp_comm huz hwZ
  have hqw : q * w = w * q := sec11_zp_comm (h.z_cent q hq) hwZ
  have hqpe : q * p * q⁻¹ = w * p := by rw [hw]; group
  have hupe : u * p * u⁻¹ = e * p := by rw [he]; group
  have hupe_inv : u⁻¹ * p * u = e⁻¹ * p := by
    have h1 : p = e * (u⁻¹ * p * u) := by
      calc p = u⁻¹ * (u * p * u⁻¹) * u := by group
        _ = u⁻¹ * (e * p) * u := by rw [hupe]
        _ = e * (u⁻¹ * p * u) := by
              rw [show u⁻¹ * (e * p) * u = (u⁻¹ * e) * p * u by group,
                show u⁻¹ * e = e * u⁻¹ from (show Commute u e from hue).inv_left]
              group
    calc u⁻¹ * p * u = e⁻¹ * (e * (u⁻¹ * p * u)) := by group
      _ = e⁻¹ * p := by rw [show e * (u⁻¹ * p * u) = p from h1.symm]
  have hqe' : q * (e⁻¹ * p) = e⁻¹ * (q * p) := by
    rw [show q * (e⁻¹ * p) = (q * e⁻¹) * p by group,
      show q * e⁻¹ = e⁻¹ * q from (show Commute q e from hqe).inv_right]
    group
  have hue_inv : u * e⁻¹ = e⁻¹ * u := (show Commute u e from hue).inv_right
  have huwp : u * (w * p) = w * (u * p) := by
    rw [show u * (w * p) = (u * w) * p by group, huw]
    group
  have key : q' * p * q'⁻¹ = w * p := by
    calc q' * p * q'⁻¹
        = u * q * (u⁻¹ * p * u) * q⁻¹ * u⁻¹ := by rw [hq']; group
      _ = u * q * (e⁻¹ * p) * q⁻¹ * u⁻¹ := by rw [hupe_inv]
      _ = u * (q * (e⁻¹ * p)) * q⁻¹ * u⁻¹ := by group
      _ = u * (e⁻¹ * (q * p)) * q⁻¹ * u⁻¹ := by rw [hqe']
      _ = u * e⁻¹ * ((q * p) * q⁻¹) * u⁻¹ := by group
      _ = u * e⁻¹ * (w * p) * u⁻¹ := by rw [hqpe]
      _ = e⁻¹ * u * (w * p) * u⁻¹ := by rw [hue_inv]
      _ = e⁻¹ * (u * (w * p)) * u⁻¹ := by group
      _ = e⁻¹ * (w * (u * p)) * u⁻¹ := by rw [huwp]
      _ = e⁻¹ * w * ((u * p) * u⁻¹) := by group
      _ = e⁻¹ * w * (e * p) := by rw [hupe]
      _ = w * p := by
            have hwe : e⁻¹ * w * e = w := by
              rw [show e⁻¹ * w * e = e⁻¹ * (w * e) by group,
                show w * e = e * w from sec11_zp_mul_comm hwZ heZ]
              group
            rw [show e⁻¹ * w * (e * p) = (e⁻¹ * w * e) * p by group, hwe]
  have hqinvp : q⁻¹ * p * q = w⁻¹ * p := by
    have h1 : w * (q⁻¹ * p * q) = p := by
      calc w * (q⁻¹ * p * q)
          = w * q⁻¹ * p * q := by group
        _ = q⁻¹ * w * p * q := by
              rw [show w * q⁻¹ = q⁻¹ * w from
                (show Commute q w from hqw).symm.inv_right]
        _ = q⁻¹ * (w * p) * q := by group
        _ = q⁻¹ * (q * p * q⁻¹) * q := by rw [← hqpe]
        _ = p := by group
    calc q⁻¹ * p * q = w⁻¹ * (w * (q⁻¹ * p * q)) := by group
      _ = w⁻¹ * p := by rw [h1]
  have hcpc : c * p * c⁻¹ = p := by
    calc c * p * c⁻¹
        = q' * (q⁻¹ * p * q) * q'⁻¹ := by rw [hc]; group
      _ = q' * (w⁻¹ * p) * q'⁻¹ := by rw [hqinvp]
      _ = q' * w⁻¹ * p * q'⁻¹ := by group
      _ = w⁻¹ * (q' * p * q'⁻¹) := by
            rw [show q' * w⁻¹ = w⁻¹ * q' from
              sec11_zp_comm (h.z_cent q' hq'Q) ((zpowers z).inv_mem hwZ)]
            group
      _ = w⁻¹ * (w * p) := by rw [key]
      _ = p := by group
  have hcp : c * p = p * c := by
    have h2 := congrArg (fun x => x * c) hcpc
    rwa [show c * p * c⁻¹ * c = c * p by group] at h2
  have hQmem : c ∈ Q := by
    rw [hc]
    exact Q.mul_mem (by rw [hq']; exact hun q hq) (Q.inv_mem hq)
  rw [mem_sec11Y_iff]
  exact ⟨hQmem, hcp⟩

theorem Sec11Q8.comm_not_mem_of_not_mem_Y [Finite G] {z : G} {Q : Subgroup G}
    (h : Sec11Q8 G z Q) {p : G} (hp : p ∈ Q) (hpz : p ∉ zpowers z) {u : G}
    (huz : u * z = z * u) (hup : u * p * u⁻¹ * p⁻¹ ∈ zpowers z)
    (hu1 : ∃ q ∈ Q, u * q * u⁻¹ * q⁻¹ ∉ zpowers z) {q : G} (hq : q ∈ Q)
    (hqY : q ∉ sec11Y p Q) : u * q * u⁻¹ * q⁻¹ ∉ zpowers z := by
  set P : Subgroup G := sec11Qg z u Q with hP
  have hYP : sec11Y p Q ≤ P := by
    intro y hy
    show y ∈ sec11Qg z u Q
    rw [mem_sec11Qg_iff]
    refine ⟨(mem_sec11Y_iff.mp hy).1, ?_, ?_⟩
    · exact h.z_cent y (mem_sec11Y_iff.mp hy).1
    · exact Sec11Q8.comm_mem_zpowers_of_mem_Y h hp hpz huz hup hy
  have hPne : P ≠ Q := by
    obtain ⟨q0, hq0Q, hq0w⟩ := hu1
    intro heq
    have hq0P : q0 ∈ P := heq.symm ▸ hq0Q
    rw [mem_sec11Qg_iff] at hq0P
    exact hq0w hq0P.2.2
  have hcardP_dvd : Nat.card ↥P ∣ 8 := by
    rw [← h.card]
    exact Subgroup.card_dvd_of_le (show P ≤ Q from sec11Qg_le z u Q)
  have hcardY_le : 4 ≤ Nat.card ↥P := by
    rw [← Sec11Q8.card_Y h hp hpz]
    exact Subgroup.card_le_of_le hYP
  have hcardP_ne8 : Nat.card ↥P ≠ 8 := by
    intro h8
    have hcardle : Nat.card ↥Q ≤ Nat.card ↥P := by rw [h.card, h8]
    exact hPne (Subgroup.eq_of_le_of_card_ge (show P ≤ Q from sec11Qg_le z u Q) hcardle)
  have hcardP : Nat.card ↥P = 4 := by
    have hdvd' : Nat.card ↥P ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
      exact hcardP_dvd
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two).mp hdvd'
    have hk2 : k = 2 := by
      have h1 : 4 ≤ 2 ^ k := by rw [← hk]; exact hcardY_le
      have h2 : 2 ^ k ≠ 8 := by rw [← hk]; exact hcardP_ne8
      interval_cases k
      · norm_num at h1
      · norm_num at h1
      · rfl
      · norm_num at h2
    rw [hk, hk2]; norm_num
  have hPY : sec11Y p Q = P :=
    Subgroup.eq_of_le_of_card_ge hYP (by rw [hcardP, Sec11Q8.card_Y h hp hpz])
  have hqP : q ∉ P := by
    rw [← hPY]
    exact hqY
  intro hw
  apply hqP
  show q ∈ sec11Qg z u Q
  rw [mem_sec11Qg_iff]
  exact ⟨hq, h.z_cent q hq, hw⟩

theorem sec11_act_mul [Finite G] {z : G} {Q : Subgroup G} (h : Sec11Q8 G z Q) {u v p : G}
    (hp : p ∈ Q) (hpz : p ∉ zpowers z) (hun : ∀ q ∈ Q, u * q * u⁻¹ ∈ Q)
    (hvn : ∀ q ∈ Q, v * q * v⁻¹ ∈ Q) (huz : u * z = z * u) (hvz : v * z = z * v)
    (hup : u * p * u⁻¹ * p⁻¹ ∈ zpowers z) (hvp : v * p * v⁻¹ * p⁻¹ ∈ zpowers z)
    (hu1 : ∃ q ∈ Q, u * q * u⁻¹ * q⁻¹ ∉ zpowers z)
    (hv1 : ∃ q ∈ Q, v * q * v⁻¹ * q⁻¹ ∉ zpowers z) :
    ∀ q ∈ Q, (u * v) * q * (u * v)⁻¹ * q⁻¹ ∈ zpowers z := by
  intro q hq
  by_cases hqY : q ∈ sec11Y p Q
  · have hvqZ : v * q * v⁻¹ * q⁻¹ ∈ zpowers z :=
      Sec11Q8.comm_mem_zpowers_of_mem_Y h hp hpz hvz hvp hqY
    have huqZ : u * q * u⁻¹ * q⁻¹ ∈ zpowers z :=
      Sec11Q8.comm_mem_zpowers_of_mem_Y h hp hpz huz hup hqY
    have hid : (u * v) * q * (u * v)⁻¹ * q⁻¹ =
        u * (v * q * v⁻¹ * q⁻¹) * u⁻¹ * (u * q * u⁻¹ * q⁻¹) := by group
    rw [hid]
    have huvq : u * (v * q * v⁻¹ * q⁻¹) * u⁻¹ = v * q * v⁻¹ * q⁻¹ := by
      rw [show u * (v * q * v⁻¹ * q⁻¹) = (v * q * v⁻¹ * q⁻¹) * u from
        sec11_zp_comm huz hvqZ]
      group
    rw [huvq]
    exact (zpowers z).mul_mem hvqZ huqZ
  · set cv : G := v * q * v⁻¹ * q⁻¹ with hcv
    set cu : G := u * q * u⁻¹ * q⁻¹ with hcu
    have hcvY : cv ∈ sec11Y p Q := by
      rw [hcv]; exact Sec11Q8.comm_mem_Y h hp hpz hvn hvz hvp hq
    have hcuY : cu ∈ sec11Y p Q := by
      rw [hcu]; exact Sec11Q8.comm_mem_Y h hp hpz hun huz hup hq
    have hcvZ : cv ∉ zpowers z := by
      rw [hcv]; exact Sec11Q8.comm_not_mem_of_not_mem_Y h hp hpz hvz hvp hv1 hq hqY
    have hcuZ : cu ∉ zpowers z := by
      rw [hcu]; exact Sec11Q8.comm_not_mem_of_not_mem_Y h hp hpz huz hup hu1 hq hqY
    have hcvQ : cv ∈ Q := (mem_sec11Y_iff.mp hcvY).1
    have hcv2Z : cv * cv ∈ zpowers z := (h.el cv hcvQ cv hcvQ).2
    have hcvcuZ : cv⁻¹ * cu ∈ zpowers z :=
      Sec11Q8.inv_mul_mem_of_mem_Y h hp hpz hcvY hcuY hcvZ hcuZ
    have heZ : u * cv * u⁻¹ * cv⁻¹ ∈ zpowers z :=
      Sec11Q8.comm_mem_zpowers_of_mem_Y h hp hpz huz hup hcvY
    have hid : (u * v) * q * (u * v)⁻¹ * q⁻¹ = (u * cv * u⁻¹) * cu := by
      rw [hcv, hcu]; group
    rw [hid]
    have hcu_eq : cu = cv * (cv⁻¹ * cu) := by group
    have h_eq : (u * cv * u⁻¹) * cu =
        (u * cv * u⁻¹ * cv⁻¹) * (cv * cv * (cv⁻¹ * cu)) := by
      calc (u * cv * u⁻¹) * cu
          = (u * cv * u⁻¹ * cv⁻¹) * (cv * cu) := by group
        _ = (u * cv * u⁻¹ * cv⁻¹) * (cv * cv * (cv⁻¹ * cu)) := by rw [hcu_eq]; group
    rw [h_eq]
    exact (zpowers z).mul_mem heZ ((zpowers z).mul_mem hcv2Z hcvcuZ)

end CFSG.OddStandard.SmallF3.Omega
