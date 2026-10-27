module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117M
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec11_comm_of_mem_zpowers {z q u : G} (hqz : q * z = z * q)
    (hu : u ∈ zpowers z) : q * u = u * q := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact (show Commute q z from hqz).zpow_right k

@[expose] def sec11Qg (z g : G) (Q : Subgroup G) : Subgroup G where
  carrier := {q | q ∈ Q ∧ q * z = z * q ∧ g * q * g⁻¹ * q⁻¹ ∈ zpowers z}
  one_mem' := by
    refine ⟨Q.one_mem, by simp, ?_⟩
    simpa using (zpowers z).one_mem
  mul_mem' := by
    rintro q q' ⟨hq, hqz, hw⟩ ⟨hq', hqz', hw'⟩
    refine ⟨Q.mul_mem hq hq', ?_, ?_⟩
    · calc q * q' * z = q * (q' * z) := by rw [mul_assoc]
        _ = q * (z * q') := by rw [hqz']
        _ = (q * z) * q' := by rw [mul_assoc]
        _ = (z * q) * q' := by rw [hqz]
        _ = z * (q * q') := by rw [mul_assoc]
    · have hc : q * (g * q' * g⁻¹ * q'⁻¹) * q⁻¹ = g * q' * g⁻¹ * q'⁻¹ := by
        have h := sec11_comm_of_mem_zpowers hqz hw'
        calc q * (g * q' * g⁻¹ * q'⁻¹) * q⁻¹
            = (q * (g * q' * g⁻¹ * q'⁻¹)) * q⁻¹ := rfl
          _ = ((g * q' * g⁻¹ * q'⁻¹) * q) * q⁻¹ := by rw [h]
          _ = g * q' * g⁻¹ * q'⁻¹ := by group
      have hid : g * (q * q') * g⁻¹ * (q * q')⁻¹ =
          (g * q * g⁻¹ * q⁻¹) * (q * (g * q' * g⁻¹ * q'⁻¹) * q⁻¹) := by group
      rw [hid, hc]
      exact (zpowers z).mul_mem hw hw'
  inv_mem' := by
    rintro q ⟨hq, hqz, hw⟩
    refine ⟨Q.inv_mem hq, ?_, ?_⟩
    · exact (show Commute q z from hqz).inv_left
    · have hc : q⁻¹ * (g * q * g⁻¹ * q⁻¹)⁻¹ * q = (g * q * g⁻¹ * q⁻¹)⁻¹ := by
        have h := sec11_comm_of_mem_zpowers hqz ((zpowers z).inv_mem hw)
        calc q⁻¹ * (g * q * g⁻¹ * q⁻¹)⁻¹ * q
            = q⁻¹ * ((g * q * g⁻¹ * q⁻¹)⁻¹ * q) := by rw [mul_assoc]
          _ = q⁻¹ * (q * (g * q * g⁻¹ * q⁻¹)⁻¹) := by rw [← h]
          _ = (g * q * g⁻¹ * q⁻¹)⁻¹ := by group
      have hid : g * q⁻¹ * g⁻¹ * (q⁻¹)⁻¹ = q⁻¹ * (g * q * g⁻¹ * q⁻¹)⁻¹ * q := by group
      rw [hid, hc]
      exact (zpowers z).inv_mem hw

theorem mem_sec11Qg_iff {z g q : G} {Q : Subgroup G} :
    q ∈ sec11Qg z g Q ↔ q ∈ Q ∧ q * z = z * q ∧ g * q * g⁻¹ * q⁻¹ ∈ zpowers z :=
  Iff.rfl

theorem sec11Qg_le (z g : G) (Q : Subgroup G) : sec11Qg z g Q ≤ Q := fun _ hq => hq.1

theorem sec11_z_mem_Qg {z g : G} {Q : Subgroup G} (hzQ : z ∈ Q) (hgz : g * z = z * g) :
    z ∈ sec11Qg z g Q := by
  refine ⟨hzQ, rfl, ?_⟩
  rw [hgz]
  simpa using (zpowers z).one_mem

theorem sec11_mem_Qg_of_mul {z g : G} {C Q : Subgroup G}
    (hg : ∀ c ∈ C, g * c * g⁻¹ * c⁻¹ ∈ zpowers z) (hn : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hcomm : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c) {c q : G} (hc : c ∈ C) (hq : q ∈ Q)
    (hqz : q * z = z * q) (h : g * (c * q) * g⁻¹ * (c * q)⁻¹ ∈ zpowers z) :
    q ∈ sec11Qg z g Q := by
  refine ⟨hq, hqz, ?_⟩
  have hv : g * q * g⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hn q hq) (Q.inv_mem hq)
  have hcv : c * (g * q * g⁻¹ * q⁻¹) * c⁻¹ = g * q * g⁻¹ * q⁻¹ := by
    rw [hcomm c hc _ hv]
    group
  have hid : g * (c * q) * g⁻¹ * (c * q)⁻¹ =
      (g * c * g⁻¹ * c⁻¹) * (c * (g * q * g⁻¹ * q⁻¹) * c⁻¹) := by group
  rw [hid, hcv] at h
  have h2 := (zpowers z).mul_mem ((zpowers z).inv_mem (hg c hc)) h
  rwa [inv_mul_cancel_left] at h2

private theorem sec11_card_zpowers {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card ↥(zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1

private theorem sec11_card_le_four_of_ne [Finite G] {Q P : Subgroup G}
    (hPQ : P ≤ Q) (hcard : Nat.card Q = 8) (hne : P ≠ Q) : Nat.card P ≤ 4 := by
  have hdvd : Nat.card P ∣ 8 := by rw [← hcard]; exact Subgroup.card_dvd_of_le hPQ
  have hne8 : Nat.card P ≠ 8 := by
    intro hcon
    refine hne (Subgroup.eq_of_le_of_card_ge hPQ ?_)
    rw [hcard, hcon]
  have hdvd' : Nat.card P ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
    exact hdvd
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two).mp hdvd'
  have hk3ne : k ≠ 3 := by
    intro hk3eq
    apply hne8
    rw [hk, hk3eq]
    norm_num
  have hk2 : k ≤ 2 := by omega
  calc Nat.card P = 2 ^ k := hk
    _ ≤ 2 ^ 2 := by gcongr
    _ = 4 := by norm_num

private theorem sec11_Qg_inf_le_zpowers {z g : G} {Q1 Q2 : Subgroup G}
    (hinf : Q1 ⊓ Q2 = zpowers z) (hgz : g * z = z * g)
    (hs2 : ∀ q ∈ Q2, g * q * g⁻¹ ∈ Q1) :
    sec11Qg z g (Q1 ⊔ Q2) ⊓ Q2 ≤ zpowers z := by
  intro q hq
  rw [Subgroup.mem_inf] at hq
  obtain ⟨hqQ', hqQ2⟩ := hq
  rw [mem_sec11Qg_iff] at hqQ'
  obtain ⟨_, _, hw⟩ := hqQ'
  have hzpow_le_Q2 : zpowers z ≤ Q2 := (le_of_eq hinf.symm).trans inf_le_right
  have hconjQ2 : g * q * g⁻¹ ∈ Q2 := by
    have h : g * q * g⁻¹ = (g * q * g⁻¹ * q⁻¹) * q := by group
    rw [h]
    exact Q2.mul_mem (hzpow_le_Q2 hw) hqQ2
  have hconjQ1 : g * q * g⁻¹ ∈ Q1 := hs2 q hqQ2
  have hconj : g * q * g⁻¹ ∈ zpowers z := (le_of_eq hinf) ⟨hconjQ1, hconjQ2⟩
  rw [Subgroup.mem_zpowers_iff] at hconj ⊢
  obtain ⟨k, hk⟩ := hconj
  refine ⟨k, ?_⟩
  have hgc : Commute g z := hgz
  have h1 : g⁻¹ * z ^ k * g = z ^ k := by
    calc g⁻¹ * z ^ k * g
        = g⁻¹ * (z ^ k * g) := by group
      _ = g⁻¹ * (g * z ^ k) := by rw [← (hgc.zpow_right k).eq]
      _ = z ^ k := by group
  have hthis : q = g⁻¹ * (g * q * g⁻¹) * g := by group
  rw [← hk] at hthis
  rw [h1] at hthis
  exact hthis.symm

private theorem sec11_Qg_le_sup {z g : G} {Q1 Q2 : Subgroup G}
    (hcomm : ∀ p ∈ Q1, ∀ q ∈ Q2, p * q = q * p) (hinf : Q1 ⊓ Q2 = zpowers z)
    (hzc1 : ∀ q ∈ Q1, q * z = z * q) (hzc2 : ∀ q ∈ Q2, q * z = z * q)
    (hn1 : ∀ q ∈ Q1, g * q * g⁻¹ ∈ Q1) (hn2 : ∀ q ∈ Q2, g * q * g⁻¹ ∈ Q2) :
    sec11Qg z g (Q1 ⊔ Q2) ≤ sec11Qg z g Q1 ⊔ sec11Qg z g Q2 := by
  intro q hq
  rw [mem_sec11Qg_iff] at hq
  obtain ⟨hq_sup, _, hw⟩ := hq
  obtain ⟨q1, hq1, q2, hq2, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hq_sup
  set a1 : G := g * q1 * g⁻¹ * q1⁻¹ with ha1
  set a2 : G := g * q2 * g⁻¹ * q2⁻¹ with ha2
  have ha1Q1 : a1 ∈ Q1 := by
    rw [ha1]
    exact Q1.mul_mem (hn1 q1 hq1) (Q1.inv_mem hq1)
  have ha2Q2 : a2 ∈ Q2 := by
    rw [ha2]
    exact Q2.mul_mem (hn2 q2 hq2) (Q2.inv_mem hq2)
  have hcomm1a2 : q1 * a2 = a2 * q1 := hcomm q1 hq1 a2 ha2Q2
  have hid : g * (q1 * q2) * g⁻¹ * (q1 * q2)⁻¹ = a1 * a2 := by
    have h1 : g * q1 * g⁻¹ = a1 * q1 := by rw [ha1]; group
    have h2 : g * q2 * g⁻¹ = a2 * q2 := by rw [ha2]; group
    have hsplit : g * (q1 * q2) * g⁻¹ =
        (g * q1 * g⁻¹) * (g * q2 * g⁻¹) := by group
    rw [hsplit, h1, h2, mul_inv_rev]
    calc (a1 * q1) * (a2 * q2) * (q2⁻¹ * q1⁻¹)
        = a1 * (q1 * (a2 * q2)) * (q2⁻¹ * q1⁻¹) := by group
      _ = a1 * (q1 * a2) * (q2 * q2⁻¹) * q1⁻¹ := by group
      _ = a1 * (q1 * a2) * q1⁻¹ := by group
      _ = a1 * (a2 * q1) * q1⁻¹ := by rw [hcomm1a2]
      _ = a1 * a2 := by group
  have hprod : a1 * a2 ∈ zpowers z := by rw [← hid]; exact hw
  have hzpow_le_Q2 : zpowers z ≤ Q2 := (le_of_eq hinf.symm).trans inf_le_right
  have ha1Q2 : a1 ∈ Q2 := by
    have h : a1 = (a1 * a2) * a2⁻¹ := by group
    rw [h]
    exact Q2.mul_mem (hzpow_le_Q2 hprod) (Q2.inv_mem ha2Q2)
  have ha1z : a1 ∈ zpowers z := (le_of_eq hinf) ⟨ha1Q1, ha1Q2⟩
  have ha2z : a2 ∈ zpowers z := by
    have h : a2 = a1⁻¹ * (a1 * a2) := by group
    rw [h]
    exact (zpowers z).mul_mem ((zpowers z).inv_mem ha1z) hprod
  have hq1' : q1 ∈ sec11Qg z g Q1 := ⟨hq1, hzc1 q1 hq1, ha1z⟩
  have hq2' : q2 ∈ sec11Qg z g Q2 := ⟨hq2, hzc2 q2 hq2, ha2z⟩
  exact (sec11Qg z g Q1 ⊔ sec11Qg z g Q2).mul_mem
    (Subgroup.mem_sup_left hq1') (Subgroup.mem_sup_right hq2')

theorem sec11_card_Qg_swap [Finite G] {z g : G} {Q1 Q2 : Subgroup G} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hcomm : ∀ p ∈ Q1, ∀ q ∈ Q2, p * q = q * p) (hinf : Q1 ⊓ Q2 = zpowers z)
    (hQ1 : Nat.card Q1 = 8) (hgz : g * z = z * g) (hs2 : ∀ q ∈ Q2, g * q * g⁻¹ ∈ Q1) :
    Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) ≤ 8 := by
  have hle : sec11Qg z g (Q1 ⊔ Q2) ≤ Q1 ⊔ Q2 := sec11Qg_le z g (Q1 ⊔ Q2)
  have hcount := sec11_card_le_inf_mul (P1 := Q1) (Q2 := Q2)
    (Q' := sec11Qg z g (Q1 ⊔ Q2)) hcomm hinf hz2 hz1 hle
  have hzle : sec11Qg z g (Q1 ⊔ Q2) ⊓ Q2 ≤ zpowers z :=
    sec11_Qg_inf_le_zpowers hinf hgz hs2
  have hcard_inf : Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2) ⊓ Q2) ≤ 2 := by
    calc Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2) ⊓ Q2)
        ≤ Nat.card ↥(zpowers z) := Subgroup.card_le_of_le hzle
      _ = 2 := sec11_card_zpowers hz2 hz1
  have hbound : 2 * Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) ≤ 2 * 8 := by
    calc 2 * Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2))
        ≤ Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2) ⊓ Q2) * Nat.card Q1 := hcount
      _ ≤ 2 * 8 := Nat.mul_le_mul hcard_inf (le_of_eq hQ1)
  omega

theorem sec11_card_Qg_base [Finite G] {z g : G} {Q1 Q2 : Subgroup G} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hcomm : ∀ p ∈ Q1, ∀ q ∈ Q2, p * q = q * p) (hinf : Q1 ⊓ Q2 = zpowers z)
    (hQ1 : Nat.card Q1 = 8) (hQ2 : Nat.card Q2 = 8) (hzc1 : ∀ q ∈ Q1, q * z = z * q)
    (hzc2 : ∀ q ∈ Q2, q * z = z * q) (hgz : g * z = z * g)
    (hn1 : ∀ q ∈ Q1, g * q * g⁻¹ ∈ Q1) (hn2 : ∀ q ∈ Q2, g * q * g⁻¹ ∈ Q2)
    (ht1 : ∃ y ∈ Q1, g * y * g⁻¹ * y⁻¹ ∉ zpowers z)
    (ht2 : ∃ y ∈ Q2, g * y * g⁻¹ * y⁻¹ ∉ zpowers z) :
    Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) ≤ 8 := by
  have hz_inf : z ∈ Q1 ⊓ Q2 := (le_of_eq hinf.symm) (Subgroup.mem_zpowers z)
  have hzQ1 : z ∈ Q1 := (Subgroup.mem_inf.mp hz_inf).1
  have hzQ2 : z ∈ Q2 := (Subgroup.mem_inf.mp hz_inf).2
  have hP1le : Nat.card ↥(sec11Qg z g Q1) ≤ 4 := by
    rcases ht1 with ⟨y, hyQ1, hyw⟩
    refine sec11_card_le_four_of_ne (sec11Qg_le z g Q1) hQ1 ?_
    intro heq
    have hy : y ∈ sec11Qg z g Q1 := by rw [heq]; exact hyQ1
    rw [mem_sec11Qg_iff] at hy
    exact hyw hy.2.2
  have hP2le : Nat.card ↥(sec11Qg z g Q2) ≤ 4 := by
    rcases ht2 with ⟨y, hyQ2, hyw⟩
    refine sec11_card_le_four_of_ne (sec11Qg_le z g Q2) hQ2 ?_
    intro heq
    have hy : y ∈ sec11Qg z g Q2 := by rw [heq]; exact hyQ2
    rw [mem_sec11Qg_iff] at hy
    exact hyw hy.2.2
  have hinfP : sec11Qg z g Q1 ⊓ sec11Qg z g Q2 = zpowers z := by
    apply le_antisymm
    · calc sec11Qg z g Q1 ⊓ sec11Qg z g Q2 ≤ Q1 ⊓ Q2 :=
          inf_le_inf (sec11Qg_le z g Q1) (sec11Qg_le z g Q2)
        _ = zpowers z := hinf
    · exact le_inf (Subgroup.zpowers_le_of_mem (sec11_z_mem_Qg hzQ1 hgz))
        (Subgroup.zpowers_le_of_mem (sec11_z_mem_Qg hzQ2 hgz))
  have hcommP : ∀ p ∈ sec11Qg z g Q1, ∀ q ∈ sec11Qg z g Q2, p * q = q * p := by
    intro p hp q hq
    exact hcomm p (sec11Qg_le z g Q1 hp) q (sec11Qg_le z g Q2 hq)
  have hdecomp : sec11Qg z g (Q1 ⊔ Q2) ≤
      sec11Qg z g Q1 ⊔ sec11Qg z g Q2 :=
    sec11_Qg_le_sup hcomm hinf hzc1 hzc2 hn1 hn2
  have hcount := sec11_card_le_inf_mul (P1 := sec11Qg z g Q1)
    (Q2 := sec11Qg z g Q2) (Q' := sec11Qg z g (Q1 ⊔ Q2))
    hcommP hinfP hz2 hz1 hdecomp
  have hbound : 2 * Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2)) ≤ 16 := by
    calc 2 * Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2))
        ≤ Nat.card ↥(sec11Qg z g (Q1 ⊔ Q2) ⊓ sec11Qg z g Q2)
            * Nat.card ↥(sec11Qg z g Q1) := hcount
      _ ≤ Nat.card ↥(sec11Qg z g Q2) * Nat.card ↥(sec11Qg z g Q1) :=
          Nat.mul_le_mul_right _ (Subgroup.card_le_of_le inf_le_right)
      _ ≤ 4 * 4 := Nat.mul_le_mul hP2le hP1le
      _ = 16 := by norm_num
  omega

theorem sec11_card_Qg_pair [Finite G] {z g1 g2 : G} {Q1 Q2 : Subgroup G} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hcomm : ∀ p ∈ Q1, ∀ q ∈ Q2, p * q = q * p) (hinf : Q1 ⊓ Q2 = zpowers z)
    (hQ1 : Nat.card Q1 = 8) (hQ2 : Nat.card Q2 = 8) (hzc1 : ∀ q ∈ Q1, q * z = z * q)
    (hzc2 : ∀ q ∈ Q2, q * z = z * q) (hg1z : g1 * z = z * g1) (hg2z : g2 * z = z * g2)
    (hs2 : ∀ q ∈ Q2, g1 * q * g1⁻¹ ∈ Q1)
    (hn1 : ∀ q ∈ Q1, g2 * q * g2⁻¹ ∈ Q1) (hn2 : ∀ q ∈ Q2, g2 * q * g2⁻¹ ∈ Q2)
    (ht1 : ∃ y ∈ Q1, g2 * y * g2⁻¹ * y⁻¹ ∉ zpowers z) :
    Nat.card ↥(sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2)) ≤ 4 := by
  have hz_inf : z ∈ Q1 ⊓ Q2 := (le_of_eq hinf.symm) (Subgroup.mem_zpowers z)
  have hzQ1 : z ∈ Q1 := (Subgroup.mem_inf.mp hz_inf).1
  have hzQ2 : z ∈ Q2 := (Subgroup.mem_inf.mp hz_inf).2
  have hP1le : Nat.card ↥(sec11Qg z g2 Q1) ≤ 4 := by
    rcases ht1 with ⟨y, hyQ1, hyw⟩
    refine sec11_card_le_four_of_ne (sec11Qg_le z g2 Q1) hQ1 ?_
    intro heq
    have hy : y ∈ sec11Qg z g2 Q1 := by rw [heq]; exact hyQ1
    rw [mem_sec11Qg_iff] at hy
    exact hyw hy.2.2
  have hinfP : sec11Qg z g2 Q1 ⊓ sec11Qg z g2 Q2 = zpowers z := by
    apply le_antisymm
    · calc sec11Qg z g2 Q1 ⊓ sec11Qg z g2 Q2 ≤ Q1 ⊓ Q2 :=
          inf_le_inf (sec11Qg_le z g2 Q1) (sec11Qg_le z g2 Q2)
        _ = zpowers z := hinf
    · exact le_inf (Subgroup.zpowers_le_of_mem (sec11_z_mem_Qg hzQ1 hg2z))
        (Subgroup.zpowers_le_of_mem (sec11_z_mem_Qg hzQ2 hg2z))
  have hcommP : ∀ p ∈ sec11Qg z g2 Q1, ∀ q ∈ sec11Qg z g2 Q2, p * q = q * p := by
    intro p hp q hq
    exact hcomm p (sec11Qg_le z g2 Q1 hp) q (sec11Qg_le z g2 Q2 hq)
  have hdecompQ2 : sec11Qg z g2 (Q1 ⊔ Q2) ≤
      sec11Qg z g2 Q1 ⊔ sec11Qg z g2 Q2 :=
    sec11_Qg_le_sup hcomm hinf hzc1 hzc2 hn1 hn2
  have hle : sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2) ≤
      sec11Qg z g2 Q1 ⊔ sec11Qg z g2 Q2 := inf_le_right.trans hdecompQ2
  have hcount := sec11_card_le_inf_mul (P1 := sec11Qg z g2 Q1)
    (Q2 := sec11Qg z g2 Q2)
    (Q' := sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2))
    hcommP hinfP hz2 hz1 hle
  have hzle : (sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2))
      ⊓ sec11Qg z g2 Q2 ≤ zpowers z := by
    have hsub : (sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2))
        ⊓ sec11Qg z g2 Q2 ≤ sec11Qg z g1 (Q1 ⊔ Q2) ⊓ Q2 :=
      le_inf (le_trans inf_le_left inf_le_left)
        (le_trans inf_le_right (sec11Qg_le z g2 Q2))
    exact hsub.trans (sec11_Qg_inf_le_zpowers hinf hg1z hs2)
  have hcard_inf : Nat.card ↥((sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2))
      ⊓ sec11Qg z g2 Q2) ≤ 2 := by
    calc Nat.card ↥((sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2))
          ⊓ sec11Qg z g2 Q2)
        ≤ Nat.card ↥(zpowers z) := Subgroup.card_le_of_le hzle
      _ = 2 := sec11_card_zpowers hz2 hz1
  have hbound : 2 * Nat.card ↥(sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2))
      ≤ 2 * 4 := by
    calc 2 * Nat.card ↥(sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2))
        ≤ Nat.card ↥((sec11Qg z g1 (Q1 ⊔ Q2) ⊓ sec11Qg z g2 (Q1 ⊔ Q2))
            ⊓ sec11Qg z g2 Q2) * Nat.card ↥(sec11Qg z g2 Q1) := hcount
      _ ≤ 2 * 4 := Nat.mul_le_mul hcard_inf hP1le
  omega

end CFSG.OddStandard.SmallF3.Omega
