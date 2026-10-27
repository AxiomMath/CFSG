module

public import CFSG.GH74.GLS.IVK.Proofs2.Sp48O2
public import Mathlib.GroupTheory.Sylow

public section

open Matrix

namespace CFSG.ClassicalGroups.Orthogonal.PlaneSylow

open CFSG.GH74.GLS.IVK.Proofs2.Sp48
open CFSG.GH74.GLS.IVK.Proofs2.Sp48.O2Plane

variable {K : Type} [Field K]

theorem natCard_O2 [Finite K] (h2 : (2 : K) ≠ 0) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card K : ℤ) ≡ ε [ZMOD 4]) :
    (Nat.card ↥(O2 K) : ℤ) = 2 * (Nat.card K - ε) := by
  have hSO2cardZ : (Nat.card ↥(SO2 K) : ℤ) = (Nat.card K : ℤ) - ε :=
    card_SO2 h2 ε hε hq
  have hIndex : ((SO2 K).subgroupOf (O2 K)).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨sig K, sig_mem_O2⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact fun h => sig_not_mem_Rx h2 (SO2_le_Rx h)
    · intro b
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      change ((b : GL (Fin 2) K) * sig K ∈ SO2 K) ∨ ((b : GL (Fin 2) K) ∈ SO2 K)
      rcases O2_cases b.2 with hb | hb
      · exact Or.inr hb
      · refine Or.inl ?_
        set r : GL (Fin 2) K := sig K * (b : GL (Fin 2) K) with hr
        have hb' : r ∈ SO2 K := by rw [hr]; exact hb
        have hconj : sig K * r * sig K = r⁻¹ := by
          have h := sig_mul_mul_sig_mul_SO2 (r := r) hb'
          exact eq_inv_of_mul_eq_one_left h
        have hx : (b : GL (Fin 2) K) * sig K = sig K * r * sig K := by
          rw [hr]
          calc (b : GL (Fin 2) K) * sig K
              = (sig K * sig K) * (b : GL (Fin 2) K) * sig K := by
                rw [sig_mul_self, one_mul]
            _ = sig K * (sig K * (b : GL (Fin 2) K)) * sig K := by
                simp only [mul_assoc]
        rw [hx, hconj]
        exact (SO2 K).inv_mem hb'
  have hHcard : Nat.card ↥((SO2 K).subgroupOf (O2 K)) = Nat.card ↥(SO2 K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe SO2_le_O2).toEquiv
  have hmul : Nat.card ↥((SO2 K).subgroupOf (O2 K)) *
      ((SO2 K).subgroupOf (O2 K)).index = Nat.card ↥(O2 K) :=
    Subgroup.card_mul_index (G := ↥(O2 K)) (H := (SO2 K).subgroupOf (O2 K))
  rw [hHcard, hIndex] at hmul
  have hcast : (Nat.card ↥(O2 K) : ℤ) = 2 * (Nat.card ↥(SO2 K) : ℤ) := by
    rw [← hmul]
    push_cast
    ring
  rw [hcast, hSO2cardZ]

theorem natCard_O2_nat [Finite K] (h2 : (2 : K) ≠ 0) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card K : ℤ) ≡ ε [ZMOD 4]) (m : ℕ) (hm : (m : ℤ) = Nat.card K - ε) :
    Nat.card ↥(O2 K) = 2 * m := by
  have hz := natCard_O2 (K := K) h2 ε hε hq
  have h2m : ((2 * m : ℕ) : ℤ) = 2 * (Nat.card K - ε) := by
    push_cast
    rw [hm]
  have hcast : (Nat.card ↥(O2 K) : ℤ) = ((2 * m : ℕ) : ℤ) := by
    rw [hz, ← h2m]
  exact_mod_cast hcast

def planeSylow (c : GL (Fin 2) K) : Subgroup (GL (Fin 2) K) :=
  Subgroup.closure {c, sig K}

theorem planeSylow_le_O2 {c : GL (Fin 2) K} (hc : c ∈ SO2 K) : planeSylow c ≤ O2 K := by
  change Subgroup.closure ({c, sig K} : Set (GL (Fin 2) K)) ≤ O2 K
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact SO2_le_O2 hc
  · exact sig_mem_O2

theorem conj_sig_zpow {c : GL (Fin 2) K} (hc : c ∈ SO2 K) (i : ℤ) :
    sig K * c ^ i * sig K = c ^ (-i) := by
  have hsig : (sig K)⁻¹ = sig K := inv_eq_of_mul_eq_one_right (sig_mul_self (F := K))
  have hconj : sig K * c * (sig K)⁻¹ = c⁻¹ := by
    rw [hsig]
    exact eq_inv_of_mul_eq_one_left (sig_mul_mul_sig_mul_SO2 (r := c) hc)
  calc sig K * c ^ i * sig K
      = sig K * c ^ i * (sig K)⁻¹ := by rw [hsig]
    _ = (sig K * c * (sig K)⁻¹) ^ i := (conj_zpow (a := sig K) (b := c) (i := i)).symm
    _ = (c⁻¹) ^ i := by rw [hconj]
    _ = (c ^ i)⁻¹ := inv_zpow c i
    _ = c ^ (-i) := (zpow_neg c i).symm

theorem mul_sig_zpow {c : GL (Fin 2) K} (hc : c ∈ SO2 K) (i : ℤ) :
    c ^ i * sig K = sig K * c ^ (-i) := by
  have h := conj_sig_zpow hc i
  calc c ^ i * sig K
      = (sig K * sig K) * c ^ i * sig K := by rw [sig_mul_self (F := K), one_mul]
    _ = sig K * (sig K * c ^ i * sig K) := by simp only [mul_assoc]
    _ = sig K * c ^ (-i) := by rw [h]

theorem sig_mul_zpow_mul_self {c : GL (Fin 2) K} (hc : c ∈ SO2 K) (i : ℤ) :
    (sig K * c ^ i) * (sig K * c ^ i) = 1 := by
  calc (sig K * c ^ i) * (sig K * c ^ i)
      = (sig K * c ^ i * sig K) * c ^ i := by simp only [mul_assoc]
    _ = c ^ (-i) * c ^ i := by rw [conj_sig_zpow hc i]
    _ = 1 := by rw [← zpow_add, neg_add_cancel, zpow_zero]

theorem mem_planeSylow_iff {c : GL (Fin 2) K} (hc : c ∈ SO2 K) (x : GL (Fin 2) K) :
    x ∈ planeSylow c ↔ ∃ i : ℤ, x = c ^ i ∨ x = sig K * c ^ i := by
  change x ∈ Subgroup.closure ({c, sig K} : Set (GL (Fin 2) K)) ↔
    ∃ i : ℤ, x = c ^ i ∨ x = sig K * c ^ i
  constructor
  · intro hx
    refine Subgroup.closure_induction
      (p := fun x _ => ∃ i : ℤ, x = c ^ i ∨ x = sig K * c ^ i) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl | rfl
      · exact ⟨1, Or.inl (by rw [zpow_one])⟩
      · exact ⟨0, Or.inr (by rw [zpow_zero, mul_one])⟩
    · exact ⟨0, Or.inl (zpow_zero c)⟩
    · rintro y z - - ⟨i, hi | hi⟩ ⟨j, hj | hj⟩
      · exact ⟨i + j, Or.inl (by rw [hi, hj, zpow_add])⟩
      · refine ⟨j - i, Or.inr ?_⟩
        rw [hi, hj]
        calc c ^ i * (sig K * c ^ j)
            = (c ^ i * sig K) * c ^ j := (mul_assoc _ _ _).symm
          _ = (sig K * c ^ (-i)) * c ^ j := by rw [mul_sig_zpow hc i]
          _ = sig K * (c ^ (-i) * c ^ j) := mul_assoc _ _ _
          _ = sig K * c ^ (-i + j) := by rw [← zpow_add]
          _ = sig K * c ^ (j - i) := by
              congr 1
              ring
      · exact ⟨i + j, Or.inr (by rw [hi, hj, mul_assoc, zpow_add])⟩
      · refine ⟨j - i, Or.inl ?_⟩
        rw [hi, hj]
        calc (sig K * c ^ i) * (sig K * c ^ j)
            = ((sig K * c ^ i) * sig K) * c ^ j := (mul_assoc _ _ _).symm
          _ = c ^ (-i) * c ^ j := by rw [conj_sig_zpow hc i]
          _ = c ^ (-i + j) := by rw [← zpow_add]
          _ = c ^ (j - i) := by
              congr 1
              ring
    · rintro y - ⟨i, hi | hi⟩
      · exact ⟨-i, Or.inl (by rw [hi, ← zpow_neg])⟩
      · exact ⟨i, Or.inr (by rw [hi, inv_eq_of_mul_eq_one_right (sig_mul_zpow_mul_self hc i)])⟩
  · rintro ⟨i, rfl | rfl⟩
    · exact (Subgroup.closure ({c, sig K} : Set (GL (Fin 2) K))).zpow_mem
        (Subgroup.subset_closure (by simp)) i
    · exact (Subgroup.closure ({c, sig K} : Set (GL (Fin 2) K))).mul_mem
        (Subgroup.subset_closure (by simp))
        ((Subgroup.closure ({c, sig K} : Set (GL (Fin 2) K))).zpow_mem
          (Subgroup.subset_closure (by simp)) i)

theorem neg_one_mem_planeSylow {c : GL (Fin 2) K} {r : ℕ}
    (hneg : c ^ (2 ^ (r - 1)) = -1) : (-1 : GL (Fin 2) K) ∈ planeSylow c := by
  rw [← hneg]
  exact (planeSylow c).pow_mem (Subgroup.subset_closure (by simp)) (2 ^ (r - 1))

theorem sig_not_mem_zpowers {c : GL (Fin 2) K} (h2 : (2 : K) ≠ 0) (hc : c ∈ SO2 K) :
    sig K ∉ Subgroup.zpowers c := by
  intro h
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
  apply sig_not_mem_Rx h2
  have hmem : c ^ i ∈ Rx K := (Rx K).zpow_mem (SO2_le_Rx hc) i
  rwa [hi] at hmem

theorem card_planeSylow {c : GL (Fin 2) K} {r : ℕ} (h2 : (2 : K) ≠ 0)
    (hc : c ∈ SO2 K) (hord : orderOf c = 2 ^ r) :
    Nat.card ↥(planeSylow c) = 2 ^ (r + 1) := by
  let cD : planeSylow c := ⟨c, Subgroup.subset_closure (by simp)⟩
  let sigD : planeSylow c := ⟨sig K, Subgroup.subset_closure (by simp)⟩
  have hHcard : Nat.card ↥(Subgroup.zpowers cD) = 2 ^ r := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe cD]
    exact hord
  have hsig_not : sigD ∉ Subgroup.zpowers cD := by
    intro hmem
    have h : sig K ∈ Subgroup.zpowers c := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have := congrArg Subtype.val hn
      simpa [cD] using this
    exact sig_not_mem_zpowers h2 hc h
  have hindex : (Subgroup.zpowers cD).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨sigD, hsig_not, ?_⟩
    intro b
    obtain ⟨i, hi | hi⟩ := (mem_planeSylow_iff hc (b : GL (Fin 2) K)).mp b.2
    · right
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨i, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hi.symm
    · left
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨-i, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_zpow, Subgroup.coe_mul]
      change c ^ (-i) = (b : GL (Fin 2) K) * sig K
      rw [hi]
      exact (conj_sig_zpow hc i).symm
  have hmul : Nat.card ↥(Subgroup.zpowers cD) * (Subgroup.zpowers cD).index =
      Nat.card ↥(planeSylow c) :=
    Subgroup.card_mul_index (G := planeSylow c) (H := Subgroup.zpowers cD)
  rw [hHcard, hindex] at hmul
  rw [← hmul, pow_succ]

theorem eq_one_or_neg_one_of_sq_eq_one {c : GL (Fin 2) K} {r : ℕ}
    (hc : c ∈ SO2 K) (hord : orderOf c = 2 ^ r) (hr : 1 ≤ r)
    (hneg : c ^ (2 ^ (r - 1)) = -1)
    {x : GL (Fin 2) K} (hx : x ∈ Subgroup.zpowers c) (hx2 : x ^ 2 = 1) :
    x = 1 ∨ x = -1 := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hci : c ^ ((2 : ℤ) * i) = 1 := by
    rw [mul_comm (2 : ℤ) i, zpow_mul, hi]
    simpa using hx2
  have hdvd : (orderOf c : ℤ) ∣ (2 : ℤ) * i :=
    orderOf_dvd_iff_zpow_eq_one.mpr hci
  have hdvd' : ((2 : ℤ) ^ r) ∣ (2 : ℤ) * i := by
    have h := hdvd
    rw [hord] at h
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have h2r : ((2 : ℤ) ^ r) = 2 * (2 : ℤ) ^ (r - 1) := by
    rw [← pow_sub_one_mul (n := r) (a := (2 : ℤ)) (by omega), mul_comm]
  have hdvd'' : (2 : ℤ) ^ (r - 1) ∣ i := by
    refine (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp ?_
    rwa [h2r] at hdvd'
  obtain ⟨k, hk⟩ := hdvd''
  have hx' : x = (-1 : GL (Fin 2) K) ^ k := by
    rw [← hi, hk, zpow_mul,
      show (2 : ℤ) ^ (r - 1) = ((2 ^ (r - 1) : ℕ) : ℤ) from by push_cast; ring,
      zpow_natCast, hneg]
  rcases Int.even_or_odd k with hk' | hk'
  · exact Or.inl (hx'.trans hk'.neg_one_zpow)
  · exact Or.inr (hx'.trans hk'.neg_one_zpow)

theorem mem_center_planeSylow_iff {c : GL (Fin 2) K} {r : ℕ}
    (hc : c ∈ SO2 K) (hord : orderOf c = 2 ^ r) (hr : 2 ≤ r)
    (hneg : c ^ (2 ^ (r - 1)) = -1) (x : planeSylow c) :
    x ∈ Subgroup.center (planeSylow c) ↔
      (x : GL (Fin 2) K) = 1 ∨ (x : GL (Fin 2) K) = -1 := by
  let cD : planeSylow c := ⟨c, Subgroup.subset_closure (by simp)⟩
  let sigD : planeSylow c := ⟨sig K, Subgroup.subset_closure (by simp)⟩
  constructor
  · intro hx
    obtain ⟨i, hi | hi⟩ := (mem_planeSylow_iff hc (x : GL (Fin 2) K)).mp x.2
    · have hcomm : sig K * c ^ i = c ^ i * sig K := by
        have h := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hx) sigD)
        rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
        simpa [sigD, hi] using h
      have hci : c ^ i = c ^ (-i) := by
        have h : sig K * c ^ i = sig K * c ^ (-i) := by
          rw [hcomm, mul_sig_zpow hc i]
        exact mul_left_cancel h
      have hsq : (c ^ i) ^ 2 = 1 := by
        have h : c ^ i * c ^ i = 1 := by
          nth_rewrite 2 [hci]
          rw [← zpow_add, show i + -i = 0 by ring, zpow_zero]
        simpa [pow_two] using h
      have hmem : c ^ i ∈ Subgroup.zpowers c := Subgroup.zpow_mem_zpowers c i
      have hunit := eq_one_or_neg_one_of_sq_eq_one hc hord (by omega : 1 ≤ r) hneg hmem hsq
      rw [← hi] at hunit
      exact hunit
    · exfalso
      have hcomm : c * (sig K * c ^ i) = (sig K * c ^ i) * c := by
        have h := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hx) cD)
        rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
        simpa [cD, hi] using h
      have hcs : c * sig K = sig K * c ^ (-1 : ℤ) := by
        simpa using mul_sig_zpow hc (1 : ℤ)
      have hL : c * (sig K * c ^ i) = sig K * c ^ (i - 1) := by
        rw [← mul_assoc, hcs, mul_assoc, ← zpow_add]
        congr 1
        ring
      have hR : (sig K * c ^ i) * c = sig K * c ^ (i + 1) := by
        rw [mul_assoc]
        congr 1
        rw [zpow_add, zpow_one]
      have hbody : sig K * c ^ (i - 1) = sig K * c ^ (i + 1) := by
        rw [← hL, hcomm, hR]
      have h1 : c ^ (i - 1) = c ^ (i + 1) := mul_left_cancel hbody
      have h2 : c ^ (2 : ℤ) = 1 := by
        have h := congrArg (fun t => c ^ (-(i - 1)) * t) h1
        rw [← zpow_add, ← zpow_add] at h
        have e1 : -(i - 1) + (i - 1) = 0 := by ring
        have e2 : -(i - 1) + (i + 1) = 2 := by ring
        rw [e1, e2, zpow_zero] at h
        exact h.symm
      have h2n : c ^ 2 = 1 := by simpa using h2
      have hc2 : c ^ 2 ≠ 1 := by
        intro h
        have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one h
        rw [hord] at hdvd
        have hle : 2 ^ r ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
        have hge : 4 ≤ 2 ^ r := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
        omega
      exact hc2 h2n
  · rintro (h1 | h1)
    · rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h1]
      simp
    · rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h1]
      exact Commute.neg_one_right (g : GL (Fin 2) K)

theorem center_planeSylow {c : GL (Fin 2) K} {r : ℕ}
    (hc : c ∈ SO2 K) (hord : orderOf c = 2 ^ r) (hr : 2 ≤ r)
    (hneg : c ^ (2 ^ (r - 1)) = -1) :
    Subgroup.center (planeSylow c) =
      (Subgroup.zpowers (-1 : GL (Fin 2) K)).subgroupOf (planeSylow c) := by
  ext x
  rw [Subgroup.mem_subgroupOf, mem_zpowers_neg_one_iff]
  exact mem_center_planeSylow_iff hc hord hr hneg x

theorem isSylow_planeSylow [Finite K] (h2 : (2 : K) ≠ 0) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card K : ℤ) ≡ ε [ZMOD 4]) (m : ℕ) (hm : (m : ℤ) = Nat.card K - ε)
    {r m' : ℕ} (hmfac : m = 2 ^ r * m') (hm' : Odd m')
    {c : GL (Fin 2) K} (hc : c ∈ SO2 K) (hord : orderOf c = 2 ^ r) :
    ∃ S : Sylow 2 ↥(O2 K), (S : Subgroup ↥(O2 K)) = (planeSylow c).subgroupOf (O2 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDle : planeSylow c ≤ O2 K := planeSylow_le_O2 hc
  have hcardP : Nat.card ↥((planeSylow c).subgroupOf (O2 K)) = 2 ^ (r + 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv,
      card_planeSylow h2 hc hord]
  have hP : IsPGroup 2 ↥((planeSylow c).subgroupOf (O2 K)) :=
    IsPGroup.of_card (n := r + 1) hcardP
  have hO2nat : Nat.card ↥(O2 K) = 2 * m := natCard_O2_nat h2 ε hε hq m hm
  have hindex : ((planeSylow c).subgroupOf (O2 K)).index = m' := by
    have hmul := Subgroup.index_mul_card (G := ↥(O2 K))
      (H := (planeSylow c).subgroupOf (O2 K))
    rw [hcardP, hO2nat, hmfac] at hmul
    have hnorm : 2 * (2 ^ r * m') = 2 ^ (r + 1) * m' := by
      rw [pow_succ]
      ring
    rw [hnorm] at hmul
    rw [mul_comm (2 ^ (r + 1)) m'] at hmul
    exact Nat.mul_right_cancel (by positivity) hmul
  have hodd : ¬ 2 ∣ ((planeSylow c).subgroupOf (O2 K)).index := by
    rw [hindex]
    exact hm'.not_two_dvd_nat
  exact ⟨hP.toSylow hodd, IsPGroup.toSylow_coe hP hodd⟩

theorem exists_planeSylow [Finite K] (h2 : (2 : K) ≠ 0) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card K : ℤ) ≡ ε [ZMOD 4]) (m : ℕ) (hm : (m : ℤ) = Nat.card K - ε) :
    ∃ c : GL (Fin 2) K,
      c ∈ SO2 K ∧
      orderOf c = 2 ^ padicValNat 2 m ∧
      c ^ (2 ^ (padicValNat 2 m - 1)) = -1 ∧
      planeSylow c ≤ O2 K ∧
      Nat.card ↥(planeSylow c) = 2 ^ (padicValNat 2 m + 1) ∧
      Subgroup.center (planeSylow c) =
        (Subgroup.zpowers (-1 : GL (Fin 2) K)).subgroupOf (planeSylow c) ∧
      (∀ x : planeSylow c, x ∈ Subgroup.center (planeSylow c) ↔
        (x : GL (Fin 2) K) = 1 ∨ (x : GL (Fin 2) K) = -1) ∧
      (∀ x : GL (Fin 2) K, x ∈ Subgroup.zpowers c → x ^ 2 = 1 →
        x = 1 ∨ x = -1) ∧
      (∃ S : Sylow 2 ↥(O2 K), (S : Subgroup ↥(O2 K)) =
        (planeSylow c).subgroupOf (O2 K)) := by
  obtain ⟨g, hg, hordg, hall⟩ := exists_generator_SO2 h2 ε hε hq m hm
  set r : ℕ := padicValNat 2 m with hr
  set m' : ℕ := m.divMaxPow 2 with hm'
  have hmpos : 0 < m := by
    have hq2 : 1 < Nat.card K := Finite.one_lt_card (α := K)
    have hpos : (0 : ℤ) < (m : ℤ) := by
      rcases hε with rfl | rfl <;> rw [hm] <;> omega
    exact_mod_cast hpos
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hmpos
  have hfac : m = 2 ^ r * m' := by
    rw [hr, hm']
    exact (Nat.pow_padicValNat_mul_divMaxPow 2 m).symm
  have hodd : Odd m' := by
    have hnd : ¬ 2 ∣ m' := Nat.not_dvd_divMaxPow (p := 2) (n := m) (by norm_num) hm0
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
  have hm'pos : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · rw [h, mul_zero] at hfac
      omega
    · exact h
  have h4Z : (4 : ℤ) ∣ (m : ℤ) := by
    have h := hq
    rw [Int.modEq_iff_dvd] at h
    rw [hm]
    have hneg : (Nat.card K : ℤ) - ε = -(ε - (Nat.card K : ℤ)) := by ring
    rw [hneg]
    exact dvd_neg.mpr h
  have h4 : 4 ∣ m := by exact_mod_cast h4Z
  have hr2 : 2 ≤ r := by
    have h4pow : 4 ∣ 2 ^ r := by
      have hdec : 2 ^ r * m' = m := hfac.symm
      have hcop : Nat.Coprime 4 m' := by
        simpa using (Nat.coprime_two_left.mpr hodd).pow_left 2
      have hmul4 : 4 ∣ 2 ^ r * m' := by rw [hdec]; exact h4
      exact hcop.dvd_of_dvd_mul_right hmul4
    have hle : 4 ≤ 2 ^ r := Nat.le_of_dvd (by positivity) h4pow
    by_contra h
    have hrle : r ≤ 1 := by omega
    have h2le : 2 ^ r ≤ 2 := by
      calc 2 ^ r ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hrle
        _ = 2 := by norm_num
    omega
  let c : GL (Fin 2) K := g ^ m'
  have hc : c ∈ SO2 K := (SO2 K).pow_mem hg m'
  have hm'div : m' ∣ m := ⟨2 ^ r, by rw [hfac, mul_comm]⟩
  have hordc : orderOf c = 2 ^ r := by
    rw [show c = g ^ m' from rfl, orderOf_pow, hordg, Nat.gcd_eq_right hm'div]
    rw [hfac]
    exact Nat.mul_div_left (2 ^ r) hm'pos
  have hgneg : g ^ (m / 2) = -1 := by
    have heven : Even m := even_iff_two_dvd.mpr (dvd_trans (by norm_num : 2 ∣ 4) h4)
    have h2m : m = 2 * (m / 2) := (Nat.two_mul_div_two_of_even heven).symm
    exact pow_eq_neg_one_of_generator (k := m / 2) h2 (by rw [hordg]; exact h2m)
      (hall _ neg_one_mem_SO2)
  have hexp : m' * 2 ^ (r - 1) = m / 2 := by
    have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
      rw [← pow_sub_one_mul (n := r) (a := 2) (by omega : r ≠ 0), mul_comm]
    have hm2 : m = 2 * (2 ^ (r - 1) * m') := by
      rw [hfac, hpow, mul_assoc]
    rw [hm2, Nat.mul_div_right (2 ^ (r - 1) * m') (by norm_num : 0 < 2), mul_comm]
  have hneg : c ^ (2 ^ (r - 1)) = -1 := by
    rw [show c = g ^ m' from rfl, ← pow_mul, hexp, hgneg]
  refine ⟨c, hc, hordc, hneg, planeSylow_le_O2 hc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_planeSylow h2 hc hordc]
  · exact center_planeSylow hc hordc hr2 hneg
  · intro x
    exact mem_center_planeSylow_iff hc hordc hr2 hneg x
  · intro x hx hx2
    exact eq_one_or_neg_one_of_sq_eq_one hc hordc (by omega) hneg hx hx2
  · exact isSylow_planeSylow h2 ε hε hq m hm hfac hodd hc hordc

end CFSG.ClassicalGroups.Orthogonal.PlaneSylow

