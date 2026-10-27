module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

private lemma seg27_index_subgroupOf_eq_two {G : Type*} [Group G] [Finite G] {X S : Subgroup G}
    (hXS : X ≤ S) (hc : Nat.card S = 2 * Nat.card X) :
    (X.subgroupOf S).index = 2 := by
  have hcard : Nat.card (X.subgroupOf S) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXS).toEquiv
  have h := Subgroup.index_mul_card (H := X.subgroupOf S)
  rw [hcard, hc] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := X)) h

private lemma seg27_subgroupOf_normal_of_card_eq_two_mul {G : Type*} [Group G] [Finite G]
    {X S : Subgroup G} (hXS : X ≤ S) (hc : Nat.card S = 2 * Nat.card X) :
    (X.subgroupOf S).Normal :=
  Subgroup.normal_of_index_eq_two (seg27_index_subgroupOf_eq_two hXS hc)

theorem seg27_card_mul_card_le {G : Type*} [Group G] [Finite G] {A B C : Subgroup G}
    (hA : A ≤ C) (hB : B ≤ C) :
    Nat.card A * Nat.card B ≤ Nat.card C * Nat.card (A ⊓ B : Subgroup G) := by
  have hAC : A ⊓ C = A := inf_eq_left.mpr hA
  have hBC : B ⊓ C = B := inf_eq_left.mpr hB
  have hABC : (A ⊓ B) ⊓ C = A ⊓ B := inf_eq_left.mpr (le_trans inf_le_left hA)
  have h1 : A.relIndex C * Nat.card A = Nat.card C := by
    have := Subgroup.relIndex_mul_card (H := A) (K := C)
    rwa [hAC] at this
  have h2 : B.relIndex C * Nat.card B = Nat.card C := by
    have := Subgroup.relIndex_mul_card (H := B) (K := C)
    rwa [hBC] at this
  have h3 : (A ⊓ B).relIndex C * Nat.card (A ⊓ B : Subgroup G) = Nat.card C := by
    have := Subgroup.relIndex_mul_card (H := A ⊓ B) (K := C)
    rwa [hABC] at this
  have hle : (A ⊓ B).relIndex C ≤ A.relIndex C * B.relIndex C := Subgroup.relIndex_inf_le
  have h1' : Nat.card C = A.relIndex C * Nat.card A := h1.symm
  have h2' : Nat.card C = B.relIndex C * Nat.card B := h2.symm
  have h3' : Nat.card C = (A ⊓ B).relIndex C * Nat.card (A ⊓ B : Subgroup G) := h3.symm
  have hrpos : 0 < A.relIndex C * B.relIndex C := by
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have hAp : 0 < A.relIndex C := by
      by_contra hz
      rw [Nat.not_lt, Nat.le_zero] at hz
      rw [hz, zero_mul] at h1
      exact hCpos.ne' h1.symm
    have hBp : 0 < B.relIndex C := by
      by_contra hz
      rw [Nat.not_lt, Nat.le_zero] at hz
      rw [hz, zero_mul] at h2
      exact hCpos.ne' h2.symm
    exact mul_pos hAp hBp
  have key : (A.relIndex C * B.relIndex C) * (Nat.card A * Nat.card B)
      ≤ (A.relIndex C * B.relIndex C) * (Nat.card C * Nat.card (A ⊓ B : Subgroup G)) := by
    calc
      (A.relIndex C * B.relIndex C) * (Nat.card A * Nat.card B)
          = (A.relIndex C * Nat.card A) * (B.relIndex C * Nat.card B) := by ring
      _ = Nat.card C * Nat.card C := by rw [← h1', ← h2']
      _ = (Nat.card C * Nat.card (A ⊓ B : Subgroup G)) * (A ⊓ B).relIndex C := by
            rw [h3']; ring
      _ ≤ (Nat.card C * Nat.card (A ⊓ B : Subgroup G)) * (A.relIndex C * B.relIndex C) :=
            Nat.mul_le_mul_left _ hle
      _ = (A.relIndex C * B.relIndex C) * (Nat.card C * Nat.card (A ⊓ B : Subgroup G)) := by
            ring
  exact Nat.le_of_mul_le_mul_left key hrpos

theorem seg27_exists_orderOf_prime {G : Type*} [Group G] [Finite G] (A : Subgroup G) {p : ℕ}
    (hp : p.Prime) (h : p ∣ Nat.card A) : ∃ g ∈ A, orderOf g = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) p h
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem seg27_exists_orderOf_two {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    (h : 2 ∣ Nat.card A) : ∃ g ∈ A, orderOf g = 2 :=
  seg27_exists_orderOf_prime A Nat.prime_two h

theorem seg27_conj_mem_of_card_eq_two_mul {G : Type*} [Group G] [Finite G] {X S : Subgroup G}
    (hXS : X ≤ S) (hc : Nat.card S = 2 * Nat.card X) {s x : G} (hs : s ∈ S) (hx : x ∈ X) :
    s * x * s⁻¹ ∈ X := by
  have hnorm : (X.subgroupOf S).Normal := seg27_subgroupOf_normal_of_card_eq_two_mul hXS hc
  have hmem : (⟨x, hXS hx⟩ : ↥S) ∈ X.subgroupOf S := Subgroup.mem_subgroupOf.mpr hx
  have hconj := hnorm.conj_mem (⟨x, hXS hx⟩ : ↥S) hmem (⟨s, hs⟩ : ↥S)
  simpa using Subgroup.mem_subgroupOf.mp hconj

theorem seg27_mem_of_card_eq_two_mul_of_odd {G : Type*} [Group G] [Finite G] {X S : Subgroup G}
    (hXS : X ≤ S) (hc : Nat.card S = 2 * Nat.card X) {s : G} (hs : s ∈ S)
    (hodd : Odd (orderOf s)) : s ∈ X := by
  have hnorm : (X.subgroupOf S).Normal := seg27_subgroupOf_normal_of_card_eq_two_mul hXS hc
  have hindex : (X.subgroupOf S).index = 2 := seg27_index_subgroupOf_eq_two hXS hc
  haveI : (X.subgroupOf S).Normal := hnorm
  have hsq' : (⟨s, hs⟩ : ↥S) ^ 2 ∈ X.subgroupOf S := by
    have := Subgroup.pow_index_mem (X.subgroupOf S) (⟨s, hs⟩ : ↥S)
    rwa [hindex] at this
  have hsq : s ^ 2 ∈ X := by
    simpa using Subgroup.mem_subgroupOf.mp hsq'
  obtain ⟨k, hk⟩ := hodd
  have hpow : s ^ (2 * (k + 1)) = s := by
    have h1 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [h1, pow_succ, ← hk, pow_orderOf_eq_one, one_mul]
  have hs_eq : s = (s ^ 2) ^ (k + 1) := by
    rw [← pow_mul]
    exact hpow.symm
  rw [hs_eq]
  exact pow_mem hsq (k + 1)

theorem seg27_card_dvd_factorial {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (H : Subgroup G) (hH : H ≠ ⊤) : Nat.card G ∣ H.index.factorial := by
  have hNtop : H.normalCore ≠ ⊤ := fun htop =>
    hH (top_le_iff.mp (htop ▸ Subgroup.normalCore_le H))
  have hN : H.normalCore = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore).resolve_right hNtop
  have hdvd : H.normalCore.index ∣ H.index.factorial :=
    Subgroup.index_normalCore_dvd_factorial_index H
  rw [← Subgroup.index_bot, ← hN]
  exact hdvd

private lemma seg27_sylow_five_subsingleton {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = 45) : Subsingleton (Sylow 5 G) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let P : Sylow 5 G := default
  haveI : (P : Subgroup G).FiniteIndex := inferInstance
  haveI : Finite (Sylow 5 G) := Sylow.finite_of_finiteIndex P
  set n := Nat.card (Sylow 5 G) with hn
  have hmod : n % 5 = 1 := by
    have := card_sylow_modEq_one 5 G
    rw [← hn] at this
    simpa [Nat.ModEq] using this
  have hdvd45 : n ∣ 45 := by
    rw [hn, Sylow.card_eq_index_normalizer P, ← h]
    exact Subgroup.index_dvd_card _
  have h5n : ¬ 5 ∣ n := by
    intro hd
    have h0 : n % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    rw [h0] at hmod
    norm_num at hmod
  have hcop : Nat.Coprime n 5 := (Nat.prime_five.coprime_iff_not_dvd.mpr h5n).symm
  have hdvd9 : n ∣ 9 := by
    have h45 : (45 : ℕ) = 9 * 5 := by norm_num
    rw [h45] at hdvd45
    exact (hcop.dvd_mul_right).mp hdvd45
  have hnle : n ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd9
  have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hdvd9 (by norm_num)
  have hn1le : 1 ≤ n := hnpos
  have hn1 : n = 1 := by
    interval_cases n <;> omega
  exact (Nat.card_eq_one_iff_unique.mp (by rw [← hn]; exact hn1)).1

private lemma seg27_sylow_three_subsingleton {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = 45) : Subsingleton (Sylow 3 G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Sylow 3 G := default
  haveI : (Q : Subgroup G).FiniteIndex := inferInstance
  haveI : Finite (Sylow 3 G) := Sylow.finite_of_finiteIndex Q
  set n := Nat.card (Sylow 3 G) with hn
  have hmod : n % 3 = 1 := by
    have := card_sylow_modEq_one 3 G
    rw [← hn] at this
    simpa [Nat.ModEq] using this
  have hdvd45 : n ∣ 45 := by
    rw [hn, Sylow.card_eq_index_normalizer Q, ← h]
    exact Subgroup.index_dvd_card _
  have h3n : ¬ 3 ∣ n := by
    intro hd
    have h0 : n % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    rw [h0] at hmod
    norm_num at hmod
  have hcop : Nat.Coprime n 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3n).symm
  have hdvd15 : n ∣ 15 := by
    have h45 : (45 : ℕ) = 15 * 3 := by norm_num
    rw [h45] at hdvd45
    exact (hcop.dvd_mul_right).mp hdvd45
  have hnle : n ≤ 15 := Nat.le_of_dvd (by norm_num) hdvd15
  have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hdvd15 (by norm_num)
  have hn1le : 1 ≤ n := hnpos
  have hn1 : n = 1 := by
    interval_cases n <;> omega
  exact (Nat.card_eq_one_iff_unique.mp (by rw [← hn]; exact hn1)).1

theorem seg27_exists_orderOf_fifteen {G : Type*} [Group G] [Finite G] (h : Nat.card G = 45) :
    ∃ g : G, orderOf g = 15 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Subsingleton (Sylow 5 G) := seg27_sylow_five_subsingleton h
  haveI : Subsingleton (Sylow 3 G) := seg27_sylow_three_subsingleton h
  let P : Sylow 5 G := default
  let Q : Sylow 3 G := default
  have hPnorm : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  have hQnorm : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
  have hdisj : Disjoint (P : Subgroup G) (Q : Subgroup G) :=
    IsPGroup.disjoint_of_ne 5 3 (by norm_num) P.1 Q.1 P.2 Q.2
  have hbot : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := disjoint_iff.mp hdisj
  have h5dvd : 5 ∣ Nat.card (P : Subgroup G) := P.dvd_card_of_dvd_card (by rw [h]; norm_num)
  obtain ⟨y, hyP, hy5⟩ := seg27_exists_orderOf_prime (P : Subgroup G) Nat.prime_five h5dvd
  have h3dvd : 3 ∣ Nat.card (Q : Subgroup G) := Q.dvd_card_of_dvd_card (by rw [h]; norm_num)
  obtain ⟨x, hxQ, hx3⟩ := seg27_exists_orderOf_prime (Q : Subgroup G) Nat.prime_three h3dvd
  have hcP : x * y * x⁻¹ * y⁻¹ ∈ (P : Subgroup G) := by
    have h1 : x * y * x⁻¹ ∈ (P : Subgroup G) := hPnorm.conj_mem y hyP x
    exact mul_mem h1 (inv_mem hyP)
  have hcQ : x * y * x⁻¹ * y⁻¹ ∈ (Q : Subgroup G) := by
    have h2 : y * x⁻¹ * y⁻¹ ∈ (Q : Subgroup G) := hQnorm.conj_mem x⁻¹ (inv_mem hxQ) y
    have h3 : x * (y * x⁻¹ * y⁻¹) ∈ (Q : Subgroup G) := mul_mem hxQ h2
    simpa [mul_assoc] using h3
  have hc : x * y * x⁻¹ * y⁻¹ = 1 := by
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ (P : Subgroup G) ⊓ (Q : Subgroup G) := ⟨hcP, hcQ⟩
    rw [hbot] at hmem
    simpa using hmem
  have hcomm : Commute x y := by
    have h1 : (x * y) * (y * x)⁻¹ = 1 := by simpa [mul_inv_rev, mul_assoc] using hc
    exact mul_inv_eq_one.mp h1
  refine ⟨x * y, ?_⟩
  calc orderOf (x * y) = orderOf x * orderOf y :=
        hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx3, hy5]; norm_num)
    _ = 15 := by rw [hx3, hy5]

private lemma seg27_mem_cycleType_of_prime_dvd_order {g : Equiv.Perm (Fin 6)} {p : ℕ}
    (hp : p.Prime) (hp15 : p ∣ 15) (hp35 : p = 3 ∨ p = 5) (h15 : orderOf g = 15) :
    ∃ n ∈ g.cycleType, p ∣ n := by
  by_contra hcon
  push Not at hcon
  have hct : g.cycleType.lcm = 15 := by rw [Equiv.Perm.lcm_cycleType, h15]
  have hdiv : g.cycleType.lcm ∣ 15 / p :=
    Multiset.lcm_dvd.2 fun n hn => by
      have hdvd15 : n ∣ 15 := by
        simpa [h15] using Equiv.Perm.dvd_of_mem_cycleType hn
      have hnp : ¬ p ∣ n := hcon n hn
      have hcop : Nat.Coprime n p := (hp.coprime_iff_not_dvd.mpr hnp).symm
      have h15eq : (15 : ℕ) = (15 / p) * p := (Nat.div_mul_cancel hp15).symm
      rw [h15eq] at hdvd15
      exact (hcop.dvd_mul_right).mp hdvd15
  rw [hct] at hdiv
  rcases hp35 with rfl | rfl
  · norm_num at hdiv
  · norm_num at hdiv

theorem seg27_orderOf_ne_fifteen (g : Equiv.Perm (Fin 6)) : orderOf g ≠ 15 := by
  intro h15
  obtain ⟨n5, hn5mem, hn5dvd⟩ :=
    seg27_mem_cycleType_of_prime_dvd_order Nat.prime_five (by norm_num) (Or.inr rfl) h15
  obtain ⟨n3, hn3mem, hn3dvd⟩ :=
    seg27_mem_cycleType_of_prime_dvd_order Nat.prime_three (by norm_num) (Or.inl rfl) h15
  have hn5le : n5 ≤ 6 :=
    le_trans (Multiset.le_sum_of_mem hn5mem) (by simpa using Equiv.Perm.sum_cycleType_le g)
  have hn5ge : 2 ≤ n5 := Equiv.Perm.two_le_of_mem_cycleType hn5mem
  have hn5 : n5 = 5 := by
    interval_cases n5 <;> omega
  have hn3ge : 2 ≤ n3 := Equiv.Perm.two_le_of_mem_cycleType hn3mem
  have hn3ge3 : 3 ≤ n3 := Nat.le_of_dvd (by omega) hn3dvd
  have hn3ne5 : n3 ≠ 5 := by
    rintro rfl
    norm_num at hn3dvd
  have htm : (5 : ℕ) ∈ g.cycleType := hn5 ▸ hn5mem
  have hsum8 : 8 ≤ g.cycleType.sum := by
    have hcons : (5 : ℕ) ::ₘ g.cycleType.erase 5 = g.cycleType := Multiset.cons_erase htm
    rw [← hcons, Multiset.sum_cons]
    have hmemn3 : n3 ∈ g.cycleType.erase 5 := (Multiset.mem_erase_of_ne hn3ne5).mpr hn3mem
    have hle := Multiset.le_sum_of_mem hmemn3
    omega
  have hsum6 : g.cycleType.sum ≤ 6 := by simpa using Equiv.Perm.sum_cycleType_le g
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
