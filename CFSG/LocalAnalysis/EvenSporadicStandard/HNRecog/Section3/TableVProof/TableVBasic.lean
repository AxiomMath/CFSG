module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem tableV_Gxy_eq_Gxyz_pow (a c : G) (n : ℕ) : Gxy a c = Gxyz a ((a * c) ^ n) c := by
  ext g
  simp only [mem_Gxy, mem_Gxyz, mem_Gx]
  constructor
  · rintro ⟨ha, hc⟩
    refine ⟨ha, ?_, hc⟩
    exact ((show Commute a g from ha).mul_left (show Commute c g from hc)).pow_left n
  · rintro ⟨ha, -, hc⟩
    exact ⟨ha, hc⟩

theorem tableV_dihedral {a c : G} (ha : a ^ 2 = 1) (hc : c ^ 2 = 1) (hac : IsConj a c) {m : ℕ}
    (hm : orderOf (a * c) = 2 * m) :
    a * (a * c) ^ m = (a * c) ^ m * a ∧ c * (a * c) ^ m = (a * c) ^ m * c ∧
      IsConj a (a * (a * c) ^ m) ∧ IsConj a (c * (a * c) ^ m) := by
  have haa : a * a = 1 := by simpa [pow_two] using ha
  have hcc : c * c = 1 := by simpa [pow_two] using hc
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hconj_a : a * (a * c) * a⁻¹ = (a * c)⁻¹ := by
    have hl : a * (a * c) * a⁻¹ = c * a := by
      rw [← mul_assoc, haa, one_mul, hai]
    rw [hl, mul_inv_rev, hai, hci]
  have hconj_c : c * (a * c) * c⁻¹ = (a * c)⁻¹ := by
    have hl : c * (a * c) * c⁻¹ = c * a := by group
    rw [hl, mul_inv_rev, hai, hci]
  have hconj_nat : ∀ n : ℕ, a * (a * c) ^ n * a⁻¹ = ((a * c) ^ n)⁻¹ := by
    intro n
    have h := congrArg (fun z => z ^ n) hconj_a
    rwa [conj_pow, inv_pow] at h
  have hconj_nat_c : ∀ n : ℕ, c * (a * c) ^ n * c⁻¹ = ((a * c) ^ n)⁻¹ := by
    intro n
    have h := congrArg (fun z => z ^ n) hconj_c
    rwa [conj_pow, inv_pow] at h
  have hs2 : ((a * c) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm m 2, ← hm]
    exact pow_orderOf_eq_one (a * c)
  have hsinv : ((a * c) ^ m)⁻¹ = (a * c) ^ m :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs2)
  have ha_comm : a * (a * c) ^ m = (a * c) ^ m * a := by
    have h := hconj_nat m
    rw [hsinv] at h
    calc a * (a * c) ^ m = (a * (a * c) ^ m * a⁻¹) * a := by group
      _ = (a * c) ^ m * a := by rw [h]
  have hc_comm : c * (a * c) ^ m = (a * c) ^ m * c := by
    have h := hconj_nat_c m
    rw [hsinv] at h
    calc c * (a * c) ^ m = (c * (a * c) ^ m * c⁻¹) * c := by group
      _ = (a * c) ^ m * c := by rw [h]
  have hconj_a_even : ∀ j : ℕ, IsConj a (a * (a * c) ^ (2 * j)) := by
    intro j
    refine isConj_iff.mpr ⟨((a * c) ^ j)⁻¹, ?_⟩
    have h1 : a * (a * c) ^ j = ((a * c) ^ j)⁻¹ * a := by
      have h := hconj_nat j
      calc a * (a * c) ^ j = (a * (a * c) ^ j * a⁻¹) * a := by group
        _ = ((a * c) ^ j)⁻¹ * a := by rw [h]
    have h2 : ((a * c) ^ j)⁻¹ * ((a * c) ^ j)⁻¹ = ((a * c) ^ (2 * j))⁻¹ := by
      rw [← pow_two, inv_pow, ← pow_mul, Nat.mul_comm j 2]
    have h3 : ((a * c) ^ (2 * j))⁻¹ * a = a * (a * c) ^ (2 * j) := by
      have h := hconj_nat (2 * j)
      calc ((a * c) ^ (2 * j))⁻¹ * a = (a * (a * c) ^ (2 * j) * a⁻¹) * a := by rw [h]
        _ = a * (a * c) ^ (2 * j) := by group
    calc ((a * c) ^ j)⁻¹ * a * (((a * c) ^ j)⁻¹)⁻¹
        = ((a * c) ^ j)⁻¹ * (a * (a * c) ^ j) := by group
      _ = ((a * c) ^ j)⁻¹ * (((a * c) ^ j)⁻¹ * a) := by rw [h1]
      _ = (((a * c) ^ j)⁻¹ * ((a * c) ^ j)⁻¹) * a := by group
      _ = ((a * c) ^ (2 * j))⁻¹ * a := by rw [h2]
      _ = a * (a * c) ^ (2 * j) := h3
  have hconj_c_even : ∀ j : ℕ, IsConj c (c * (a * c) ^ (2 * j)) := by
    intro j
    refine isConj_iff.mpr ⟨((a * c) ^ j)⁻¹, ?_⟩
    have h1 : c * (a * c) ^ j = ((a * c) ^ j)⁻¹ * c := by
      have h := hconj_nat_c j
      calc c * (a * c) ^ j = (c * (a * c) ^ j * c⁻¹) * c := by group
        _ = ((a * c) ^ j)⁻¹ * c := by rw [h]
    have h2 : ((a * c) ^ j)⁻¹ * ((a * c) ^ j)⁻¹ = ((a * c) ^ (2 * j))⁻¹ := by
      rw [← pow_two, inv_pow, ← pow_mul, Nat.mul_comm j 2]
    have h3 : ((a * c) ^ (2 * j))⁻¹ * c = c * (a * c) ^ (2 * j) := by
      have h := hconj_nat_c (2 * j)
      calc ((a * c) ^ (2 * j))⁻¹ * c = (c * (a * c) ^ (2 * j) * c⁻¹) * c := by rw [h]
        _ = c * (a * c) ^ (2 * j) := by group
    calc ((a * c) ^ j)⁻¹ * c * (((a * c) ^ j)⁻¹)⁻¹
        = ((a * c) ^ j)⁻¹ * (c * (a * c) ^ j) := by group
      _ = ((a * c) ^ j)⁻¹ * (((a * c) ^ j)⁻¹ * c) := by rw [h1]
      _ = (((a * c) ^ j)⁻¹ * ((a * c) ^ j)⁻¹) * c := by group
      _ = ((a * c) ^ (2 * j))⁻¹ * c := by rw [h2]
      _ = c * (a * c) ^ (2 * j) := h3
  rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
  · refine ⟨ha_comm, hc_comm, hconj_a_even j, hac.trans (hconj_c_even j)⟩
  · have hc_eq : c = a * (a * c) := by rw [← mul_assoc, haa, one_mul]
    have he : a * (a * c) ^ (2 * j + 1) = c * (a * c) ^ (2 * j) := by
      calc a * (a * c) ^ (2 * j + 1) = a * ((a * c) * (a * c) ^ (2 * j)) := by rw [pow_succ']
        _ = (a * (a * c)) * (a * c) ^ (2 * j) := (mul_assoc a (a * c) _).symm
        _ = c * (a * c) ^ (2 * j) := by rw [← hc_eq]
    have he2 : c * (a * c) ^ (2 * j + 1) = a * (a * c) ^ (2 * (j + 1)) := by
      have hr : (a * c) * (a * c) ^ (2 * j + 1) = (a * c) ^ (2 * (j + 1)) := by
        conv_rhs => rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, pow_succ']
      nth_rewrite 1 [hc_eq]
      rw [← hr, mul_assoc]
    exact ⟨ha_comm, hc_comm, he ▸ hac.trans (hconj_c_even j), he2 ▸ hconj_a_even (j + 1)⟩

theorem tableV_orderOf_orb4A {a z c : G} (h : IsF5Type a z) (hc : c ∈ orb4A a z a) :
    orderOf (a * c) = 4 := by
  have hc' : IsConj a c ∧ IsConj z ((a * c) ^ 2) := hc
  exact perp_orderOf_eq_four (perp_orderOf_of_isConj_z h hc'.2)

theorem tableV_orderOf_orb4B {a z c : G} (h : IsF5Type a z) (hc : c ∈ orb4B a a) :
    orderOf (a * c) = 4 := by
  have hc' : IsConj a c ∧ IsConj a ((a * c) ^ 2) := hc
  exact perp_orderOf_eq_four (perp_orderOf_of_isConj_a h hc'.2)

theorem tableV_orb4B_row {a z c : G} (h : IsF5Type a z) (hc : c ∈ orb4B a a) :
    (a * c) ^ 2 ∈ orb2A a a ∧ c ∈ sSet a z ((a * c) ^ 2) 2 := by
  have hc' : IsConj a c ∧ IsConj a ((a * c) ^ 2) := hc
  obtain ⟨hac, hbA⟩ := hc'
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hc2 : c ^ 2 = 1 := by
    have hco : orderOf c = 2 := perp_orderOf_of_isConj_a h hac
    rw [← hco]
    exact pow_orderOf_eq_one c
  have hb2 : orderOf ((a * c) ^ 2) = 2 := perp_orderOf_of_isConj_a h hbA
  have hord : orderOf (a * c) = 4 := tableV_orderOf_orb4B h hc
  obtain ⟨hab, hbc, hab_conj, hcb_conj⟩ :=
    tableV_dihedral ha2 hc2 hac (m := 2) (by rw [hord])
  refine ⟨⟨hbA, hab_conj⟩, ?_⟩
  have hbase : c ∈ sBase a ((a * c) ^ 2) := by
    refine ⟨hac, ?_, ?_, ?_⟩
    · rw [← hbc]
      exact hcb_conj
    · intro hca
      have h1 : orderOf (a * c) = 1 := by rw [hca, ← pow_two, ha2, orderOf_one]
      omega
    · intro hca'
      have h2 : orderOf (a * c) = 2 := by
        have he : a * c = (a * c) ^ 2 := by
          conv_lhs => rw [hca']
          rw [← mul_assoc, ← pow_two, ha2, one_mul]
        rw [he, hb2]
      omega
  exact ⟨hbase, rfl⟩

theorem tableV_orb6A_row {a z c : G} (h : IsF5Type a z) (hc : c ∈ orb6A a a) :
    (a * c) ^ 3 ∈ orb2A a a ∧ c ∈ sSet a z ((a * c) ^ 3) 5 := by
  have hc' : IsConj a c ∧ orderOf (a * c) = 6 ∧ IsConj a ((a * c) ^ 3) := hc
  obtain ⟨hac, hord, hbA⟩ := hc'
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hc2 : c ^ 2 = 1 := by
    have hco : orderOf c = 2 := perp_orderOf_of_isConj_a h hac
    rw [← hco]
    exact pow_orderOf_eq_one c
  have hb2 : orderOf ((a * c) ^ 3) = 2 := perp_orderOf_of_isConj_a h hbA
  obtain ⟨hab, hbc, hab_conj, hcb_conj⟩ :=
    tableV_dihedral ha2 hc2 hac (m := 3) (by rw [hord])
  refine ⟨⟨hbA, hab_conj⟩, ?_⟩
  have hbase : c ∈ sBase a ((a * c) ^ 3) := by
    refine ⟨hac, ?_, ?_, ?_⟩
    · rw [← hbc]
      exact hcb_conj
    · intro hca
      have h1 : orderOf (a * c) = 1 := by rw [hca, ← pow_two, ha2, orderOf_one]
      omega
    · intro hca'
      have h2 : orderOf (a * c) = 2 := by
        have he : a * c = (a * c) ^ 3 := by
          conv_lhs => rw [hca']
          rw [← mul_assoc, ← pow_two, ha2, one_mul]
        rw [he, hb2]
      omega
  exact ⟨hbase, rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
