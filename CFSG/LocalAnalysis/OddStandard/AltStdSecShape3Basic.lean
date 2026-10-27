module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalCentral
public import CFSG.LocalAnalysis.OddStandard.AltStdBalJ

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem sq_mem_L_of_mem_sup (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {c : G} (hc : c ∈ L ⊔ Q) :
    c ^ 2 ∈ L := by
  obtain ⟨l, hl, q, hq, rfl⟩ := (mem_sup_iff_mul d).1 hc
  have hcomm : q * l = l * q := (d.comm_L hq hl).symm
  have hq2 : q * q = 1 := by
    rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with rfl | rfl
    · simp
    · exact d.mul_self
  have : (l * q) ^ 2 = l ^ 2 := by
    calc (l * q) ^ 2 = l * q * (l * q) := by rw [sq]
      _ = l * (q * l) * q := by group
      _ = l * (l * q) * q := by rw [hcomm]
      _ = (l * l) * (q * q) := by group
      _ = l * l := by rw [hq2, mul_one]
      _ = l ^ 2 := by rw [sq]
  rw [this]
  exact pow_mem hl 2

theorem comm_of_mem_Q (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {q c : G} (hq : q ∈ Q)
    (hc : c ∈ centralizer ({z} : Set G)) : c * q = q * c := by
  rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with rfl | rfl
  · simp
  · exact mem_centralizer_singleton_iff.1 hc

theorem inv_conj_mul_mem_L (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u c' : G}
    (hu : u ∈ centralizer ({z} : Set G)) (hc' : c' ∈ L ⊔ Q) : u⁻¹ * c' * u * c' ∈ L := by
  obtain ⟨l, hl, q, hq, rfl⟩ := (mem_sup_iff_mul d).1 hc'
  have hqu : u * q = q * u := comm_of_mem_Q d hQ2 hq hu
  have hl' : u⁻¹ * l * u ∈ L := by
    have := (mem_normalizer_iff.1 (AltStdBal.centralizer_le_normalizer h d (inv_mem hu)) l).1 hl
    simpa using this
  have hq2 : q * q = 1 := by
    rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with rfl | rfl
    · simp
    · exact d.mul_self
  have hql : q * l = l * q := (d.comm_L hq hl).symm
  have hqinv : u⁻¹ * q * u = q := by
    calc u⁻¹ * q * u = u⁻¹ * (q * u) := by group
      _ = u⁻¹ * (u * q) := by rw [hqu]
      _ = q := by group
  have : u⁻¹ * (l * q) * u * (l * q) = (u⁻¹ * l * u) * l := by
    calc u⁻¹ * (l * q) * u * (l * q) = (u⁻¹ * l * u) * (u⁻¹ * q * u) * (l * q) := by group
      _ = (u⁻¹ * l * u) * q * (l * q) := by rw [hqinv]
      _ = (u⁻¹ * l * u) * (q * l) * q := by group
      _ = (u⁻¹ * l * u) * (l * q) * q := by rw [hql]
      _ = (u⁻¹ * l * u) * l * (q * q) := by group
      _ = (u⁻¹ * l * u) * l := by rw [hq2, mul_one]
  rw [this]
  exact mul_mem hl' hl

theorem orderOf_eq_four_of_sq_eq (d : Cyc L Q z) {u : G} (hu2 : u ^ 2 = z) : orderOf u = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := by rw [sq]; exact d.mul_self
  have hz1 : z ≠ 1 := by
    intro h1
    have := d.order
    rw [h1, orderOf_one] at this
    omega
  have h1 : ¬ u ^ (2 ^ 1) = 1 := by rw [pow_one, hu2]; exact hz1
  have h2 : u ^ (2 ^ (1 + 1)) = 1 := by
    calc u ^ (2 ^ (1 + 1)) = (u ^ 2) ^ 2 := by rw [← pow_mul]; norm_num
      _ = 1 := by rw [hu2]; exact hz2
  have := orderOf_eq_prime_pow h1 h2
  simpa using this

theorem conj_mem_sup (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {c x : G}
    (hc : c ∈ centralizer ({z} : Set G)) (hx : x ∈ L ⊔ Q) : c * x * c⁻¹ ∈ L ⊔ Q := by
  obtain ⟨l, hl, q, hq, rfl⟩ := (mem_sup_iff_mul d).1 hx
  have hcq : c * q = q * c := comm_of_mem_Q d hQ2 hq hc
  have hl' : c * l * c⁻¹ ∈ L :=
    (mem_normalizer_iff.1 (AltStdBal.centralizer_le_normalizer h d hc) l).1 hl
  have hcq' : q * c⁻¹ = c⁻¹ * q := by
    have h1 : c⁻¹ * (c * q) * c⁻¹ = c⁻¹ * (q * c) * c⁻¹ := by rw [hcq]
    simpa [mul_assoc] using h1
  have : c * (l * q) * c⁻¹ = (c * l * c⁻¹) * q := by
    calc c * (l * q) * c⁻¹ = c * l * (q * c⁻¹) := by group
      _ = c * l * (c⁻¹ * q) := by rw [hcq']
      _ = (c * l * c⁻¹) * q := by group
  rw [this]
  exact Subgroup.mul_mem_sup hl' hq

theorem sq_mem_mul_L_of_outer (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    {u : G} (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = z)
    {r : G} (hr : r ∈ centralizer ({z} : Set G)) (hrL : r ∉ L ⊔ Q) :
    ∃ l ∈ L, r * r = z * l := by
  rcases mem_sup_or_inv_mul_mem_sup h d hu huL hr with h1 | h1
  · exact absurd h1 hrL
  · refine ⟨u⁻¹ * (u⁻¹ * r) * u * (u⁻¹ * r), inv_conj_mul_mem_L h d hQ2 hu h1, ?_⟩
    calc r * r = (u * (u⁻¹ * r)) * (u * (u⁻¹ * r)) := by group
      _ = (u * u) * (u⁻¹ * (u⁻¹ * r) * u * (u⁻¹ * r)) := by group
      _ = z * (u⁻¹ * (u⁻¹ * r) * u * (u⁻¹ * r)) := by rw [← sq, hu2]

end CFSG.OddStandard.AltStdSec
