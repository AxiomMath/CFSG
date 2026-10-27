module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueThreeAdicFusion

public section

namespace CFSG.Semidihedral.UnitaryDValue

section General

variable {G : Type*} [Group G]

theorem mul_inv_mem_iff_of_mul_inv_mem {H : Subgroup G} {a b c : G} (h : a * b⁻¹ ∈ H) :
    c * b⁻¹ ∈ H ↔ c * a⁻¹ ∈ H := by
  constructor
  · intro hc
    have e : c * a⁻¹ = c * b⁻¹ * (a * b⁻¹)⁻¹ := by group
    rw [e]
    exact H.mul_mem hc (H.inv_mem h)
  · intro hc
    have e : c * b⁻¹ = c * a⁻¹ * (a * b⁻¹) := by group
    rw [e]
    exact H.mul_mem hc h

end General

namespace DValueData

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem CT_commutator_mem_C {g h : G} (hg : g ∈ D.CT) (hh : h ∈ D.CT) :
    g * h * g⁻¹ * h⁻¹ ∈ D.C := by
  obtain ⟨c₁, hc₁, i, rfl⟩ := hg
  obtain ⟨c₂, hc₂, j, rfl⟩ := hh
  have e : c₁ * D.t ^ i * (c₂ * D.t ^ j) * (c₁ * D.t ^ i)⁻¹ * (c₂ * D.t ^ j)⁻¹ =
      c₁ * (D.t ^ i * c₂ * (D.t ^ i)⁻¹) * (D.t ^ j * c₁⁻¹ * (D.t ^ j)⁻¹) * c₂⁻¹ := by
    group
  rw [e]
  exact D.C.mul_mem (D.C.mul_mem (D.C.mul_mem hc₁
    (D.conj_mem_C (zpow_mem D.t_mem_normalizer_T i) hc₂))
    (D.conj_mem_C (zpow_mem D.t_mem_normalizer_T j) (D.C.inv_mem hc₁))) (D.C.inv_mem hc₂)

theorem conj_zpow_mul_zpow_mem_C {g a : G} (ha : a ∈ Subgroup.normalizer (D.T : Set G))
    (h : g * a * g⁻¹ * a ∈ D.C) (i : ℤ) : g * a ^ i * g⁻¹ * a ^ i ∈ D.C := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · rw [zpow_natCast]
    exact D.conj_pow_mul_pow_mem_C ha h n
  · have hX := D.conj_pow_mul_pow_mem_C ha h n
    have e : g * a ^ (-(n : ℤ)) * g⁻¹ * a ^ (-(n : ℤ)) =
        (a ^ n * (g * a ^ n * g⁻¹ * a ^ n) * (a ^ n)⁻¹)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
      group
    rw [e]
    exact D.C.inv_mem (D.conj_mem_C (pow_mem ha n) hX)

theorem y_conj_mul_mem_C {g : G} (hg : g ∈ D.CT) : D.y * g * D.y⁻¹ * g ∈ D.C := by
  obtain ⟨c, hc, i, rfl⟩ := hg
  have hti : D.y * D.t ^ i * D.y⁻¹ * D.t ^ i ∈ D.C :=
    D.conj_zpow_mul_zpow_mem_C D.t_mem_normalizer_T D.y_t_y_inv_t_mem_C i
  have e : D.y * (c * D.t ^ i) * D.y⁻¹ * (c * D.t ^ i) =
      (D.y * c * D.y⁻¹) * (D.y * D.t ^ i * D.y⁻¹ * D.t ^ i) *
        ((D.t ^ i)⁻¹ * c * ((D.t ^ i)⁻¹)⁻¹) := by
    group
  rw [e]
  exact D.C.mul_mem (D.C.mul_mem (D.conj_mem_C D.y_mem_normalizer_T hc) hti)
    (D.conj_mem_C (inv_mem (zpow_mem D.t_mem_normalizer_T i)) hc)

theorem mul_y_conj_mul_mem_C {h w : G} (hh : h ∈ D.CT) (hw : w ∈ D.CT) :
    h * D.y * w * (h * D.y)⁻¹ * w ∈ D.C := by
  have e : h * D.y * w * (h * D.y)⁻¹ * w =
      (h * (D.y * w * D.y⁻¹ * w) * h⁻¹) * (h * w⁻¹ * h⁻¹ * w⁻¹⁻¹) := by
    group
  rw [e]
  exact D.C.mul_mem (D.conj_mem_C (D.CT_le_normalizer_T hh) (D.y_conj_mul_mem_C hw))
    (D.CT_commutator_mem_C hh (inv_mem hw))

theorem mem_P_of_mem_QT_of_mem_C {g : G} (hgQ : g ∈ D.QT) (hgC : g ∈ D.C) :
    g ∈ D.primaryPart 3 :=
  ⟨hgC, D.three_element_of_mem_QT hgQ⟩

theorem QT_commutator_mem_P {g h : G} (hg : g ∈ D.QT) (hh : h ∈ D.QT) :
    g * h * g⁻¹ * h⁻¹ ∈ D.primaryPart 3 :=
  D.mem_P_of_mem_QT_of_mem_C
    (D.QT.mul_mem (D.QT.mul_mem (D.QT.mul_mem hg hh) (D.QT.inv_mem hg)) (D.QT.inv_mem hh))
    (D.CT_commutator_mem_C (D.QT_le_CT hg) (D.QT_le_CT hh))

theorem exists_eq_mul_tThree_zpow {r : G} (hr : r ∈ D.CT) :
    ∃ c ∈ D.C, ∃ i : ℤ, r = c * D.tThree ^ i := by
  obtain ⟨c, hc, i, rfl⟩ := hr
  have he : ((3 : ℕ) : ℤ) ∣ 1 - (D.threeExponent : ℤ) := by
    have h1 := D.threeExponent_mod
    have h2 : (D.threeExponent : ℤ) % 3 = 1 := by exact_mod_cast h1
    omega
  obtain ⟨m, hm⟩ := dvd_mul_of_dvd_right he i
  have hsplit : D.t ^ i = D.t ^ (i * (1 - (D.threeExponent : ℤ))) * D.tThree ^ i := by
    have hτ : D.tThree = D.t ^ (D.threeExponent : ℤ) := by
      rw [zpow_natCast]
      rfl
    rw [hτ, ← zpow_mul, ← zpow_add]
    congr 1
    ring
  refine ⟨c * D.t ^ (i * (1 - (D.threeExponent : ℤ))), D.C.mul_mem hc ?_, i, ?_⟩
  · rw [hm, zpow_mul, zpow_natCast]
    exact D.C.zpow_mem D.t_cube_mem_C m
  · rw [hsplit, mul_assoc]

theorem exists_conj_QT_of_mem_CT {r w w' : G} (hr : r ∈ D.CT) (hw : w ∈ D.QT) (hw' : w' ∈ D.QT)
    (hrw : r * w * r⁻¹ = w') : ∃ q ∈ D.QT, q * w * q⁻¹ = w' := by
  obtain ⟨c, hc, i, rfl⟩ := D.exists_eq_mul_tThree_zpow hr
  obtain ⟨c₃, c₃', n, hc₃z, hc₃'z, hcomm, hprod, hc₃o, hc₃'o⟩ :=
    finite_prime_primary_factorization c 3 Nat.prime_three
  have hzc : Subgroup.zpowers c ≤ D.C := (Subgroup.zpowers_le).mpr hc
  have hc₃C : c₃ ∈ D.C := hzc hc₃z
  have hc₃'C : c₃' ∈ D.C := hzc hc₃'z
  have hc₃P : c₃ ∈ D.primaryPart 3 := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hc₃o
    exact ⟨hc₃C, k, hk⟩
  have hτi : D.tThree ^ i ∈ D.QT := zpow_mem D.tThree_mem_QT i
  set q := c₃ * D.tThree ^ i with hq
  have hqQ : q ∈ D.QT := D.QT.mul_mem (D.P_le_QT hc₃P) hτi
  set w₂ := q * w * q⁻¹ with hw₂
  have hw₂Q : w₂ ∈ D.QT := D.QT.mul_mem (D.QT.mul_mem hqQ hw) (D.QT.inv_mem hqQ)
  have hcc : c = c₃' * c₃ := by rw [← hprod, hcomm.eq]
  have hw'eq : w' = c₃' * w₂ * c₃'⁻¹ := by
    rw [← hrw, hw₂, hq, hcc]
    group
  set e := w₂ * c₃'⁻¹ * w₂⁻¹ with he
  have heC : e ∈ D.C :=
    D.conj_mem_C (D.QT_le_normalizer_T hw₂Q) (D.C.inv_mem hc₃'C)
  have heo : orderOf e = orderOf c₃' := by
    rw [he, orderOf_conj_eq, orderOf_inv]
  have hdQ : c₃' * e ∈ D.QT := by
    have : c₃' * e = w' * w₂⁻¹ := by
      rw [hw'eq, he]
      group
    rw [this]
    exact D.QT.mul_mem hw' (D.QT.inv_mem hw₂Q)
  have hdcop : Nat.Coprime 3 (orderOf (c₃' * e)) := by
    have hce : Commute c₃' e := D.C_comm _ hc₃'C _ heC
    refine Nat.Coprime.coprime_dvd_right hce.orderOf_mul_dvd_mul_orderOf ?_
    rw [heo]
    exact Nat.Coprime.mul_right hc₃'o hc₃'o
  obtain ⟨k, hk⟩ := D.three_element_of_mem_QT hdQ
  have hk0 : k = 0 := by
    rw [hk] at hdcop
    by_contra hk0
    have : 3 ∣ 3 ^ k := dvd_pow_self 3 hk0
    exact absurd (Nat.Coprime.eq_one_of_dvd hdcop this) (by norm_num)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  refine ⟨q, hqQ, ?_⟩
  rw [hw'eq]
  have h1 : c₃' * w₂ * c₃'⁻¹ * w₂⁻¹ = 1 := by
    rw [← hk, he]
    group
  have h2 : c₃' * w₂ * c₃'⁻¹ = w₂ := by
    calc c₃' * w₂ * c₃'⁻¹ = c₃' * w₂ * c₃'⁻¹ * w₂⁻¹ * w₂ := by group
      _ = w₂ := by rw [h1, one_mul]
  rw [h2]

theorem mul_tThree_inv_mem_or {v : G} (hv : v ∈ D.QT) (hvP : v ∉ D.primaryPart 3) :
    v * D.tThree⁻¹ ∈ D.primaryPart 3 ∨ v * D.tThree ∈ D.primaryPart 3 := by
  obtain ⟨u, hu, i, hi, rfl⟩ := D.exists_of_mem_QT_not_mem_P hv hvP
  have hcases : i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hcases with h | h
  · left
    have h3 : (3 : ℤ) ∣ i - 1 := by omega
    have e : u * D.tThree ^ i * D.tThree⁻¹ = u * D.tThree ^ (i - 1) := by
      rw [zpow_sub_one, mul_assoc]
    rw [e]
    exact (D.primaryPart 3).mul_mem hu (D.tThree_zpow_mem_P3 h3)
  · right
    have h3 : (3 : ℤ) ∣ i + 1 := by omega
    have e : u * D.tThree ^ i * D.tThree = u * D.tThree ^ (i + 1) := by
      rw [zpow_add_one, mul_assoc]
    rw [e]
    exact (D.primaryPart 3).mul_mem hu (D.tThree_zpow_mem_P3 h3)

namespace Exceptional

variable {D} (E : D.Exceptional)

include E in
theorem mem_CT_of_fix {g : G} (hg : g ∈ Subgroup.normalizer (D.T : Set G))
    (hfix : g * E.u₀ ^ 3 * g⁻¹ = E.u₀ ^ 3) : g ∈ D.CT := by
  obtain ⟨i, j, -, hj, hc⟩ := D.normalizer_T_cases hg
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · have hc' : (D.t ^ i)⁻¹ * g ∈ D.C := by simpa using hc
    have ht : D.t ∈ D.CT := ⟨1, D.C.one_mem, 1, by simp⟩
    have hg'' : g = D.t ^ i * ((D.t ^ i)⁻¹ * g) := by group
    rw [hg'']
    exact mul_mem (pow_mem ht i) (D.C_le_CT hc')
  · exfalso
    have hc1 : (D.t ^ i * D.y)⁻¹ * g ∈ D.C := by simpa using hc
    have hg1 : g = D.t ^ i * (D.y * ((D.t ^ i * D.y)⁻¹ * g)) := by group
    have hz : g * E.u₀ ^ 3 * g⁻¹ = (E.u₀ ^ 3)⁻¹ := by
      rw [hg1, conj_mul_eq, conj_mul_eq,
        D.C_conj hc1 (E.Z_le_C E.u₀_cube_mem_Z), D.y_W _ (E.Z_le_W E.u₀_cube_mem_Z)]
      exact conj_eq_of_comm ((Commute.pow_left
        (E.t_comm_Z ((E.Z).inv_mem E.u₀_cube_mem_Z) : Commute D.t _) i).eq)
    exact E.u₀_cube_inv_ne (hz.symm.trans hfix)

theorem u₀_cube_ne_one : E.u₀ ^ 3 ≠ 1 := by
  intro h
  apply E.u₀_cube_inv_ne
  rw [h, inv_one]

end Exceptional

end DValueData

end CFSG.Semidihedral.UnitaryDValue
