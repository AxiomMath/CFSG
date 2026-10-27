module

public import Mathlib.GroupTheory.Transfer

public section

open scoped commutatorElement

namespace CFSG.GroupTheory

theorem sylow_eq_bot_of_normalizer_le_centralizer_of_perfect {H : Type*} [Group H] [Finite H]
    (hperf : commutator H = ⊤) {r : ℕ} [Fact r.Prime] (P : Sylow r H)
    (hP : Subgroup.normalizer ((P : Subgroup H) : Set H) ≤
      Subgroup.centralizer ((P : Subgroup H) : Set H)) :
    (P : Subgroup H) = ⊥ := by
  classical
  let φ : H →* ↥P := MonoidHom.transferSylow P hP
  have hcomm : ∀ x y : ↥P, ⁅x, y⁆ = 1 := by
    intro x y
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.1 (hP (Subgroup.le_normalizer x.2)) y.1 y.2).symm
  have hker : φ.ker = ⊤ := by
    apply top_le_iff.mp
    rw [← hperf, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact hcomm _ _
  have hcomp : φ.ker.IsComplement' (P : Subgroup H) :=
    MonoidHom.ker_transferSylow_isComplement' P hP
  rw [hker] at hcomp
  exact Subgroup.isComplement'_top_left.mp hcomp

theorem exists_commutator_ne_one_of_perfect {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hperf : ⁅K, K⁆ = K) {r : ℕ} [Fact r.Prime] (hr : r ∣ Nat.card K) :
    ∃ P : Subgroup G, P ≤ K ∧ IsPGroup r P ∧
      ∃ g ∈ K ⊓ Subgroup.normalizer (P : Set G), ∃ x ∈ P, g * x * g⁻¹ * x⁻¹ ≠ 1 := by
  classical
  have hperf' : commutator ↥K = ⊤ := by
    apply (Subgroup.map_subtype_inj (H := K)).mp
    rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_subtype_commutator, hperf]
  let P' : Sylow r ↥K := Classical.choice Sylow.nonempty
  have hP'ne : (P' : Subgroup ↥K) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P' hr
  by_contra hno
  push Not at hno
  have hNC : Subgroup.normalizer (P' : Subgroup ↥K) ≤
      Subgroup.centralizer (P' : Set ↥K) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hPg : ((P' : Subgroup ↥K).map K.subtype) ≤ K := Subgroup.map_subtype_le _
    have hPgrp : IsPGroup r ((P' : Subgroup ↥K).map K.subtype) := P'.isPGroup'.map K.subtype
    have hnN : (n : G) ∈ Subgroup.normalizer
        (((P' : Subgroup ↥K).map K.subtype) : Set G) :=
      Subgroup.le_normalizer_map (f := K.subtype)
        (Subgroup.mem_map_of_mem K.subtype hn)
    have hcommG : (n : G) * (x : G) * (n : G)⁻¹ * (x : G)⁻¹ = 1 :=
      hno ((P' : Subgroup ↥K).map K.subtype) hPg hPgrp (n : G) ⟨n.2, hnN⟩
        (x : G) (Subgroup.mem_map_of_mem K.subtype hx)
    have hcommK : ⁅n, x⁆ = 1 := by
      apply K.subtype_injective
      rw [map_commutatorElement]
      simpa [commutatorElement_def] using hcommG
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcommK).symm
  exact hP'ne (sylow_eq_bot_of_normalizer_le_centralizer_of_perfect hperf' P' hNC)

end CFSG.GroupTheory
