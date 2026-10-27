module

public import CFSG.GF2Type.CenterFour.CaseBBasic
public import CFSG.GF2Type.CenterFour.BasicFusion
public import CFSG.GF2Type.CenterFour.CaseDefs

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

private theorem fused_mul_z_of_centralizer (hC : Config z n) {w : G} (hw : Fused z w)
    (hwC : w ∈ centralizer ({z} : Set G)) (hne : w ≠ z) : Fused z (w * z) := by
  obtain ⟨h, rfl⟩ := hw
  obtain ⟨g', hg'⟩ := hC.exists_conj_eq_mul_z hwC hne
  exact ⟨g', hg'⟩

private theorem mem_core_of_fused_centralizes {z₁ : G} (hC1 : Config z₁ n) {w : G}
    (hw : Fused z₁ w) (hwK : w ∈ centralizer (centerAt z₁ : Set G)) : w ∈ coreAt z₁ := by
  obtain ⟨k, rfl⟩ := hw
  exact hC1.mem_core_of_centralizes k hwK

theorem CaseB.fused_of_fused_mul (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {j : G}
    (hj : j ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) (hj1 : j ≠ 1)
    (hfj : Fused z (g⁻¹ * z * g * j)) : Fused z j := by
  by_cases hjz : j = z
  · rw [hjz]
    exact Fused.refl z
  have hC1 : Config (g⁻¹ * z * g) n := hC.conj g
  have hzQ : g⁻¹ * z * g ∉ coreAt z := CaseB.not_mem_core hC hK
  have hzK : z ∉ centralizer (centerAt (g⁻¹ * z * g) : Set G) :=
    CaseB.not_mem_centralizer_center hC hH hK
  have hjQ : j ∈ coreAt z := (Subgroup.mem_inf.mp hj).1
  have hjH : j ∈ centralizer ({g⁻¹ * z * g} : Set G) := (Subgroup.mem_inf.mp hj).2
  have hzH : z ∈ centralizer ({g⁻¹ * z * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hH).symm
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hC.orderOf_eq, sq] at h
  have hz1sq : (g⁻¹ * z * g) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (g⁻¹ * z * g)
    rwa [hC1.orderOf_eq] at h
  have hne : g⁻¹ * z * g * j ≠ z := by
    intro h
    apply hzQ
    have e : g⁻¹ * z * g = z * j⁻¹ := by
      calc g⁻¹ * z * g = g⁻¹ * z * g * j * j⁻¹ := by group
        _ = z * j⁻¹ := by rw [h]
    rw [e]
    exact mul_mem hC.mem_core (inv_mem hjQ)
  obtain ⟨j', hj'K, hj'eq⟩ : ∃ j' : G,
      j' ∈ centralizer (centerAt (g⁻¹ * z * g) : Set G) ∧ (j' = j ∨ j' = j * z) := by
    by_cases hjK : j ∈ centralizer (centerAt (g⁻¹ * z * g) : Set G)
    · exact ⟨j, hjK, Or.inl rfl⟩
    · exact ⟨j * z, hC1.mul_mem_centralizer hjH hzH hjK hzK, Or.inr rfl⟩
  have hj'Q : j' ∈ coreAt z := by
    rcases hj'eq with h | h
    · rw [h]
      exact hjQ
    · rw [h]
      exact mul_mem hjQ hC.mem_core
  have hj'C : j' ∈ centralizer ({g⁻¹ * z * g} : Set G) := by
    rcases hj'eq with h | h
    · rw [h]
      exact hjH
    · rw [h]
      exact mul_mem hjH hzH
  have hj'1 : j' ≠ 1 := by
    rcases hj'eq with h | h
    · rw [h]
      exact hj1
    · intro h1
      apply hjz
      have hjz1 : j * z = 1 := by
        rw [← h]
        exact h1
      calc j = j * z * z := by rw [mul_assoc, hz2, mul_one]
        _ = 1 * z := by rw [hjz1]
        _ = z := one_mul z
  have hj'z : j' ≠ z := by
    intro h'
    apply hzK
    rw [h'] at hj'K
    exact hj'K
  have hj'R : j' ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hj'Q, hj'C⟩
  have hj'2 : j' ^ 2 = 1 := (CaseB.isElemAbelian hC hH hK).2 j' hj'R
  have hcomm : Commute (g⁻¹ * z * g) j' :=
    (Subgroup.mem_centralizer_singleton_iff.1 hj'C).symm
  have ha2 : (g⁻¹ * z * g * j') ^ 2 = 1 := by
    rw [hcomm.mul_pow, hz1sq, hj'2, one_mul]
  have ha1 : g⁻¹ * z * g * j' ≠ 1 := by
    intro h
    apply hzQ
    have e : g⁻¹ * z * g = j'⁻¹ := by
      calc g⁻¹ * z * g = g⁻¹ * z * g * j' * j'⁻¹ := by group
        _ = j'⁻¹ := by rw [h, one_mul]
    rw [e]
    exact inv_mem hj'Q
  have haZ : g⁻¹ * z * g * j' ∉ centerAt (g⁻¹ * z * g) := by
    intro hmem
    have h2 : orderOf (g⁻¹ * z * g * j') = 2 := orderOf_eq_prime ha2 ha1
    have heq := hC1.eq_of_mem_center hmem h2
    apply hj'1
    calc j' = (g⁻¹ * z * g)⁻¹ * (g⁻¹ * z * g * j') := by group
      _ = (g⁻¹ * z * g)⁻¹ * (g⁻¹ * z * g) := by rw [heq]
      _ = 1 := by group
  have hfj' : Fused z (g⁻¹ * z * g * j') := by
    rcases hj'eq with h | h
    · rw [h]
      exact hfj
    · rw [h, ← mul_assoc]
      exact fused_mul_z_of_centralizer hC hfj (mul_mem hH (hC.core_le_centralizer hjQ)) hne
  have hW : g⁻¹ * z * g * j' ∈ coreAt (g⁻¹ * z * g) :=
    mem_core_of_fused_centralizes hC1 ((Fused.conj_iff (g := g)).mpr hfj')
      (mul_mem (hC1.core_le_centralizer_center hC1.mem_core) hj'K)
  obtain ⟨q, -, hq⟩ := hC1.exists_conj_eq_mul hW ha2 haZ
  have key : g⁻¹ * z * g * j' * (g⁻¹ * z * g) = j' := by
    calc g⁻¹ * z * g * j' * (g⁻¹ * z * g)
        = j' * (g⁻¹ * z * g * (g⁻¹ * z * g)) := by rw [hcomm.eq]; group
      _ = j' := by rw [← sq, hz1sq, mul_one]
  have hfz1 : Fused (g⁻¹ * z * g * j') j' := ⟨q, hq.trans key⟩
  have hfj'' : Fused z j' := hfj'.trans hfz1
  rcases hj'eq with h | h
  · rw [h] at hfj''
    exact hfj''
  · have hjj : j = j' * z := by
      rw [h, mul_assoc, hz2, mul_one]
    rw [hjj]
    exact fused_mul_z_of_centralizer hC hfj'' (hC.core_le_centralizer hj'Q) hj'z

end CFSG.GF2Type.CenterFour
