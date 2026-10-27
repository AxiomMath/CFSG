
module

public import CFSG.LieType.Multipliers.L34
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem cyclic_four {K : Type*} [Group K] [IsCyclic K] [Finite K] (hK : Nat.card K = 4) :
    ∃ g : K, g * g ≠ 1 ∧ ∀ x : K, (x * x = 1 ↔ x = 1 ∨ x = g * g) ∧
      (x * x = 1 ∨ x * x = g * g) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  have ho : orderOf g = 4 := by
    rw [← hK]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have h4 : g ^ 4 = 1 := by rw [← ho]; exact pow_orderOf_eq_one g
  have hg2 : g * g ≠ 1 := fun h => by
    have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [ho] at this
    exact absurd this (by norm_num)
  have hg1 : g ≠ 1 := fun h => hg2 (by rw [h, mul_one])
  have hg3 : g ^ 3 ≠ 1 := fun h => hg1 (by
    calc g = g ^ 4 * (g ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, h]; group)
  have hg33 : g ^ 3 ≠ g * g := fun h => hg1 (by
    calc g = g ^ 3 * (g * g)⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  refine ⟨g, hg2, fun x => ?_⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (hg x)
  have hmod := zpow_mod_orderOf g k
  rw [ho] at hmod
  push_cast at hmod
  have hk0 : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
  have hk4 : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
  have hkm : g ^ k = g ^ (k % 4).toNat := by
    rw [← hmod, ← zpow_natCast, Int.toNat_of_nonneg hk0]
  rw [hkm]
  have hm4 : (k % 4).toNat < 4 := by omega
  generalize (k % 4).toNat = m at hm4
  interval_cases m
  · simp
  · rw [pow_one]
    refine ⟨⟨fun h => absurd h hg2, fun h => h.elim (fun h1 => absurd h1 hg1) fun h1 => ?_⟩,
      Or.inr rfl⟩
    exact absurd (mul_left_cancel (a := g) (by rw [mul_one]; exact h1)).symm hg1
  · have e : g ^ 2 * g ^ 2 = 1 := by rw [← pow_add]; exact h4
    exact ⟨⟨fun _ => Or.inr (pow_two g), fun _ => e⟩, Or.inl e⟩
  · have e : g ^ 3 * g ^ 3 = g * g := by
      rw [← pow_add, show 3 + 3 = 4 + 2 from rfl, pow_add, h4, one_mul, pow_two]
    exact ⟨⟨fun h => absurd (e ▸ h) hg2,
      fun h => h.elim (fun h1 => absurd h1 hg3) fun h1 => absurd h1 hg33⟩, Or.inr e⟩

theorem sq_comm_eq_one {E : Type*} [Group E] {x y : E}
    (hd : x⁻¹ * y⁻¹ * x * y ∈ center E) (hx2 : x * x ∈ center E) :
    (x⁻¹ * y⁻¹ * x * y) * (x⁻¹ * y⁻¹ * x * y) = 1 := by
  have hdc := mem_center_iff.mp hd
  have hxc := mem_center_iff.mp hx2
  generalize hdd : x⁻¹ * y⁻¹ * x * y = d at hdc ⊢
  have h1 : y⁻¹ * x * y = x * d := by rw [← hdd]; group
  have h2 : y⁻¹ * (x * x) * y = x * x * (d * d) := by
    calc y⁻¹ * (x * x) * y = (y⁻¹ * x * y) * (y⁻¹ * x * y) := by group
      _ = x * d * (x * d) := by rw [h1]
      _ = x * (d * x) * d := by group
      _ = x * (x * d) * d := by rw [hdc x]
      _ = x * x * (d * d) := by group
  have h3 : y⁻¹ * (x * x) * y = x * x := by
    rw [mul_assoc, ← hxc y]
    group
  rw [h3] at h2
  exact (mul_eq_left.mp h2.symm)

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

private theorem sqData_U : ∀ k ∈ 0 :: sqData.map (·.1), k < 16 ∨ (k % 4 = 0 ∧ k < 64) := by
  decide

private theorem U1_idx : ∀ k < 16, k ∈ 0 :: sqData.map (·.1) := by decide

private theorem U2_idx : ∀ k < 16, 4 * k ∈ 0 :: sqData.map (·.1) := by decide

theorem comm_of_mul_self {X : Type*} [Group X] {s t : X} (hs : s * s = 1) (ht : t * t = 1)
    (hst : s * t * (s * t) = 1) : s * t = t * s := by
  calc s * t = (s * t)⁻¹ := (inv_eq_of_mul_eq_one_right hst).symm
    _ = t⁻¹ * s⁻¹ := mul_inv_rev s t
    _ = t * s := by rw [inv_eq_of_mul_eq_one_right hs, inv_eq_of_mul_eq_one_right ht]

end CFSG.ComponentClassification.GrSLit.L34Facts
