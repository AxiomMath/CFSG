module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem sylow_relIndex_eq_of_primePower_index (K : Subgroup G)
    (hindex : ∃ e : ℕ, K.index = p ^ e) (S : Sylow p G) :
    K.relIndex (S : Subgroup G) = K.index := by
  obtain ⟨e, he⟩ := hindex
  have hcoprime : K.index.Coprime (S : Subgroup G).index := by
    rw [he]
    exact (Fact.out : p.Prime).coprime_pow_of_not_dvd S.not_dvd_index |>.symm
  have hmul : K.relIndex (S : Subgroup G) * (S : Subgroup G).index =
      (S : Subgroup G).relIndex K * K.index := by
    calc
      _ = (K ⊓ (S : Subgroup G)).index := by
        simpa using Subgroup.relIndex_inf_mul_relIndex K (S : Subgroup G) ⊤
      _ = ((S : Subgroup G) ⊓ K).index := by rw [inf_comm]
      _ = _ := by
        simpa using (Subgroup.relIndex_inf_mul_relIndex (S : Subgroup G) K ⊤).symm
  have hdvd : K.index ∣ K.relIndex (S : Subgroup G) :=
    hcoprime.dvd_of_dvd_mul_right (hmul ▸ dvd_mul_left K.index
      ((S : Subgroup G).relIndex K))
  have hle : K.relIndex (S : Subgroup G) ≤ K.index := by
    simpa using (Subgroup.relIndex_le_of_le_right (H := K)
      (K := (S : Subgroup G)) (L := ⊤) le_top
      (by simpa using K.index_ne_zero_of_finite))
  exact Nat.le_antisymm hle
    (Nat.le_of_dvd (Nat.pos_of_ne_zero
      (K.subgroupOf (S : Subgroup G)).index_ne_zero_of_finite) hdvd)

theorem sylow_intersection_relIndex_eq (N D : Subgroup G)
    (hindex : ∃ e : ℕ, D.relIndex N = p ^ e) (S : Sylow p N) :
    D.relIndex ((S : Subgroup N).map N.subtype) = D.relIndex N := by
  rw [← Subgroup.relIndex_comap]
  exact sylow_relIndex_eq_of_primePower_index (D.subgroupOf N) hindex S

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
