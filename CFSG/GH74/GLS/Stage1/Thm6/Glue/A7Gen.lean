module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue.A7

open Subgroup

section Sylow

variable {H : Type*} [Group H]

theorem relIndex_dvd_index_of_normal' [Finite H] (S K : Subgroup H) [K.Normal] :
    S.relIndex K ∣ S.index := by
  have h1 : S.relIndex K * K.index = (S ⊓ K).index := by
    have h := Subgroup.relIndex_inf_mul_relIndex S K ⊤
    rwa [inf_top_eq, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h
  have h2 : (S ⊓ K).relIndex S * S.index = (S ⊓ K).index :=
    Subgroup.relIndex_mul_index inf_le_left
  have h3 : (S ⊓ K).relIndex S = K.relIndex (S ⊔ K) := by
    rw [Subgroup.relIndex_sup_right, inf_comm, Subgroup.inf_relIndex_right]
  obtain ⟨m, hm⟩ := Subgroup.relIndex_dvd_index_of_le (le_sup_right : K ≤ S ⊔ K)
  have hpos : 0 < K.relIndex (S ⊔ K) := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, zero_mul] at hm
    exact Subgroup.index_ne_zero_of_finite hm
  refine ⟨m, ?_⟩
  rw [hm, ← h2, h3] at h1
  have h4 : K.relIndex (S ⊔ K) * (S.relIndex K * m) = K.relIndex (S ⊔ K) * S.index := by
    rw [← h1]
    ring
  exact (Nat.eq_of_mul_eq_mul_left hpos h4).symm

theorem exists_sylow_subgroupOf [Finite H] {p : ℕ} [Fact p.Prime] (S : Sylow p H) (K : Subgroup H)
    [K.Normal] : ∃ Q : Sylow p ↥K, (Q : Subgroup ↥K) = (S : Subgroup H).subgroupOf K := by
  have hS : IsPGroup p ↥((S : Subgroup H).subgroupOf K) := S.isPGroup'.comap_subtype
  have hidx : ¬ p ∣ ((S : Subgroup H).subgroupOf K).index := by
    intro hd
    have h2 : p ∣ (S : Subgroup H).relIndex K := hd
    exact S.not_dvd_index (h2.trans (relIndex_dvd_index_of_normal' _ _))
  exact ⟨hS.toSylow hidx, rfl⟩

end Sylow

theorem card_sylow_two_of_card_A7 {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = Nat.card (alternatingGroup (Fin 7))) (Q : Sylow 2 K) :
    Nat.card (Q : Subgroup K) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2520 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  rw [Sylow.card_eq_multiplicity, hK, h2520,
    show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]

end CFSG.GH74.GLS.Stage1.Thm6.Glue.A7
