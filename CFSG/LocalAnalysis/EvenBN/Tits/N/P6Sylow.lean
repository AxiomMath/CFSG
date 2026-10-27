module

public import CFSG.Open.FusionDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open CFSG.ABGLocalTools

variable {G : Type*} [Group G]

theorem isSylowOf_of_fusionIsSylowIn [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (h : fusionIsSylowIn p P K) : IsSylowOf p P K := by
  obtain ⟨hPK, hPp, hmax⟩ := h
  obtain ⟨T, hT⟩ := (hPp.comap_of_injective K.subtype K.subtype_injective).exists_le_sylow
  exact ⟨T, hmax _ (Subgroup.map_subtype_le _) (T.isPGroup'.map K.subtype)
    fun x hx => ⟨⟨x, hPK hx⟩, hT hx, rfl⟩⟩

theorem fusionIsSylowIn_of_isSylowOf {p : ℕ} {P K : Subgroup G} (h : IsSylowOf p P K) :
    fusionIsSylowIn p P K := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, fun R hRK hR hQR => ?_⟩
  have hQR' : (Q : Subgroup K) ≤ R.subgroupOf K := fun x hx => hQR ⟨x, hx, rfl⟩
  rw [← Q.is_maximal' (hR.comap_of_injective K.subtype K.subtype_injective) hQR']
  exact ((Subgroup.subgroupOf_map_subtype R K).trans (inf_eq_left.mpr hRK)).symm

theorem fusionIsSylowIn_inf_of_normal [Finite G] {p : ℕ} [Fact p.Prime] {S H K : Subgroup G}
    (hS : fusionIsSylowIn p S H) (hKH : K ≤ H) (hnorm : H ≤ normalizer (K : Set G)) :
    fusionIsSylowIn p (S ⊓ K) K :=
  fusionIsSylowIn_of_isSylowOf
    (IsSylowOf.inf_of_le_normalizer (isSylowOf_of_fusionIsSylowIn hS) hKH hnorm)

theorem relIndex_inf_eq_two [Finite G] {S H K : Subgroup G} (hS : fusionIsSylowIn 2 S H)
    (hKH : K ≤ H) (hnorm : H ≤ normalizer (K : Set G))
    (hidx : K.relIndex H = 2 ∨ K.relIndex H = 6) : (S ⊓ K).relIndex S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (isSylowOf_of_fusionIsSylowIn hS).card_eq
  have h2 := (IsSylowOf.inf_of_le_normalizer (isSylowOf_of_fusionIsSylowIn hS) hKH hnorm).card_eq
  have h3 : K.relIndex H * Nat.card K = Nat.card H := by
    have h := Subgroup.relIndex_mul_card K H
    rwa [inf_eq_left.mpr hKH] at h
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hr : K.relIndex H ≠ 0 := by rcases hidx with h | h <;> rw [h] <;> norm_num
  have hr1 : (K.relIndex H).factorization 2 = 1 := by
    rcases hidx with h | h <;> rw [h]
    · exact Nat.Prime.factorization_self Nat.prime_two
    · have h6 : (6 : ℕ) = 2 * 3 := by norm_num
      rw [h6, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), add_zero]
  have hv : (Nat.card H).factorization 2 = (Nat.card K).factorization 2 + 1 := by
    rw [← h3, Nat.factorization_mul hr hKpos.ne', Finsupp.add_apply, hr1, add_comm]
  have h4 : Nat.card S = 2 * Nat.card (S ⊓ K : Subgroup G) := by
    rw [h1, h2, hv, pow_succ, mul_comm]
  have h5 := Subgroup.relIndex_mul_card (S ⊓ K) S
  rw [inf_eq_left.mpr (inf_le_left : S ⊓ K ≤ S)] at h5
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h5.trans h4)

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6
