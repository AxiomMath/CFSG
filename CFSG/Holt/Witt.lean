module

public import CFSG.Holt.Basic

public section

namespace CFSG.Holt

open MulAction CFSG.Open

variable {X : Type*} [Group X]

section Sylow

variable [Finite X] {p : ℕ} [Fact p.Prime]

theorem card_eq_of_fusionIsSylowIn {P K : Subgroup X} (hP : fusionIsSylowIn p P K) :
    Nat.card P = p ^ (Nat.card K).factorization p := by
  obtain ⟨T, hT⟩ := exists_sylow_map_eq_of_fusionIsSylowIn hP
  rw [← hT, Subgroup.card_map_of_injective K.subtype_injective]
  exact T.card_eq_multiplicity

theorem fusionIsSylowIn_of_card_eq {P K : Subgroup X} (hPK : P ≤ K) (hP : IsPGroup p P)
    (hcard : Nat.card P = p ^ (Nat.card K).factorization p) : fusionIsSylowIn p P K := by
  refine ⟨hPK, hP, fun Q hQK hQ hPQ => ?_⟩
  obtain ⟨R, hQR, hR⟩ := exists_fusionIsSylowIn_ge hQ hQK
  have hPR : P = R := Subgroup.eq_of_le_of_card_ge (hPQ.trans hQR)
    (by rw [card_eq_of_fusionIsSylowIn hR, hcard])
  exact le_antisymm (hQR.trans hPR.ge) hPQ

theorem exists_mem_conj_of_fusionIsSylowIn {P Q K : Subgroup X} (hP : fusionIsSylowIn p P K)
    (hQ : fusionIsSylowIn p Q K) : ∃ k ∈ K, ∀ x : X, x ∈ Q ↔ k⁻¹ * x * k ∈ P := by
  obtain ⟨SP, hSP⟩ := exists_sylow_map_eq_of_fusionIsSylowIn hP
  obtain ⟨SQ, hSQ⟩ := exists_sylow_map_eq_of_fusionIsSylowIn hQ
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K SP SQ
  refine ⟨k, k.2, fun x => ?_⟩
  rw [← hSP, ← hSQ, ← hk]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k⁻¹ * y * k, mem_smul_sylow_iff.mp hy, by simp⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨k * y * k⁻¹, mem_smul_sylow_iff.mpr ?_, ?_⟩
    · rw [show k⁻¹ * (k * y * k⁻¹) * k = y by group]
      exact hy
    · rw [map_mul, map_mul, hyx, map_inv, Subgroup.coe_subtype]
      group

end Sylow

end CFSG.Holt
