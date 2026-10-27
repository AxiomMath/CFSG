module

public import CFSG.LieType.AlgebraicGroups.G2ExceptionalBound

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {L : Type} [Field L] [IsAlgClosed L]

theorem finrank_tangentSpace_realizedCoord_le_posRoots (τ : Tag)
    (x : realizedCoord τ L →ₐ[L] L) :
    Module.finrank L (TangentSpace L (realizedCoord τ L) x) ≤
      τ.rank + 2 * {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
  have hreal := isConnectedAlgebraicSubgroup_adjointPointSubgroup τ L
  have := hreal.finiteType
  obtain ⟨N, α, hα, hαr⟩ := exists_enum (finite_posRoots τ)
  choose m β hβ hβr using fun w : WeylGroup τ => exists_enum (inversionSet_finite w)
  obtain ⟨-, -, hcov, -, -, -⟩ := exceptional_Lang_rootword_Bruhat_regular_cover τ L
  have hN : N = {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
    have h : (Set.range α).ncard = Nat.card (Fin N) := Set.ncard_range_of_injective hα
    rw [hαr, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    exact h.symm
  have hm : ∀ w : WeylGroup τ, m w ≤
      {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
    intro w
    have hle := Set.ncard_le_ncard
      (show inversionSet w ⊆ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α} from
        fun _ h => ⟨h.1, h.2.1⟩) (finite_posRoots τ)
    have hcard : (inversionSet w).ncard = m w := by
      have h : (inversionSet w).ncard = (Set.range (β w)).ncard := by rw [hβr w]
      rw [h, Set.ncard_range_of_injective (hβ w), Nat.card_eq_fintype_card,
        Fintype.card_fin]
    omega
  refine finrank_tangentSpace_quotient_le (subgroupPoints (adjointPointSubgroup τ L))
    hreal.pointsZero_eq (fun _ => τ.rank) (fun w => N + m w)
    (fun w => bruhatCo τ L w α (β w)) ?_ (fun w => ?_) x
  · rw [hcov α hα hαr m β hβ hβr, subgroupPoints_map, transportPoints_modGLPoint]
    rfl
  · have h1 := hN
    have h2 := hm w
    omega

theorem finrank_tangentSpace_realizedCoord_E7_le (x : realizedCoord Tag.E7 L →ₐ[L] L) :
    Module.finrank L (TangentSpace L (realizedCoord Tag.E7 L) x) ≤ 133 := by
  have h := finrank_tangentSpace_realizedCoord_le_posRoots (L := L) Tag.E7 x
  have h63 : {α : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 α ∧ 0 < height α}.ncard = 63 := by
    have hset : {α : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 α ∧ 0 < height α} =
        ((rootFinset Tag.E7).filter fun α => 0 < height α : Finset _) := by
      ext α
      simp [mem_rootFinset]
    rw [hset, Set.ncard_coe_finset]
    decide +kernel
  rw [h63] at h
  norm_num at h
  exact h

end CFSG.LieType.AlgebraicGroups

end
