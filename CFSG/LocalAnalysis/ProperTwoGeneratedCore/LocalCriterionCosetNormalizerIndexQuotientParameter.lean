module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexRecognitionParameter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOddInvolutions

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII

universe u v

theorem identity_adjoined_whole_involution_card
    {L : Type u} [Group L] [Finite L] (P : Subgroup L) :
    Nat.card ↥(({1} : Set L) ∪ {x : L | x ∈ P ∧ IsInvolution x}) =
      Nat.card {x : L // x ∈ P ∧ IsInvolution x} + 1 := by
  classical
  let I : Set L := {x : L | x ∈ P ∧ IsInvolution x}
  have hone : (1 : L) ∉ I := by
    intro h
    exact h.2.ne_one rfl
  change Nat.card ↥(({1} : Set L) ∪ I) = Nat.card I + 1
  rw [Set.singleton_union, Nat.card_congr (Equiv.Set.insert hone), Nat.card_sum]
  rw [Nat.card_unique (α := PUnit.{u + 1})]

theorem central_odd_borel_preimage_exact_parameter
    {L : Type u} {F : Type v} [Group L] [Group F] [Finite L] [Finite F]
    (f : L →* F) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) (hcentral : f.ker ≤ Subgroup.center L)
    (hmodel : IsSimpleBenderGroup F) (B : Subgroup F) (hB : IsBorelSubgroup B) :
    ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
      B.index = (2 ^ a) ^ i + 1 ∧
      (B.comap f).index = (2 ^ a) ^ i + 1 ∧
      Nat.card {x : L // x ∈ B.comap f ∧ IsInvolution x} = 2 ^ a - 1 ∧
      Nat.card ↥(({1} : Set L) ∪ {x : L | x ∈ B.comap f ∧ IsInvolution x}) = 2 ^ a := by
  obtain ⟨a, i, ha, hi, hparameter⟩ := simpleBender_borel_exact_whole_parameter hmodel
  obtain ⟨hindex, hcount⟩ := hparameter B hB
  have hprecount : Nat.card {x : L // x ∈ B.comap f ∧ IsInvolution x} = 2 ^ a - 1 :=
    (whole_involution_card_comap_of_central_odd_kernel f hf hodd hcentral B).trans hcount
  refine ⟨a, i, ha, hi, hindex, ?_, hprecount, ?_⟩
  · exact (Subgroup.index_comap_of_surjective B hf).trans hindex
  · rw [identity_adjoined_whole_involution_card, hprecount]
    have hpositive : 0 < 2 ^ a := pow_pos (by decide) a
    omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
