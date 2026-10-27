module

public import CFSG.HardMathSupport.Foote.Coordinator.CoverThree.Reduction
public import CFSG.HardMathSupport.Foote.Coordinator.CoverThree.Order
public import CFSG.HardMathSupport.Foote.Coordinator.CoverThree.Transfer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharClassicalCover

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem p1OffCharCoverThree_of (hGA : GriessMultipliersAllModels) (hS2 : ∀ d :
    TauCeti.ValidLieTypeIndex, CoverThreeIndex d → 3 ≠ d.1.characteristic → ∀ A : Subgroup
    (TauCeti.CFSGIndex.lie d).Group, CFSG.Open.IsElemAbelian 3 A → Nat.card A ≤ 9)
    (hS4 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ d :
        TauCeti.ValidLieTypeIndex, CoverThreeNine d → ¬ IsUThreeEight d → 3 ≠ d.1.characteristic →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) → (Nat.card
        (Subgroup.center K)).factorization 3 = 1 → ∀ P : Subgroup K, IsMulCommutative P → Nat.card P
        = 3 ^ 3 → Nat.card (P ⊓ Subgroup.center K : Subgroup K) = 3 → (∀ x ∈ P, x ^ 3 ∈
        Subgroup.center K) → ∀ k : K, k ∈ Subgroup.closure {k : K | ∃ x ∈ P, x ∉ Subgroup.center K ∧
        k * x = x * k}) : P1OffCharCoverThree := by
  intro Y _ _ Rb Y₀ h hcat K hK huniq hnc hcent d hd e hchar hz hex
  by_cases hU : IsUThreeEight d
  · obtain ⟨q, hq2, hq3, hdq⟩ := hU
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, q, hq2, hq3, Or.inr (Or.inr (Or.inr hdq))⟩)))))
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨E, hER, hEN, hEa, hEc, hEKC⟩ := hex
    have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
    have hKq : Open.IsQuasisimple K := hK.2.2
    obtain ⟨e'⟩ := e
    have hZ3 := coverThree_center_three hGA hKq d hd ⟨e'⟩ hz
    have hm3 : ∀ A : Subgroup (K ⧸ Subgroup.center K), IsElemAbelian 3 A → Nat.card A ≤ 9 := by
      intro A hA
      have := hS2 d hd hchar (A.map e'.toMonoidHom)
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hA e'.toMonoidHom)
      rwa [Subgroup.card_map_of_injective e'.injective] at this
    obtain ⟨P, hPc, hP27, hPZ, hP3, hPF⟩ :=
      coverThree_reduction Rb hKn hZ3 hm3 hcent hEa hEc hEKC
    by_cases h9 : CoverThreeNine d
    · have hcl := hS4 K hKq d h9 hU hchar ⟨e'⟩ hZ3 P hPc hP27 hPZ hP3
      have hgen : HyperGen 3 K E := by
        intro k hk
        have hk' := hcl ⟨k, hk⟩
        have hle : Subgroup.closure
            {k : K | ∃ x ∈ P, x ∉ Subgroup.center K ∧ k * x = x * k} ≤
            (Subgroup.closure {k : Y | k ∈ K ∧ ∃ F : Subgroup Y, F ≤ E ∧ F.relIndex E = 3 ∧
              ∀ f ∈ F, f * k = k * f}).comap K.subtype := by
          refine (Subgroup.closure_le _).2 fun s ⟨x, hxP, hxZ, hsx⟩ => ?_
          obtain ⟨F, hFE, hFi, hF⟩ := hPF x hxP hxZ
          exact Subgroup.subset_closure ⟨s.2, F, hFE, hFi, hF s hsx⟩
        exact hle hk'
      exact h.false_of_hyperGen hEa hEc hER hEN hgen
    · have hcard := coverThree_card_three_part hGA hKq d hd h9 ⟨e'⟩ hz
      let Ps : Sylow 3 K := Sylow.ofCard P (by rw [hP27, hcard])
      have hnt : ∃ z ∈ (P ⊓ Subgroup.center K : Subgroup K), z ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : (P ⊓ Subgroup.center K : Subgroup K) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
        rw [this] at hPZ
        simp at hPZ
      obtain ⟨z, ⟨hzP, hzZ⟩, hz1⟩ := hnt
      have hzK : z ∈ commutator K := by
        rw [hKq.1]
        exact Subgroup.mem_top z
      exact hz1 (eq_one_of_mem_center_commutator_of_abelian_sylow Ps hPc hzP hzZ hzK)

end CFSG.HardMathSupport.Foote.Coordinator
