module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFOdd
public import CFSG.ClassicalInvolution.Q3.TL4OddZT
public import CFSG.ClassicalInvolution.Q3.TL4D4NC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance

@[expose] def D4OuterAutOddFree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → LieModel S .POmegaPlus 4 3 1 →
    Q3NM.AutOddFreeOn S (fun f => f ∉ Q3NM.innSubgroup S)


theorem autOddFreeInner_d4 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : LieModel S .POmegaPlus 4 3 1) : Q3NM.AutOddFreeInner S := by
  have hFT : IsFundTag StatedLieTag.POmegaPlus := trivial
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover _ 4 3 1 Nat.prime_three (by norm_num) hFT hadm S hS
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := center_eq_bot_of_isQuasisimple hSq
  have h := Q3NM.autOddFreeInnerOn_of_centralizing_inner (X := S) (fun _ => True) hZ
    (fun x _ hx => oddCentralizerFreeTag_POmegaPlus 4 Nat.prime_three hFT hadm S ψ hψ hker x hx)
    (fun s _ hs α hα hfix => by
      obtain ⟨g, hg⟩ := d4OddAutInner3_all S hSq hZ ψ hψ hker s hs α hα fun c hc => by
        rw [hfix c hc, inv_mul_cancel]
        exact one_mem _
      exact ⟨g, hg.symm⟩)
  rintro 𝒳 hinn f ⟨s, hs⟩ hf
  exact h 𝒳 hinn f s hs trivial hf

theorem autOddFree_d4 (hD : D4OuterAutOddFree) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : LieModel S .POmegaPlus 4 3 1) : Q3NM.AutOddFree S := by
  have h := ((autOddFreeInner_d4 hS).toOn).or (hD S inferInstance hS)
  intro 𝒳 hinn f hf
  exact h 𝒳 hinn f (em _) hf

theorem omegaAutOddFreeR_of_outer (hSp : OuterFixedOddFree .PSp 2)
    (hL : OuterFixedOddFree .PSL 4) (hU : OuterFixedOddFree .PSU 4)
    (hP : ∀ k, 5 ≤ k → OuterFixedOddFree .POmegaPlus k)
    (hM : ∀ k, 4 ≤ k → OuterFixedOddFree .POmegaMinus k) (hD : D4OuterAutOddFree) :
    OmegaAutOddFreeR := by
  intro M _ _ hC
  have hs := isSimpleGroup_of_centOmega3 hC
  rcases hC with h | h | h | ⟨k, hk, h⟩ | ⟨k, hk, h⟩ | ⟨k, hk, h⟩
  · exact autOddFree_of_outer (t := .PSp) (n := 2) (fun h => by cases h.1) (by decide) trivial
      (by decide) h (hSp _ hs h)
  · exact autOddFree_of_outer (t := .PSL) (n := 4) (fun h => by cases h.1) (by decide) trivial
      (by decide) h (hL _ hs h)
  · exact autOddFree_of_outer (t := .PSU) (n := 4) (fun h => by cases h.1) (by decide) trivial
      (by decide) h (hU _ hs h)
  · exact autOddFree_of_outer (t := .POmegaOdd) (n := k) (fun h => by cases h.1) (by decide)
      trivial (by decide) h (outerFixedOddFree_pOmegaOdd _ hs h)
  · by_cases hk4 : k = 4
    · subst hk4
      exact autOddFree_d4 hD h
    · exact autOddFree_of_outer (t := .POmegaPlus) (n := k) (fun h => hk4 h.2) (by decide)
        trivial (by decide) h (hP k (by omega) _ hs h)
  · exact autOddFree_of_outer (t := .POmegaMinus) (n := k) (fun h => by cases h.1) (by decide)
      trivial (by decide) h (hM k hk _ hs h)

end CFSG.ClassicalInvolution.Q3.TL4
