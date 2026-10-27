module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddLie
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34REven
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSimple
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSporMain
public import CFSG.Sporadic.Recognition.HeMultiplierCert

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf

@[expose] def L34ProperFixedCenterTrivial : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → IsPGroup 2 (center Q) →
    Blueprint.Catalog (Q ⧸ center Q) → ∀ σ : MulAut Q, (∀ y, σ (σ y) = y) →
    ∀ P : Subgroup Q, P ≤ FixedCommutingProduct.fixedSubgroup σ →
      IsPComponent 2 (P.subgroupOf (FixedCommutingProduct.fixedSubgroup σ)) → P ≠ ⊤ →
      IsL34Type (P ⧸ Open.fusionZStar P) → 2 ≤ pRank 2 ↥(Open.fusionZStar P) → center Q = ⊥

theorem l34RankTwoCentralFixedInput_of_centerTrivial (h : L34ProperFixedCenterTrivial) :
    L34RankTwoCentralFixedInput := by
  intro Q _ _ hQ hZ hcat σ hσ P hPF hP hPne htype hrank z _ hzZ hz1
  have h1 := h Q hQ hZ hcat σ hσ P hPF hP hPne htype hrank
  rw [h1] at hzZ
  exact hz1 (Subgroup.mem_bot.mp hzZ)

theorem l34ProperFixedCenterTrivial_of_inputs
    (hGA : TBLit.GriessMultipliersAllModels)
    (hCT : EvenSporadicStandard.CentralTwoBound)
    (hGLS : GLS3OddLieAutComponentsInput) (hR1 : EvenLieExcOuterL34Input)
    (hR2 : SuzDoubleCoverL34Input) : L34ProperFixedCenterTrivial := by
  intro Q _ _ hQ hZ hcat σ hσ P hPF hP hPne htype hrank
  by_contra hZ1
  have hO := CatLeafProof.lieOrderFormulasInput
  have : IsSimpleGroup (Q ⧸ center Q) := hQ.2.1
  have hna : ∃ a b : Q ⧸ center Q, a * b ≠ b * a := hQ.2.2
  obtain ⟨σ', P', h', htype'⟩ := L34R.exists_properFixedComponent hQ hZ hσ hPF hP hPne htype
  have hodd : OddLieType (Q ⧸ center Q) → False := fun ho =>
    (not_held_not_L34_of_properFixedComponent_oddLie hGLS hO hna ho h').2 htype'
  rcases (Milestones.ct_catalog_nonabelian_type_partition (Q ⧸ center Q) hna).mp hcat with
    ⟨n, hn, hA⟩ | ho | he | hsp
  · obtain ⟨θ⟩ := hA
    exact not_isL34Type_of_properFixedComponent_alternating hn θ h' htype'
  · exact hodd ho
  · rcases L34R.uList_of_evenLie hO hGA hR1 hQ hZ hZ1 he h' htype' with
      ho | ⟨n, -, h7, hA⟩ | hL | hH
    · exact hodd ho
    · obtain ⟨θ⟩ := hA
      exact not_isL34Type_of_properFixedComponent_alternating (by omega) θ h' htype'
    ·
      have hS := card_of_isL34Type hL
      have hPd : 20160 ∣ Nat.card P' := by
        rw [← card_of_isL34Type htype']
        exact Subgroup.card_quotient_dvd_card _
      exact h'.2.2.2 ((Subgroup.card_eq_iff_eq_top P').mp
        (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card P') (hS ▸ hPd)))
    ·
      exact hZ1 (Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate Q hQ hH)
  · exact L34R.false_of_sporadic hCT hR2 hQ hZ hZ1 hsp hσ hPF hP hPne htype hrank h' htype'

end CFSG.ComponentClassification.GrSLit
