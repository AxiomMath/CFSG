module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Normal
public import CFSG.HardMathSupport.Foote.Coordinator.CoverThree.Order
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharNoInner

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts (psuConj)

open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels) in
theorem p1OffCharCoverThreeNoInner_of_cases (hGA : GriessMultipliersAllModels)
    (hDL : CoverThreeNoInnerDiagLinear) (hFL : CoverThreeNoInnerFieldLinear)
    (hDU : CoverThreeNoInnerDiagUnitary) (hFU : CoverThreeNoInnerFieldUnitary) :
    P1OffCharCoverThreeNoInner := by
  intro Y _ _ Rb Y₀ h hcat K hK huniq hnc hcent d hd he₀ hchar hz hno
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hKq : Open.IsQuasisimple K := hK.2.2
  have hC := centralizer_le_sylow_of_cover_three h hKn hcent
  have hZ3 := CFSG.HardMathSupport.Foote.Coordinator.coverThree_center_three hGA hKq d hd he₀ hz
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hER, hEa, hEc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 3) h.three_le_pRank
  have hEout := not_le_sup_centralizer_of_no_inner h hKn hcent hno hER hEa hEc
  obtain ⟨e₀⟩ := he₀
  rcases hd with ⟨q, hq, h3⟩ | ⟨q, hq, h3⟩
  ·
    obtain ⟨dd, hv⟩ := d
    simp only at hq
    subst hq
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    let e : K ⧸ Subgroup.center K ≃* projectiveSL 3 (GaloisField q.p q.exponent) :=
      e₀.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _))
    have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
    have h3F : 3 ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by rw [hcardF]; exact h3
    exfalso
    have hEN : E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore := by
      have := sup_sylow_normal_linear hKq e Rb hC
      rw [Subgroup.normalCore_eq_self]
      exact hER.trans le_sup_right
    by_cases hlin : E.map (modelAct K e) ≤ linearAutGroup 3 (GaloisField q.p q.exponent)
    · exact hDL Y Rb Y₀ h K hKq hC hcent hZ3 _ h3F e E hER hEN hEa hEc hEout hlin
    · exact hFL Y Rb Y₀ h K hKq hC hcent hZ3 _ h3F e E hER hEN hEa hEc hEout hlin
  ·
    obtain ⟨dd, hv⟩ := d
    simp only at hq
    subst hq
    by_cases h8 : q.p = 2 ∧ q.exponent = 3
    ·
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨rfl, q, h8.1, h8.2, Or.inr (Or.inr (Or.inr rfl))⟩)))))
    · exfalso
      obtain ⟨⟨hℓ, hf, -, hne⟩, F, _, _, hFc, ⟨e₁⟩⟩ :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv
          (MulEquiv.refl (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩))
      have hU : UnitaryFieldData q.p q.exponent F :=
        ⟨hℓ, hf, by rw [hFc, ← pow_mul, mul_comm]⟩
      have hq2 : 2 < q.p ^ q.exponent := by
        have h1 : 2 ≤ q.p ^ q.exponent :=
          (hℓ.two_le).trans (Nat.le_self_pow (Nat.pos_iff_ne_zero.1 q.exponent_pos) _)
        refine lt_of_le_of_ne h1 fun h2 => hne ?_
        rw [← h2]
      have h3q : 3 ∣ q.p ^ q.exponent + 1 := by rw [← TauCeti.PrimePower.card_def]; exact h3
      have h8' : q.p ^ q.exponent ≠ 8 := by
        intro h8e
        apply h8
        have hp2 : q.p = 2 := by
          have hd : q.p ∣ 2 ^ 3 := by
            rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h8e]
            exact dvd_pow_self _ q.exponent_pos.ne'
          exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow hd)
        refine ⟨hp2, ?_⟩
        rw [hp2] at h8e
        have h8'' : (2 : ℕ) ^ q.exponent = 2 ^ 3 := by rw [h8e]; norm_num
        exact Nat.pow_right_injective (le_refl 2) h8''
      let e : K ⧸ Subgroup.center K ≃* unitaryPSU hU 3 :=
        e₀.trans (e₁.trans (unitaryPSUEquiv hU (by norm_num)).symm)
      have hEN : E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore := by
        have := sup_sylow_normal_unitary hKq hU hq2 e Rb hC
        rw [Subgroup.normalCore_eq_self]
        exact hER.trans le_sup_right
      by_cases hlin : E.map (modelAct K e) ≤ (psuConj hU).range
      · exact hDU Y Rb Y₀ h K hKq hC hcent hZ3 q.p q.exponent F hU hq2 h3q h8' e E hER hEN hEa hEc
          hEout hlin
      · exact hFU Y Rb Y₀ h K hKq hC hcent hZ3 q.p q.exponent F hU hq2 h3q h8' e E hER hEN hEa hEc
          hEout hlin

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
