module

public import CFSG.LieType.BorelTits.AllModels
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenG2Two
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.LieType.ChevTwo

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo IsChevIndexTwo)
open CFSG.LieType.BorelTits

theorem characteristic_two_of_isChevIndexTwo {i : TauCeti.LieTypeIndex} (h : IsChevIndexTwo i) :
    i.characteristic = 2 := by
  cases i <;> simp_all [IsChevIndexTwo]

theorem holdsTits_alternating_six : HoldsTits (alternatingGroup (Fin 6)) 2 := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  obtain ⟨e₃⟩ := CFSG.StandardType.nonempty_largeEvenSpGroup_equiv_sympFour hK
  obtain ⟨e₄⟩ := CFSG.StandardType.nonempty_commutator_equiv e₃
  obtain ⟨eA⟩ : Nonempty (commutator ↥(CFSG.Assembly.LargeEvenSpGroup (ZMod 2) 2) ≃* alternatingGroup (Fin 6)) :=
    ⟨e₄.trans CFSG.ComponentClassification.PresentationLocal.commutatorEquivAlternating⟩
  have hΓ : Holds ↥(CFSG.Assembly.LargeEvenSpGroup (ZMod 2) 2) 2 := holds_statedSp 2 (ZMod 2) 2
  have hcard : Nat.card ↥(CFSG.Assembly.LargeEvenSpGroup (ZMod 2) 2) = 720 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := ZMod 2) 2, hK]
    decide
  have hY : Nat.card ↥(commutator ↥(CFSG.Assembly.LargeEvenSpGroup (ZMod 2) 2)) = 360 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have hidx : (commutator ↥(CFSG.Assembly.LargeEvenSpGroup (ZMod 2) 2)).index = 2 := by
    have h := Subgroup.card_mul_index (commutator ↥(CFSG.Assembly.LargeEvenSpGroup (ZMod 2) 2))
    rw [hY, hcard] at h
    omega
  have hA : HoldsTits ↥(commutator ↥(CFSG.Assembly.LargeEvenSpGroup (ZMod 2) 2)) 2 := fun V hV hVp =>
    conclusion_of_normal_of_index_eq hidx hΓ V hV hVp
  exact HoldsTits.of_mulEquiv eA hA

section Certificates

theorem holdsTits_of_lieModel_two {X : Type} [Group X] {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (h : CFSG.Blueprint.LieModel X t n 2 f) : HoldsTits X 2 := by
  by_cases ht : t = .Tits
  · subst ht
    exact holdsTits_of_lieModel_tits h
  · exact (holds_of_lieModel h ht).holdsTits

theorem holdsTits_of_psu_three_three {S : Type} [Group S] [Finite S]
    (hS : CFSG.Open.StatedClassicalModel S .PSU 3 3 1) : HoldsTits S 2 := by
  have hΓ : Holds ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (ZMod 2)) 2 :=
    CFSG.LieType.Chevalley.holds_adjointGroup_tag .G2 (ZMod 2) 2
  have hΓcard : Nat.card ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (ZMod 2)) = 12096 :=
    CFSG.ComponentClassification.ExcSelector.card_adjointGroup_G2_two (Nat.card_zmod 2)
  have hL := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds (ZMod 2)
    (Nat.card_zmod 2)
  have hC : CFSG.Open.StatedClassicalModel
      ↥⁅CFSG.Blueprint.Chevalley.adjointGroup .G2 (ZMod 2),
        CFSG.Blueprint.Chevalley.adjointGroup .G2 (ZMod 2)⁆ .PSU 3 3 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hL (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨φ⟩ := CFSG.ClassicalInvolution.Upgrade.statedClassicalModel_unique
    (by norm_num : (3 : ℕ) ≠ 2) hS hC
  obtain ⟨ψ⟩ := CFSG.StandardType.nonempty_commutator_subgroup_equiv
    (CFSG.Blueprint.Chevalley.adjointGroup .G2 (ZMod 2))
  have hSord : Nat.card S = 6048 := by
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_three le_rfl hK
        (by norm_num)]
    decide
  have hYcard : Nat.card ↥(commutator ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (ZMod 2))) =
      6048 := by
    rw [← hSord]
    exact Nat.card_congr (ψ.symm.trans φ.symm).toEquiv
  have hidx : (commutator ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (ZMod 2))).index = 2 := by
    have h := Subgroup.card_mul_index
      (commutator ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (ZMod 2)))
    rw [hYcard, hΓcard] at h
    omega
  have hY : HoldsTits ↥(commutator ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (ZMod 2))) 2 :=
    fun V hV hVp => conclusion_of_normal_of_index_eq hidx hΓ V hV hVp
  exact HoldsTits.of_mulEquiv (ψ.symm.trans φ.symm) hY

theorem holdsTits_two_of_isChevTwo {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : IsChevTwo S) : HoldsTits S 2 := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨i, hv⟩, hi, ⟨e⟩⟩
  · obtain ⟨t, m, f, hL⟩ :=
      CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d
        (characteristic_two_of_isChevIndexTwo hd) e
    exact holdsTits_of_lieModel_two hL
  · rcases hn with rfl | rfl | rfl
    · exact holdsTits_of_lieModel_two
        (CFSG.StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five e)
    · exact HoldsTits.of_mulEquiv e.symm holdsTits_alternating_six
    · exact holdsTits_of_lieModel_two
        (CFSG.StandardType.ChevTwo.lieModel_psl_four_two_of_alternating_eight e)
  · obtain ⟨q, hq, hiq⟩ | ⟨q, hq, hiq⟩ := hi
    · simp only at hiq
      subst hiq
      exact holdsTits_of_lieModel_two
        (CFSG.StandardType.ChevTwo.lieModel_psl_three_two_of_A_one q hv hq e)
    · simp only at hiq
      subst hiq
      exact holdsTits_of_psu_three_three
        (CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two q hv hq e)

end Certificates

end CFSG.LieType.ChevTwo
