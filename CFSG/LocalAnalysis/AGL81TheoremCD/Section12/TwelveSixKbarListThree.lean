module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarListInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarListThreeInner
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveCore
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveTransport
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeCoverRank
import CFSG.LieType.Simplicity.Basic
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedPSLTwoNine

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic Subgroup
open CFSG.LocalAnalysis.AGL81I.Section3 (KGroupLowRank24_12)

theorem kFactKbarListThree_holds
    : KFactKbarListThree := by
  intro K _ _ hK hrK S _ _ ⟨e⟩ Y V W₁ W₂ W₃ t₁ t₂ t₃ hInn hY3 hcfg hVY ht₁ ht₂ ht₃
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hq, -, hmem⟩ := hK
  have hZS : center S = ⊥ := KbarListThree.center_eq_bot_of_quasisimple hq e
  have hV := hcfg.elem
  have hc := hcfg.card
  have hVd : V ≤ commutator (MulAut S) :=
    (hcfg.le_commutator hVY ht₁ ht₂ ht₃).trans (Subgroup.commutator_mono le_top le_top)
  have hKS : IsSimpleGroup K → K ≃* S := fun h => KbarListFive.equiv_of_centerQuotient hq e
  have hst : ∀ {t : StatedLieTag} {n p f : ℕ}, StatedClassicalModel K t n p f →
      StatedClassicalModel S t n p f := fun h =>
    Open.StatedAPI.statedClassicalModel_of_mulEquiv
      (hKS (Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h)) h
  have halt : ∀ {n : ℕ}, 5 ≤ n → (K ≃* alternatingGroup (Fin n)) →
      Nonempty (S ≃* alternatingGroup (Fin n)) := fun hn a =>
    ⟨(hKS (CFSG.LieType.Simplicity.fam_alternating_converse K ⟨_, hn, ⟨a⟩⟩).2.2).symm.trans a⟩
  have hexc : ∀ {t : StatedLieTag} {n p f : ℕ}, (t ∈ chevalleyExceptionalTags ∨ t ∈ reeTitsTags) →
      LieModel K t n p f → LieModel S t n p f := by
    intro t n p f ht h
    have : IsSimpleGroup K := by
      rcases h with ⟨hcl, -⟩ | ⟨-, ht', h⟩ | ⟨-, ht', h⟩ | ⟨-, -, h⟩
      · exfalso
        rcases ht with ht | ht <;> revert hcl ht <;> cases t <;> decide
      · exact (CFSG.LieType.Simplicity.fam_exceptional_converse K (.inl ⟨t, p, f, ht', h⟩)).2.2
      · exact (CFSG.LieType.Simplicity.fam_exceptional_converse K
          (.inr (.inl ⟨t, p, f, ht', h⟩))).2.2
      · exact (CFSG.LieType.Simplicity.fam_exceptional_converse K (.inr (.inr ⟨p, f, h⟩))).2.2
    exact LieModel.of_mulEquiv (hKS this) h
  rcases hmem with (h | h | h | h | h | h | h | h | h) | ⟨h3, -⟩ |
      ⟨-, h | h | h | h | h | h | h | h | h | h | h | ⟨F, _, _, hF, h⟩ | h | h | h | h | h⟩ |
      ⟨h5, -⟩ | ⟨h7, -⟩ | ⟨h11, -⟩
  · obtain ⟨a⟩ := h
    obtain ⟨a'⟩ := halt (by norm_num) a
    exact (KbarListThree.false_of_alt_six hZS a' hV hc).elim
  · obtain ⟨a⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl (halt (by norm_num) a))))
  · obtain ⟨a'⟩ := Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine (hst h)
    exact (KbarListThree.false_of_alt_six hZS a' hV hc).elim
  · exact Or.inl (Or.inl ⟨by decide, hst h⟩)
  · obtain ⟨a⟩ := h
    have hm : StatedClassicalModel K .PSL 3 3 1 :=
      ⟨⟨Nat.prime_three, le_rfl, by norm_num, by simp, by simp⟩, ZMod 3, inferInstance,
        inferInstance, by rw [Nat.card_zmod, pow_one],
        ⟨a.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 3))⟩⟩
    exact (KbarListThree.false_of_psl_three_three hZS (hst hm) hV hc).elim
  · exact (KbarListThree.false_of_psu_three_three hZS (hst h) hV hc).elim
  · have := CFSG.LocalAnalysis.AGL81I.Section3.four_le_pRank_of_isPSLType_four Nat.prime_three
      (by norm_num) h
    omega
  · have := CFSG.LocalAnalysis.AGL81I.Section3.four_le_pRank_of_psu_four (by norm_num) h
    omega
  · exact Or.inr (Or.inl (Or.inl ⟨by decide, hst h⟩))
  · omega
  · exact (KbarListThree.false_of_psl_two_eight (hst h) hV hc).elim
  · exact (KbarListThree.false_of_psl_three_four (hst h) hV hc).elim
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨by decide, hst h⟩)))
  · have hS := hexc (Or.inl (by decide)) (Or.inr (Or.inl ⟨rfl, by decide, h⟩) :
      LieModel K .trialityD4 0 2 1)
    exact (KbarListThree.false_of_trialityD4 hZS hS hV hc hVd).elim
  · have hS := hexc (Or.inr (by decide)) (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩)) :
      LieModel K .Tits 0 2 1)
    exact (KbarListThree.false_of_tits hZS (hS.reeTitsModel (by decide)).2 hV hc).elim
  · obtain ⟨a⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (halt (by norm_num) a)))))
  · obtain ⟨a⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (halt (by norm_num) a))))))
  · obtain ⟨a⟩ := h
    have : IsSimpleGroup NativeSporadic.M11 := CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
    have : IsSimpleGroup K := MulEquiv.isSimpleGroup (H := NativeSporadic.M11) a
    exact (KbarListThree.false_of_m11 hZS ⟨(hKS this).symm.trans a⟩ hV hc).elim
  · obtain ⟨a⟩ := h
    have : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    have : IsSimpleGroup K := MulEquiv.isSimpleGroup (H := NativeSporadic.M12) a
    exact (KbarListThree.false_of_m12 hZS ⟨(hKS this).symm.trans a⟩ hV hc).elim
  · obtain ⟨a⟩ := h
    have : IsSimpleGroup NativeSporadic.J3 := CFSG.Sporadic.J3.isSimpleGroup_J3
    have : IsSimpleGroup K := MulEquiv.isSimpleGroup (H := NativeSporadic.J3) a
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨(hKS this).symm.trans a⟩)))))
  · have := CFSG.LocalAnalysis.AGL81I.Section3.threeNineThreeMcLRank_holds K h
    omega
  · exact (KbarListThree.false_of_sl_three_four e hF h hV hc).elim
  · obtain ⟨-, ⟨a⟩⟩ := h
    exact (KbarListThree.false_of_alt_six hZS (e.symm.trans a) hV hc).elim
  · have := CFSG.LocalAnalysis.AGL81I.Section3.threeNineThreeCoverRank_holds K hq (Or.inl h)
    omega
  · have := CFSG.LocalAnalysis.AGL81I.Section3.threeNineThreeCoverRank_holds K hq
      (Or.inr (Or.inl h))
    omega
  · have := CFSG.LocalAnalysis.AGL81I.Section3.threeNineThreeCoverRank_holds K hq
      (Or.inr (Or.inr (Or.inl h)))
    omega
  · have := CFSG.LocalAnalysis.AGL81I.Section3.threeNineThreeCoverRank_holds K hq
      (Or.inr (Or.inr (Or.inr h)))
    omega
  · omega
  · omega
  · omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
