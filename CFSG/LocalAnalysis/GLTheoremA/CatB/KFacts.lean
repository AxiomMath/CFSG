module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.KFactsE81
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KFactsAlt
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KFactsSp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.CatB.KFacts

noncomputable def pquotEquivPSimple {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hZ : Subgroup.center (PQuot 3 K) = ⊥) : PQuot 3 K ≃* PSimple 3 K :=
  ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

theorem kFactsAt_holds
    (G : Type) [Group G] [Finite G] : KFactsAt G := by
  intro X K _hK hty
  obtain ⟨hcat, hZ1⟩ := hty
  have hZ : Subgroup.center (PQuot 3 K) = ⊥ := Subgroup.card_eq_one.mp hZ1
  have hprof : KProfile (PQuot 3 K) := by
    rcases hcat with ⟨i, hi, ⟨e0⟩⟩ | ⟨i, hi, ⟨e0⟩⟩
    · obtain ⟨e⟩ := bridge_sp8two (⟨i, hi, ⟨e0⟩⟩ : catalogIs (PSimple 3 K) isSp82)
      exact kProfile_sp82.of_mulEquiv ((pquotEquivPSimple hZ).trans e).symm
    · cases i with
      | alternating m hm =>
        have hm12 : m = 12 := hi
        subst hm12
        exact kProfile_alt12.of_mulEquiv ((pquotEquivPSimple hZ).trans e0).symm
      | _ => exact hi.elim
  refine ⟨not_catalog_ON hZ hprof.card3, fun W hWK hW => rank_le_of_profile hprof hWK hW,
    fun K₀ hK₀ hcov => cover_of_profile hprof hK₀ hcov,
    fun g hg hk => inducesInnerMod_of_profile hprof hg hk, fun F hFK hF hF4 => ⟨?_, ?_⟩⟩
  · exact exists_normalizing_of_profile hprof hFK hF hF4
  · intro Q hQ hQK hQF
    exact relIndex_le_of_profile hprof hZ hFK hF hF4 hQ hQK hQF

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
