module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankFieldLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankFieldUni

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.HqRank

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem six_le_twoLocalRank
    {q : ℕ} (hq2 : q ≠ 2) {d : TauCeti.ValidLieTypeIndex}
    (hd : HqSixIdx q d.1) {X : Type} [Group X] [Finite X]
    (φ : X →* (TauCeti.CFSGIndex.lie d).Group) (hφ : Function.Surjective φ) :
    6 ≤ GLATwoLocalRank q X :=
  six_le_twoLocalRank_of_field six_le_twoLocalRank_A_field six_le_twoLocalRank_twistedA_field
    hq2 hd φ hφ

theorem six_le_twoLocalRank_of_pQuot
    {Ω : Type} [Group Ω] {p q : ℕ} (hq2 : q ≠ 2)
    {S : Subgroup Ω} {d : TauCeti.ValidLieTypeIndex} (hd : HqSixIdx q d.1)
    (eS : PSimple p S ≃* (TauCeti.CFSGIndex.lie d).Group) {K' : Type} [Group K'] [Finite K']
    (eK : PQuot p (⊤ : Subgroup K') ≃* ↥S) : 6 ≤ GLATwoLocalRank q K' := by
  let ψ : K' →* (TauCeti.CFSGIndex.lie d).Group :=
    eS.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (PQuot p S))).comp
      ((QuotientGroup.mk' (GLAPPrimeCore p ↥S)).comp (eK.toMonoidHom.comp
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup K'))).comp
          (Subgroup.topEquiv (G := K')).symm.toMonoidHom))))
  have hψ : Function.Surjective ψ :=
    eS.surjective.comp ((QuotientGroup.mk'_surjective _).comp
      ((QuotientGroup.mk'_surjective _).comp (eK.surjective.comp
        ((QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := K')).symm.surjective))))
  exact six_le_twoLocalRank hq2 hd ψ hψ

theorem not_hq_of_pQuot
    {Ω : Type} [Group Ω] [Finite Ω] {p q : ℕ} (hq2 : q ≠ 2)
    {S B : Subgroup Ω} {d : TauCeti.ValidLieTypeIndex} (hd : HqSixIdx q d.1)
    (eS : Nonempty (PSimple p S ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hB : CFSG.Open.pRank p B ≤ 5) :
    ¬ ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B := by
  rintro ⟨K', _, _, ⟨eK⟩, hle⟩
  have := six_le_twoLocalRank_of_pQuot hq2 hd eS.some eK
  omega

end CFSG.LocalAnalysis.GLTheoremA.S267.HqRank
