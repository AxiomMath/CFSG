module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144IOutBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriOuter
public import CFSG.LargeExtraspecial.A2ModSLModel
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Final
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeAFinal
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24LeafShape
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHe3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporJ3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRu3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZCo1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14ChevFacts
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHe7
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import Certificates.Data.TabCo1ThreeE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144I

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Dickson.Bal207.D4Graph CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10GTri

section D4Two


theorem ringEquiv_eq_one_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (σ : K ≃+* K) : σ = 1 := by
  ext x
  rcases CFSG.LargeExtraspecial.A2Mod.eq_zero_or_eq_one_of_card_two hK x with rfl | rfl
  · simp
  · simp

theorem not_five_dvd_card_fixSubgroup_D4_two {S : Type} [Group S] [Finite S] {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hlabK : HasLabel S (fun l : GLALabel => l = ⟨.D, 4, 1⟩))
    (hin : ¬ InnDiagKind S ⟨.D, 4, 1⟩ α) (hfld : ¬ FieldKind S ⟨.D, 4, 1⟩ α) (hα : α ^ 3 = 1) :
    ¬ 5 ∣ Nat.card ↥(fixSubgroup α) := by
  intro h5
  obtain ⟨hperf, lab', hlam', hraw⟩ := hlabK
  obtain ⟨_, _, _, _, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hEq⟩ := hQ0
  subst hEq
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  rw [if_neg (by norm_num)] at hraw
  obtain ⟨K, hKF, hKfin, hK, hsR, hnaR, θ, -⟩ := hraw
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  have hchar2 : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  have hring2 : ringChar K = 2 := ringChar.eq K 2
  let eS : S ≃* S ⧸ Subgroup.center S :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  let e := eS.trans θ
  let eA := e.trans (isoAdj K)
  have hind : LargeEvenInduces θ (fun s s' => s' = α s) (MulAut.congr e α) := by
    rintro l _ rfl
    show MulAut.congr e α (e l) = e (α l)
    simp [MulAut.congr_apply]
  have huniq : ∀ u' : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))),
      LargeEvenInduces θ (fun s s' => s' = α s) u' → u' = MulAut.congr e α := by
    intro u' hu'
    ext r
    obtain ⟨s, rfl⟩ := e.surjective r
    exact (hu' s (α s) rfl).trans (hind s (α s) rfl).symm
  set α' := MulAut.congr eA α with hα'def
  have hα3 : α' ^ 3 = 1 := by rw [hα'def, ← map_pow, hα, map_one]
  have hcongr : α' = MulAut.congr (isoAdj K) (MulAut.congr e α) := MulEquiv.ext fun x => rfl
  obtain ⟨g, a, σ, ε, hε3, hσ3, hα'eq⟩ := exists_cube_normal_form_sigma α' hα3
  have hfix : (fixSubgroup α).map eA.toMonoidHom = fixSubgroup α' :=
    Y10F.fixSubgroup_map_congr eA α
  let eC : ↥(fixSubgroup α) ≃* ↥(fixSubgroup α') :=
    (Subgroup.equivMapOfInjective _ eA.toMonoidHom eA.injective).trans (MulEquiv.subgroupCongr hfix)
  rcases (by omega : ε = 0 ∨ ε = 1 ∨ ε = 2) with hε0 | hε12
  ·
    subst hε0
    obtain ⟨d, hd⟩ :=
      CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.exactNormalAut_eq_conj_of_charTwo
        hring2 a
    have hα1 : α' = MulAut.conj (g * d) * entrywiseAdjointAut Tag.D4 σ := by
      rw [hα'eq, tri_d4Graph_zero, mul_one,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.exactNormalAut_D4_eq_mul, hd,
        map_mul, mul_assoc]
    have hu : MulAut.congr e α = MulAut.conj ((isoAdj K).symm (g * d)) *
        MulAut.congr (isoAdj K).symm (entrywiseAdjointAut Tag.D4 σ) := by
      have h1 : MulAut.congr e α = MulAut.congr (isoAdj K).symm α' := by
        rw [hcongr]
        ext x
        simp [MulAut.congr_apply]
      rw [h1, hα1, map_mul, tri_congr_conj]
    by_cases hI : MulAut.congr e α ∈
        LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))
    · exact hin (tri_innDiagKind_of_recipe hperf hlam' hK hsR hnaR θ hI hind)
    · refine hfld (tri_fieldKind_of_recipe hperf hlam' hK hsR hnaR θ
        (i := MulAut.conj ((isoAdj K).symm (g * d)))
        (f := MulAut.congr (isoAdj K).symm (entrywiseAdjointAut Tag.D4 σ)) ⟨_, rfl⟩
        (tri_field_mem σ) (hu ▸ hind) ?_)
      rintro ⟨u', hu', hind'⟩
      exact hI (huniq u' hind' ▸ hu')
  ·
    have hσ1 : σ = 1 := ringEquiv_eq_one_of_card_two hK2 σ
    subst hσ1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, -, -, ⟨eD⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv
        (ℓ := 2) (f := 1) le_rfl K hK α' hα3 g a hε12 hα'eq
    have hcard : Nat.card ↥(fixSubgroup α) = Nat.card ↥(fixSubgroup φ) :=
      Nat.card_congr (eC.trans eD).toEquiv
    have hdvd : Nat.card ↥(fixSubgroup φ) ∣ 211341312 := by
      rw [← card_graphFixedRootGroup_D4_two hK₃ hFr]
      exact Subgroup.card_subgroup_dvd_card _
    rw [hcard] at h5
    have := h5.trans hdvd
    norm_num at this

end D4Two

end CFSG.LocalAnalysis.GLTheoremA.K144I

end
