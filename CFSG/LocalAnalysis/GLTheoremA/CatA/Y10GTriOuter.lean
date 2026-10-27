module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriD4Fix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsOrthKind
public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeField
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.EvenClass
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzBal
public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddNeThree
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.Final
public import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV5
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4GraphPlanes
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Defs
public import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
public import CFSG.LieType.SeitzGeneration.OuterSpPair
public import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
public import CFSG.LieType.SeitzGeneration.RootPairSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCyc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofKFacts
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofFus
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail17
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
public import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.S4Free.SuzukiEight
public import Certificates.Certificate8166
public import Certificates.Certificate9530

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GTri

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Dickson.Bal207.D4Graph CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA.Y10GField

section Outer


theorem tri_d4Graph_zero {K : Type} [Field K] : d4Graph K 0 = 1 :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_d4Graph, pow_zero, one_mul, inv_one, mul_one]; rfl)

theorem tri_innDiagKind_of_recipe {S : Type} [Group S] {n : ℕ} (hperf : commutator S = ⊤)
    (hlam : LargeEvenInLambda2 (⟨.D, 4, n⟩ : GLALabel))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hs : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))))
    (hna : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)), a * b ≠ b * a)
    (θ : S ⧸ Subgroup.center S ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))
    {α : MulAut S} {u : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))}
    (hu : u ∈ LargeEvenInnSet _) (hind : LargeEvenInduces θ (fun s s' => s' = α s) u) :
    InnDiagKind S ⟨.D, 4, n⟩ α := by
  refine ⟨hperf, ⟨.D, 4, n⟩, hlam, ?_⟩
  dsimp only [CFSG.Assembly.LargeEvenRawDatum]
  rw [if_neg (by norm_num)]
  exact ⟨K, inferInstance, inferInstance, hK, hs, hna, θ, rfl, u, hu, hind⟩

theorem tri_fieldKind_of_recipe {S : Type} [Group S] {n : ℕ} (hperf : commutator S = ⊤)
    (hlam : LargeEvenInLambda2 (⟨.D, 4, n⟩ : GLALabel))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hs : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))))
    (hna : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)), a * b ≠ b * a)
    (θ : S ⧸ Subgroup.center S ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))
    {α : MulAut S} {i f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))}
    (hi : i ∈ LargeEvenInnSet _)
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4))))
    (hind : LargeEvenInduces θ (fun s s' => s' = α s) (i * f))
    (hout : ¬ ∃ u ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))),
      LargeEvenInduces θ (fun s s' => s' = α s) u) :
    FieldKind S ⟨.D, 4, n⟩ α := by
  refine ⟨hperf, ⟨.D, 4, n⟩, hlam, ?_⟩
  dsimp only [CFSG.Assembly.LargeEvenRawDatum]
  rw [if_neg (by norm_num)]
  exact ⟨K, inferInstance, inferInstance, hK, hs, hna, θ, rfl, ⟨i, hi, f, hf, hind⟩, hout⟩

theorem tri_field_mem {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    MulAut.congr (isoAdj K).symm (entrywiseAdjointAut Tag.D4 σ) ∈
      LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4))) := by
  refine ⟨σ, fun h h' hh' => ?_⟩
  have hh'eq : h' = sigmaOmega σ h := Subtype.ext (Units.ext hh')
  subst hh'eq
  show (isoAdj K).symm (entrywiseAdjointAut Tag.D4 σ (isoAdj K (QuotientGroup.mk h))) =
    QuotientGroup.mk (sigmaOmega σ h)
  rw [MulEquiv.symm_apply_eq, isoAdj_mk, isoAdj_mk, thetaOmega_sigmaOmega]

theorem triOuterD4_of_rig (hRig : GGLabelRigidInput) : TriOuterD4 := by
  intro S _ _ α J labK labJ hT hr hcen hlabK hin hfld hα hlabJ hJ
  obtain ⟨tK, rK, nK⟩ := labK
  dsimp only at hT hr
  subst hT
  subst hr
  obtain ⟨hperf, lab', hlam', hraw⟩ := hlabK
  obtain ⟨_, _, _, _, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hEq⟩ := hQ0
  subst hEq
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  rw [if_neg (by norm_num)] at hraw
  obtain ⟨K, hKF, hKfin, hK, hsR, hnaR, θ, -⟩ := hraw
  have hn : 1 ≤ nK := hlam'.1
  have hcanK : canonLabel (⟨.D, 4, nK⟩ : GLALabel) = ⟨.D, 4, nK⟩ := by
    simp [canonLabel]
  by_cases hn1 : nK = 1
  · exact fieldRel_of_canon_n_one 3 _ labJ (by rw [hcanK]; exact hn1)
  have hn2 : 2 ≤ nK := by omega
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
    exfalso
    subst hε0
    obtain ⟨d, hd⟩ := CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.exactNormalAut_eq_conj_of_charTwo
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
    by_cases hI : MulAut.congr e α ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))
    · exact hin (tri_innDiagKind_of_recipe hperf hlam' hK hsR hnaR θ hI hind)
    · refine hfld (tri_fieldKind_of_recipe hperf hlam' hK hsR hnaR θ
        (i := MulAut.conj ((isoAdj K).symm (g * d)))
        (f := MulAut.congr (isoAdj K).symm (entrywiseAdjointAut Tag.D4 σ)) ⟨_, rfl⟩
        (tri_field_mem σ) (hu ▸ hind) ?_)
      rintro ⟨u', hu', hind'⟩
      exact hI (huniq u' hind' ▸ hu')
  · by_cases hσ1 : σ = 1
    · subst hσ1
      have hnJ := triD4_graph hRig hn2 hK hε12 hα3 hα'eq eC hJ hlabJ
      refine Or.inl ?_
      rw [hcanK, hnJ]
    · obtain ⟨m, hm, hnm, hcJ⟩ := triD4_graphField hRig hK hσ3 hσ1 hε12 hα3 hα'eq eC hJ hlabJ
      refine Or.inr ⟨?_, Or.inr ⟨rfl, rfl, rfl, ?_⟩⟩
      · rw [hcanK, hcJ]
        show nK = 3 * m
        omega
      · rw [hcJ]

theorem triOuterD4_holds : TriOuterD4 :=
  triOuterD4_of_rig CFSG.StandardType.ggLabelRigidInput_holds

end Outer

end CFSG.LocalAnalysis.GLTheoremA.Y10GTri
