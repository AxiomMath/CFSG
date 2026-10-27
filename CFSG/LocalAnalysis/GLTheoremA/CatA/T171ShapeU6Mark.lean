module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerBase
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.ClassicalGroups.UnitaryFlag.PointSylow
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityGe5
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthSymp
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AExist
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFacts
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryGen
public import Certificates.Certificate41501
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial

private theorem three_dvd_card_of_u6 {Ω : Type} [Group Ω] [Finite Ω] {L : Subgroup Ω} {n : ℕ}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hcat : catalogIs (PSimple 3 L) (S10.isU6n n)) :
    3 ∣ Nat.card ↥L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htw : catalogIs (PSimple 3 L) S10.isTwistedA := by
    obtain ⟨i, hi, he⟩ := hcat
    refine ⟨i, ?_, he⟩
    cases i with
    | cyclic p hp => simp [S10.isU6n, onLie] at hi
    | alternating m hm => simp [S10.isU6n, onLie] at hi
    | sporadic s => simp [S10.isU6n, onLie] at hi
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d <;> simp [S10.isU6n, S10.isTwistedA, onLie] at hi ⊢
  haveI : IsSimpleGroup (PSimple 3 L) := S10.isSimple_of_catalogIs_twistedA htw
  have hOtop : GLAPPrimeCore 3 ↥L ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (PQuot 3 L) := by
      rw [PQuot, QuotientGroup.subsingleton_iff]
      exact htop
    have hsub2 : Subsingleton (PSimple 3 L) := by
      rw [PSimple, QuotientGroup.subsingleton_iff]
      refine top_unique ?_
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      rw [Subsingleton.elim x y]
    exact not_subsingleton (PSimple 3 L) hsub2
  by_contra h3
  apply hOtop
  have hcop : Nat.Coprime 3 (Nat.card ↥L) :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr h3
  have hle : (⊤ : Subgroup ↥L) ≤ GLAPPrimeCore 3 ↥L := by
    have h := le_pPrimeCore_of_normal_coprime (p := 3) (N := (⊤ : Subgroup ↥L))
      (by infer_instance) (by simpa using hcop)
    simpa [GLAPPrimeCore] using h
  exact top_unique hle

theorem u6Marking_holds :
    U6Marking := by
  intro G _ _ L J A d b n hS hcat hnodd
  obtain ⟨-, lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_markedModel hS.idiag
  obtain ⟨R, _, I, F, hsR, hna, θ, hP, hM⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have h3 : 3 ∣ Nat.card ↥L := three_dvd_card_of_u6 hS.qs hcat
  obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.S172A.pSimple_equiv_centerQuot hS.qs h3
  have hcatZ : catalogIs (↥L ⧸ Subgroup.center ↥L) (S10.isU6n n) :=
    (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eP).mpr hcat
  have hMZ : MarkedModel lab (↥L ⧸ Subgroup.center ↥L) := MarkedModel.of_mulEquiv θ.symm hM
  have hLieZ : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 n :=
    CFSG.LocalAnalysis.GLTheoremA.I91T.lieModel_of_catalogIs_isU6n hcatZ
  obtain ⟨ht, hr, hnlab⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I91T.label_of_markedModel6 hMZ hLieZ
  have hlab_eq : lab = ⟨.twA, 5, n⟩ := by
    obtain ⟨tag, rank, nn⟩ := lab
    simp only [LargeEvenLabel.mk.injEq] at ht hr hnlab ⊢
    exact ⟨ht, hr, hnlab⟩
  subst hlab_eq
  have hrecipe := hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hrecipe
  dsimp only [CFSG.Assembly.LargeEvenRecipeUnitary] at hrecipe
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hrecipe
  obtain ⟨-, -, ⟨θ', hP', -⟩⟩ := hQ
  obtain ⟨hBN, hBI⟩ := hP'
  letI := hKfield
  letI := hKfinite
  have hfield : UnitaryFieldData 2 n K := unitaryFieldDataOfCard hKcard
  letI := hfield
  exact ⟨K, hKfield, hKfinite, hfield, θ', hBI⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
