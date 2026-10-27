module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriField
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarD4Cent
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GTri

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.Y10GField

section TriD4


theorem triCanon_triD4 (hRig : GGLabelRigidInput) {X : Type} [Group X] [Finite X] {C J : Subgroup X}
    {labJ : GLALabel} {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 3) (T : K ≃+* K) (hT : ∀ c, T c = c ^ 2 ^ m)
    (e : ↥C ≃* ↥(graphFixedRootGroup TwistTag.D4 K T.toRingHom)) (hJ : GLAPComponent 3 C J)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) : canonLabel labJ = ⟨.triD4, 0, m⟩ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 K T.toRingHom) :=
    CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar.isSimpleGroup_graphFixedRootGroup_d4 hm hK hT
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K T
  haveI := hG
  have hna := tri_nonabelian_of_center_bot hZ
  obtain ⟨eJ⟩ := triComponent_equiv_simple hna e hJ
  haveI : IsSimpleGroup ↥J := eJ.isSimpleGroup
  haveI : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  obtain ⟨eR⟩ := triRecipe_equiv_of hm hK T hT
  have hlam : LargeEvenInLambda2 (⟨.triD4, 0, m⟩ : GLALabel) := ⟨hm, rfl⟩
  have hGH : GGHasLabel (⟨.triD4, 0, m⟩ : GLALabel)
      (LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.D4.tag.cartan K TwistTag.D4.perm m)) :=
    ⟨K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have := triCanon_of_equiv hRig hlabJ (eJ.trans eR.symm) hlam hGH
  rw [this]
  rfl

end TriD4

end CFSG.LocalAnalysis.GLTheoremA.Y10GTri
