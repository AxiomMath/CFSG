module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H2017LFacts
public import CFSG.Open.GriessSchurMultipliers
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.GH74.Generic.BProg.B2.L2Cover
public import CFSG.GH74.GLS.Stage2.Local.Lemma23e

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.RankThree.PerfectCover

theorem I2017LieCenterL62_holds :
    I2017LieCenterL62 := by
  intro Q _ _ hQ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p n => exact (show False from hi).elim
  | alternating m k => exact (show False from hi).elim
  | sporadic s => exact (show False from hi).elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    have hd : d = TauCeti.LieTypeIndex.A 5 gfTwoPP := hi
    subst hd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (Nat.Prime gfTwoPP.p) := ⟨Nat.prime_two⟩
    let ψ : TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A 5 gfTwoPP, hv⟩ ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 6) (GaloisField 2 1) :=
      (CFSG.RankThree.PartTwo.Census.typeAGroupEquivProjSL 5 gfTwoPP hv).trans
        ((CFSG.PGLModel.projSLEquivStatedProj 6 (GaloisField 2 1)).trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 6 (GaloisField 2 1)).symm)
    obtain ⟨-, ⟨hm⟩⟩ := CFSG.Open.Open.griess_schur_multipliers_psl 2 1 6 (by norm_num) (by norm_num)
      (fun h => absurd h (by norm_num))
    haveI : Subsingleton (ZMod (Nat.gcd 6 (2 ^ 1 - 1))) := ZMod.subsingleton_iff.mpr (by norm_num)
    haveI : Subsingleton (ZMod (CFSG.Open.griessPSLExceptional 6 (2 ^ 1)).1) :=
      ZMod.subsingleton_iff.mpr (by decide)
    haveI : Subsingleton (ZMod (CFSG.Open.griessPSLExceptional 6 (2 ^ 1)).2) :=
      ZMod.subsingleton_iff.mpr (by decide)
    haveI hsubTarget : Subsingleton
        (Multiplicative (ZMod (Nat.gcd 6 (2 ^ 1 - 1)) × ZMod (CFSG.Open.griessPSLExceptional 6 (2 ^ 1)).1 ×
          ZMod (CFSG.Open.griessPSLExceptional 6 (2 ^ 1)).2)) :=
      inferInstanceAs (Subsingleton (ZMod (Nat.gcd 6 (2 ^ 1 - 1)) × ZMod (CFSG.Open.griessPSLExceptional 6 (2 ^ 1)).1 ×
          ZMod (CFSG.Open.griessPSLExceptional 6 (2 ^ 1)).2))
    haveI : Subsingleton (CFSG.Open.griessHopfMultiplier
        (Matrix.ProjectiveSpecialLinearGroup (Fin 6) (GaloisField 2 1))) := hm.toEquiv.subsingleton
    have hY : ∀ (Y : Type) [Group Y], Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 6) (GaloisField 2 1) →
        Nat.card (hopfMultiplier Y) = 1 := by
      intro Y _ φ
      haveI : Subsingleton (CFSG.Open.griessHopfMultiplier Y) :=
        (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr φ).toEquiv.subsingleton
      haveI : Subsingleton (hopfMultiplier Y) :=
        (hopfMultiplierEquivGriess Y).symm.toEquiv.subsingleton
      exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have hqs : CFSG.IsQuasisimple Q :=
      CFSG.GH74.GLS.Stage2.Local.isQuasisimple_of_perfect_simple' hQ.1 hQ.2
    have hdvd := CFSG.GH74.Generic.BProg.B2.L2Cover.card_center_dvd_card_hopfMultiplier_qs
      (K := Q) hqs e
    have h1 := hY _ ψ
    rw [h1] at hdvd
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)

end CFSG.LocalAnalysis.GLTheoremA

end
