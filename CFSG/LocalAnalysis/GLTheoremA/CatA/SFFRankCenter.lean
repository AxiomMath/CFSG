module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H2017LFacts
public import CFSG.Open.GriessSchurMultipliers
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.GH74.Generic.BProg.B2.L2Cover
public import CFSG.GH74.GLS.Stage2.Local.Lemma23e

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.RankThree.PerfectCover

theorem I2017LieRankCenter_holds :
    I2017LieRankCenter := by
  intro Q _ _ hQ hcat z hz _
  have hqs : CFSG.IsQuasisimple Q :=
    CFSG.GH74.GLS.Stage2.Local.isQuasisimple_of_perfect_simple' hQ.1 hQ.2
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  have fin : ∀ (X : Type) [Group X], Subsingleton (CFSG.Open.griessHopfMultiplier X) →
      (Q ⧸ Subgroup.center Q ≃* X) → z = 1 := by
    intro X _ hX eX
    haveI : Subsingleton (hopfMultiplier X) :=
      (hopfMultiplierEquivGriess X).symm.toEquiv.subsingleton
    have h1 : Nat.card (hopfMultiplier X) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have hdvd := CFSG.GH74.Generic.BProg.B2.L2Cover.card_center_dvd_card_hopfMultiplier_qs
      (K := Q) hqs eX
    rw [h1] at hdvd
    have hc : Subgroup.center Q = ⊥ := Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)
    rw [hc] at hz
    exact Subgroup.mem_bot.mp hz
  cases i with
  | cyclic p n => exact (show False from hi).elim
  | alternating m k => exact (show False from hi).elim
  | sporadic s => exact (show False from hi).elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    have hd : I2017LieRankShape d := hi
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (Nat.Prime gfTwoPP.p) := ⟨Nat.prime_two⟩
    unfold I2017LieRankShape at hd
    rcases hd with ⟨N, hN8, -, hdN⟩ | ⟨k, hk5, hdk | hdk⟩
    ·
      subst hdN
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      let ψ : TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A (M + 1 - 1) gfTwoPP, hv⟩ ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin (M + 1)) (GaloisField 2 1) :=
        (CFSG.RankThree.PartTwo.Census.typeAGroupEquivProjSL (M + 1 - 1) gfTwoPP hv).trans
          ((CFSG.PGLModel.projSLEquivStatedProj (M + 1) (GaloisField 2 1)).trans
            (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (M + 1)
              (GaloisField 2 1)).symm)
      obtain ⟨-, ⟨hm⟩⟩ := CFSG.Open.Open.griess_schur_multipliers_psl 2 1 (M + 1) (by norm_num)
        (by omega) (fun h => by omega)
      have hgcd : Nat.gcd (M + 1) (2 ^ 1 - 1) = 1 := by norm_num
      have hexc : CFSG.Open.griessPSLExceptional (M + 1) (2 ^ 1) = (1, 1) := by
        simp [CFSG.Open.griessPSLExceptional, show M + 1 ≠ 2 by omega, show M + 1 ≠ 3 by omega,
          show M + 1 ≠ 4 by omega]
      haveI : Subsingleton (ZMod (Nat.gcd (M + 1) (2 ^ 1 - 1))) := ZMod.subsingleton_iff.mpr hgcd
      haveI : Subsingleton (ZMod (CFSG.Open.griessPSLExceptional (M + 1) (2 ^ 1)).1) :=
        ZMod.subsingleton_iff.mpr (by rw [hexc])
      haveI : Subsingleton (ZMod (CFSG.Open.griessPSLExceptional (M + 1) (2 ^ 1)).2) :=
        ZMod.subsingleton_iff.mpr (by rw [hexc])
      haveI : Subsingleton (CFSG.Open.griessHopfMultiplier
          (Matrix.ProjectiveSpecialLinearGroup (Fin (M + 1)) (GaloisField 2 1))) :=
        hm.toEquiv.subsingleton
      exact fin _ (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr ψ).toEquiv.subsingleton e
    ·
      subst hdk
      have hscm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even k gfTwoPP hv rfl
        (MulEquiv.refl (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.D k gfTwoPP, hv⟩))
      have hmod : CFSG.Models.LieModel (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.D k gfTwoPP, hv⟩)
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1 :=
        ⟨⟨Nat.prime_two, le_refl 1, by omega⟩, Or.inl hscm⟩
      obtain ⟨-, ⟨hm⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models _
        CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1 hmod
      have hg1 : (CFSG.Blueprint.Multiplier.genericOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).1 = 1 := by
        simp [CFSG.Blueprint.Multiplier.genericOrders]
      have hg2 : (CFSG.Blueprint.Multiplier.genericOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).2 = 1 := by
        simp [CFSG.Blueprint.Multiplier.genericOrders]
      have he1 : (CFSG.Blueprint.Multiplier.exceptionalOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).1 = 1 := by
        simp [CFSG.Blueprint.Multiplier.exceptionalOrders, show k ≠ 4 by omega]
      have he2 : (CFSG.Blueprint.Multiplier.exceptionalOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).2 = 1 := by
        simp [CFSG.Blueprint.Multiplier.exceptionalOrders, show k ≠ 4 by omega]
      haveI : Subsingleton (ZMod (CFSG.Blueprint.Multiplier.genericOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).1) := ZMod.subsingleton_iff.mpr hg1
      haveI : Subsingleton (ZMod (CFSG.Blueprint.Multiplier.genericOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).2) := ZMod.subsingleton_iff.mpr hg2
      haveI : Subsingleton (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).1) := ZMod.subsingleton_iff.mpr he1
      haveI : Subsingleton (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).2) := ZMod.subsingleton_iff.mpr he2
      haveI g1 : Subsingleton (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.genericOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).1)) :=
        inferInstanceAs (Subsingleton (ZMod (CFSG.Blueprint.Multiplier.genericOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).1))
      haveI g2 : Subsingleton (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.genericOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).2)) :=
        inferInstanceAs (Subsingleton (ZMod (CFSG.Blueprint.Multiplier.genericOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).2))
      haveI e1 : Subsingleton (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).1)) :=
        inferInstanceAs (Subsingleton (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).1))
      haveI e2 : Subsingleton (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).2)) :=
        inferInstanceAs (Subsingleton (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1).2))
      haveI hT : Subsingleton (CFSG.Blueprint.Multiplier.generic CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1 ×
          CFSG.Blueprint.Multiplier.exceptional CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus k 2 1) := inferInstance
      exact fin _ (hm.toEquiv.subsingleton) e
    ·
      subst hdk
      have hscm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even k gfTwoPP hv rfl
        (MulEquiv.refl (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedD k gfTwoPP, hv⟩))
      have hmod : CFSG.Models.LieModel (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedD k gfTwoPP, hv⟩)
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1 :=
        ⟨⟨Nat.prime_two, le_refl 1, by omega⟩, Or.inl hscm⟩
      obtain ⟨-, ⟨hm⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models _
        CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1 hmod
      have hcop : Nat.gcd 4 (2 ^ k + 1) = 1 := by
        have hev : Even (2 ^ k) := (Nat.even_pow).mpr ⟨even_two, by omega⟩
        have hodd : Odd (2 ^ k + 1) := hev.add_one
        have h2 : Nat.Coprime 2 (2 ^ k + 1) := Nat.coprime_two_left.mpr hodd
        have h4 : Nat.Coprime (2 ^ 2) (2 ^ k + 1) := Nat.Coprime.pow_left 2 h2
        norm_num at h4
        exact h4
      have hg1 : (CFSG.Blueprint.Multiplier.genericOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).1 = 1 := by
        simp [CFSG.Blueprint.Multiplier.genericOrders, hcop]
      have hg2 : (CFSG.Blueprint.Multiplier.genericOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).2 = 1 := by
        simp [CFSG.Blueprint.Multiplier.genericOrders]
      have he1 : (CFSG.Blueprint.Multiplier.exceptionalOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).1 = 1 := by
        simp [CFSG.Blueprint.Multiplier.exceptionalOrders]
      have he2 : (CFSG.Blueprint.Multiplier.exceptionalOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).2 = 1 := by
        simp [CFSG.Blueprint.Multiplier.exceptionalOrders]
      haveI : Subsingleton (ZMod (CFSG.Blueprint.Multiplier.genericOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).1) := ZMod.subsingleton_iff.mpr hg1
      haveI : Subsingleton (ZMod (CFSG.Blueprint.Multiplier.genericOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).2) := ZMod.subsingleton_iff.mpr hg2
      haveI : Subsingleton (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).1) := ZMod.subsingleton_iff.mpr he1
      haveI : Subsingleton (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders
          CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).2) := ZMod.subsingleton_iff.mpr he2
      haveI g1 : Subsingleton (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.genericOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).1)) :=
        inferInstanceAs (Subsingleton (ZMod (CFSG.Blueprint.Multiplier.genericOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).1))
      haveI g2 : Subsingleton (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.genericOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).2)) :=
        inferInstanceAs (Subsingleton (ZMod (CFSG.Blueprint.Multiplier.genericOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).2))
      haveI e1 : Subsingleton (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).1)) :=
        inferInstanceAs (Subsingleton (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).1))
      haveI e2 : Subsingleton (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).2)) :=
        inferInstanceAs (Subsingleton (ZMod (CFSG.Blueprint.Multiplier.exceptionalOrders CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1).2))
      haveI hT : Subsingleton (CFSG.Blueprint.Multiplier.generic CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1 ×
          CFSG.Blueprint.Multiplier.exceptional CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus k 2 1) := inferInstance
      exact fin _ (hm.toEquiv.subsingleton) e

end CFSG.LocalAnalysis.GLTheoremA

end
