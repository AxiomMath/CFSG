module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi22
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432Fi24

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.H1017

private theorem attained_of_model {p : ℕ} (hp : p.Prime) {s : TauCeti.SporadicName} {r : ℕ}
    (hr : 1 ≤ r) {X : Type} [Group X] (b : X ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (h : ∀ [Finite X], r ≤ CFSG.Assembly.RankThreeEven.localRank p X) :
    TwoRankAttained p s r := by
  intro K _ _ hK
  obtain ⟨i, hi, ⟨e⟩⟩ := hK
  simp only [S8.sporIs] at hi
  subst hi
  haveI : Finite X := Finite.of_equiv K (b.trans e.symm).symm.toEquiv
  obtain ⟨U, hU2, hU1, E, hEN, hEe, hEc⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank hp hr h
  exact attained_of_mulEquiv (b.trans e.symm)
    ⟨E, U, S8.CoRows.isElemAbelian_of_class hEe, hEc, hU1, hU2, hEN⟩

section Ly


theorem witLy_holds : TwoRankAttained 3 .Ly 3 :=
  attained_of_model Nat.prime_three (by norm_num) (MulEquiv.refl _)
    CFSG.RankThree.PartTwo.Census.three_le_localRank_Ly

end Ly

section Suz


theorem witSuz_holds : TwoRankAttained 3 .Suz 3 :=
  attained_of_model Nat.prime_three (by norm_num) (MulEquiv.refl _)
    CFSG.RankThree.PartTwo.Census.three_le_localRank_Suz

end Suz

section Co2


theorem witCo2_holds : TwoRankAttained 3 .Co2 3 :=
  attained_of_model Nat.prime_three (by norm_num) (MulEquiv.refl _)
    CFSG.RankThree.PartTwo.Census.three_le_localRank_Co2

end Co2

section Th


theorem witTh_holds : TwoRankAttained 3 .Th 3 :=
  attained_of_model Nat.prime_three (by norm_num) (MulEquiv.refl _)
    CFSG.RankThree.PartTwo.Census.three_le_localRank_Th

end Th

section Co1


theorem witCo1_holds : TwoRankAttained 3 .Co1 4 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  exact attained_of_model (X := CFSG.Blueprint.NativeSporadic.Co1) Nat.prime_three (by norm_num)
    (by exact b) CFSG.RankThree.PartTwo.Census.four_le_localRank_three_Co1

end Co1

section Fi24

open CFSG.RankThree.Asc83Table CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint


set_option maxRecDepth 100000 in
theorem witFi24_holds : TwoRankAttained 3 .Fi24Prime 5 := by
  intro K _ _ hK
  obtain ⟨i, hi, ⟨e⟩⟩ := hK
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have φ : NativeSporadic.Fi24prime ≃* K := b.trans e.symm
  haveI : IsSimpleGroup K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime φ.symm
  have hcard : Nat.card K = 1255205709190661721292800 := by
    rw [← Nat.card_congr φ.toEquiv, CFSG.Sporadic.Fi24.card_Fi24prime]
  have hZ : Subgroup.center K = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative fun hc => by
      haveI := hc
      have hp := (Group.is_simple_iff_prime_card (α := K)).1 inferInstance
      rw [hcard] at hp
      norm_num at hp
  let ψ0 : NativeSporadic.Fi24prime ≃*
      (certMonoid 3 781 NativeSporadic.Fi24primeSeed1 NativeSporadic.Fi24primeSeed2)ˣ :=
    MulEquiv.refl _
  let q : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨V, E, hV, hV2, hEV, hE, hc⟩ :=
    H1420.WitFi24.hasTwoLocalWitness_of_modCheckV (CFSG.RankThree.Asc83Table.matOpsSpec 3 781)
      (AGLEmbedding.R3.modCheckV_matOps Certificates.certificate9602)
      ((ψ0.symm.trans φ).trans q.symm) H1420.WitFi24.j9 9 H1420.WitFi24.fixVec
      H1420.WitFi24.A9_sq H1420.WitFi24.A9_ne_one H1420.WitFi24.A9_fix
      H1420.WitFi24.fixVec_indep
  exact ⟨E, V, hE, hc, hV, hV2, hEV⟩

end Fi24

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
