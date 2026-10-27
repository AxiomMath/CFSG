module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263Alpha
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Yardstones.Md0ec50421ce4

section Certified


theorem lieModel_twE6_of_catalogIs {Y : Type} [Group Y] {m : ℕ}
    (hcat : catalogIs Y (S10.isTE6n m)) : CFSG.Blueprint.LieModel Y .twistedE6 0 2 m := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex hcat
  cases d with
  | twistedE6 q =>
    have hq : q.p = 2 := hP.1
    have hn : q.exponent = m := hP.2
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel Y .twistedE6 q.p q.exponent := by
      refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
      exact CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.twistedE6 q hv hq (by decide) e
    rw [hq, hn] at hm
    exact (CFSG.RankThree.PartOne.Sec66T.lieModel_twistedE6_iff).2 ⟨rfl, hm⟩
  | _ => exact hP.elim

theorem exists_label_of_marking_one {X : Type} [Group X]
    (hM : CFSG.Assembly.LargeEvenMarking X (fun lab _ _ _ _ _ => lab.n = 1)) :
    ∃ lab : CFSG.Assembly.LargeEvenLabel, CFSG.Assembly.LargeEvenInLambda2 lab ∧ lab.n = 1 ∧
      CFSG.StandardType.MarkedModel lab (X ⧸ Subgroup.center X) := by
  obtain ⟨lab, hlab, R, _, I, F, θ, -, -, hP, hm⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel hM
  exact ⟨lab, hlab, hP, CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hm⟩

theorem not_marked_one_psu6 {Y : Type} [Group Y] {n : ℕ} (hn : 1 < n)
    {lab : CFSG.Assembly.LargeEvenLabel} (hlab1 : lab.n = 1)
    (hMlab : CFSG.StandardType.MarkedModel lab Y)
    (hU : CFSG.Blueprint.LieModel Y .PSU 6 2 n) : False := by
  obtain ⟨-, -, h⟩ := CFSG.LocalAnalysis.GLTheoremA.I91T.label_of_markedModel6 hMlab hU
  omega

theorem not_marked_one_twE6 {Y : Type} [Group Y] {n : ℕ} (hn : 3 ≤ n)
    {lab : CFSG.Assembly.LargeEvenLabel} (hlab : CFSG.Assembly.LargeEvenInLambda2 lab)
    (hlab1 : lab.n = 1) (hMlab : CFSG.StandardType.MarkedModel lab Y)
    (hTE : CFSG.Blueprint.LieModel Y .twistedE6 0 2 n) : False := by
  by_cases h2 : CFSG.StandardType.markChar lab = 2
  · obtain ⟨-, h⟩ := CFSG.StandardType.NbrInnerMore.eq_of_markedModel_twE6 (by omega) hTE hlab h2 hMlab
    omega
  · exfalso
    have hodd : CFSG.Blueprint.OddLieType Y := by
      obtain ⟨tag, rank, m⟩ := lab
      cases tag <;> simp [CFSG.StandardType.markChar] at h2
      all_goals first
        | exact ⟨.PSL, 2, 3, 2, Nat.prime_three, by norm_num,
            CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel
              (show CFSG.Blueprint.LieModel Y .PSL 2 3 2 from hMlab),
            (show CFSG.Blueprint.LieModel Y .PSL 2 3 2 from hMlab)⟩
        | exact ⟨.PSU, 3, 3, 1, Nat.prime_three, by norm_num,
            CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel
              (show CFSG.Blueprint.LieModel Y .PSU 3 3 1 from hMlab),
            (show CFSG.Blueprint.LieModel Y .PSU 3 3 1 from hMlab)⟩
    exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two_of_ne_Tits hTE (by decide)
      (by simp) (by simp) (by simp) hodd

theorem T263NotGF2_holds : T263NotGF2 := by
  unfold T263NotGF2
  intro X _ _ _ n hodd hn1 hcat hM
  obtain ⟨lab, hlab, hlab1, hMlab⟩ := exists_label_of_marking_one hM
  have hn3 : 3 ≤ n := by
    obtain ⟨k, rfl⟩ := hodd
    omega
  rcases hcat with hU | hE
  · exact not_marked_one_psu6 hn1 hlab1 hMlab (CFSG.LocalAnalysis.GLTheoremA.I91T.lieModel_of_catalogIs_isU6n hU)
  · exact not_marked_one_twE6 hn3 hlab hlab1 hMlab (lieModel_twE6_of_catalogIs hE)

end Certified

end CFSG.LocalAnalysis.GLTheoremA.T263

end
