module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2I164
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Rigid
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcChainsE6
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcUntw

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

section NoSylow


theorem rk2_noSylow_E6_seven {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    NoSylowNormalizesTwo 7 (adjointGroup Tag.E6 K) := by
  classical
  haveI : Fintype (WeylGroup .E6) := Fintype.ofFinite _
  have hp : Nat.Prime 7 := by norm_num
  have hpK : ¬ 7 ∣ Nat.card K := by rw [hK]; norm_num
  have he : orderOf ((Nat.card K : ℕ) : ZMod 7) = 3 := by
    rw [hK]
    exact (orderOf_eq_iff (by norm_num)).2 ⟨by decide, by decide⟩
  have hB : 12 < 7 * 3 := by norm_num
  refine noSylowNormalizesTwo_adjoint_of_chains .E6 hp (by norm_num) hpK he excE6Full
    parabolicSum_E6_univ_eq excE6Mask excE6Fac excE6Mask_cover parabolicSum_E6_coat_eq ?_ ?_ ?_
  · exact goodFactors_of_bound (by norm_num) hB (by decide)
  · intro i
    exact goodFactors_of_bound (by norm_num) hB (by fin_cases i <;> decide)
  · intro i
    fin_cases i <;> decide

end NoSylow

theorem rk2_twoLocal_lt_of_noSylow {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] {p k : ℕ}
    (hp : p.Prime) (e : X ≃* Y) (h : NoSylowNormalizesTwo p Y) (hk : 0 < k)
    (hv : (Nat.card Y).factorization p ≤ k) : GLATwoLocalRank p X < k := by
  by_contra hge
  replace hge := not_lt.1 hge
  have h1 : 1 ≤ GLATwoLocalRank p X := le_trans hk hge
  obtain ⟨A, Q, hA, hQ1, hQ2, hAQ, hAcard⟩ := rk2_exists_realizer hp h1
  refine h (Q.map e.toMonoidHom) (A.map e.toMonoidHom) ?_ ?_ ?_ ?_
  · intro hbot
    exact hQ1 ((Subgroup.map_eq_bot_iff_of_injective Q e.injective).1 hbot)
  · exact hQ2.map e.toMonoidHom
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hAQ
  · rw [Subgroup.card_map_of_injective e.injective, hAcard]
    exact pow_dvd_pow p (hv.trans hge)

section Model


theorem rk2_E6two_equiv {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (h : LabelOf K ⟨.E6, 0, 1⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧ Nat.card ↥K = ordE6 (2 ^ 1) ∧
      Nonempty (↥K ≃* ↥(adjointGroup Tag.E6 F)) := by
  obtain ⟨hQ, -, hM⟩ := labelOf_model h
  have hM' : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .E6 0 2 1 := hM
  obtain ⟨-, F, hF, hFin, hcard, ⟨φ⟩⟩ := hM'.chevalleyExceptionalModel
    (by decide : (StatedLieTag.E6) ∈ chevalleyExceptionalTags)
  have hQ' : CFSG.IsQuasisimple ↥K := (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2 hQ
  have hZ : Subgroup.center ↥K = ⊥ := by
    obtain ⟨-, ⟨eG⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
      (↥K ⧸ Subgroup.center ↥K) .E6 0 2 1 hM'
    have hcardG : Nat.card (Multiplier.generic .E6 0 2 1 × Multiplier.exceptional .E6 0 2 1) = 1 := by
      rw [CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional']
      decide
    haveI : Subsingleton (Multiplier.generic .E6 0 2 1 × Multiplier.exceptional .E6 0 2 1) :=
      (Nat.card_eq_one_iff_unique.1 hcardG).1
    haveI : Subsingleton (CFSG.Open.griessHopfMultiplier (↥K ⧸ Subgroup.center ↥K)) :=
      eG.injective.subsingleton
    exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.center_eq_bot_of_hopf_subsingleton hQ'
      (MulEquiv.refl _) inferInstance
  let ψ : ↥K ≃* ↥K ⧸ Subgroup.center ↥K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let χ : AdjointQuotient Tag.E6 F ≃* ↥(adjointGroup Tag.E6 F) :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := Tag.E6) (K := F))).trans
      QuotientGroup.quotientBot
  refine ⟨F, hF, hFin, by simpa using hcard, ?_, ⟨(ψ.trans φ).trans χ⟩⟩
  have e₂ : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordE6 (2 ^ 1) :=
    CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM'
  rw [← e₂]
  exact Nat.card_congr ψ.toEquiv

theorem rk2_twoLocal7_E6two {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (h : LabelOf K ⟨.E6, 0, 1⟩) : GLATwoLocalRank 7 ↥K ≤ 2 := by
  obtain ⟨F, hF, hFin, hcard, hordK, ⟨e⟩⟩ := rk2_E6two_equiv h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (K := F) (p := 2) (f := 1) (by simpa using hcard)
  have hN := rk2_noSylow_E6_seven hcard
  have hY : Nat.card ↥(adjointGroup Tag.E6 F) = ordE6 (2 ^ 1) := by
    rw [← hordK]
    exact (Nat.card_congr e.toEquiv).symm
  have hv : (Nat.card ↥(adjointGroup Tag.E6 F)).factorization 7 ≤ 3 := by
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hne : Nat.card ↥(adjointGroup Tag.E6 F) ≠ 0 := Nat.card_pos.ne'
    have hd : 7 ^ 4 ∣ Nat.card ↥(adjointGroup Tag.E6 F) :=
      ((Nat.prime_seven).pow_dvd_iff_le_factorization hne).2 hlt
    rw [hY] at hd
    revert hd
    norm_num [ordE6]
  have := rk2_twoLocal_lt_of_noSylow Nat.prime_seven e hN (by norm_num : 0 < 3) hv
  omega

theorem e62At_holds (G : Type) [Group G] [Finite G] : E62At G := by
  intro p L hp hp2 hL hhalf hnos
  obtain ⟨lab', hLab', hh⟩ := hhalf
  have hlab : lab' = ⟨.E6, 0, 1⟩ := rk2_E6two_unique hLab' hL
  subst hlab
  have hns : ¬ GLASplit16 p ⟨.E6, 0, 1⟩ := hnos _ hL
  have hp7 : p = 7 := by
    rcases hh with hs | hb | hc | hd | he1 | he2
    · exact absurd hs hns
    · exfalso
      obtain ⟨ht, -⟩ := hb
      rcases ht with ht | ht | ht | ht | ht <;> exact absurd ht (by decide)
    · exfalso
      obtain ⟨ht, -⟩ := hc
      rcases ht with ⟨ht, -⟩ | ht <;> exact absurd ht (by decide)
    · exfalso
      obtain ⟨-, hn, -⟩ := hd
      exact absurd hn (by decide)
    · exfalso
      obtain ⟨ht, -⟩ := he1
      exact absurd ht (by decide)
    · exact he2.2.2
  subst hp7
  exact rk2_twoLocal7_E6two hL

end Model

end CFSG.LocalAnalysis.GLTheoremA
