module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T10
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.Blueprint

section A6Distinct


private theorem lieModel_psl29_of_alt6'
    {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    CFSG.Blueprint.LieModel X .PSL 2 3 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
  have hF : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  obtain ⟨φ⟩ :=
    LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      (GaloisField 3 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  refine Or.inl ⟨by decide, ?_⟩
  exact ⟨by norm_num [StatedLieAdmissible], GaloisField 3 2, inferInstance, inferInstance, hK,
    ⟨e.trans (φ.symm.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 3 2)))⟩⟩

theorem a6NoChar2Lambda_holds
    : A6NoChar2Lambda := by
  intro lab D _ _ hΛ hch2 hM hA6
  have hA6' : catalogIs D isA6 := hA6
  obtain ⟨i, hi, ⟨e⟩⟩ := hA6
  have e6 : D ≃* alternatingGroup (Fin 6) := by
    cases i with
    | alternating n h =>
      simp only [isA6] at hi
      subst hi
      exact e
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie _ => exact hi.elim
  have hcard360 : Nat.card D = 360 := by
    rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have h6 := lieModel_psl29_of_alt6' e6
  have hodd : CFSG.Blueprint.OddLieType D :=
    ⟨.PSL, 2, 3, 2, Nat.prime_three, by norm_num,
      CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel h6, h6⟩
  have hX : CFSG.Blueprint.LieModel D (markTag lab) (markRank lab) 2 (markDeg lab) := by
    have h := hM
    unfold MarkedModel at h
    rwa [hch2] at h
  by_cases hT : markTag lab = .Tits
  ·
    have htag : lab.tag = .twF4der := by
      obtain ⟨tg, rk, n⟩ := lab
      cases tg <;> simp only [markTag] at hT ⊢ <;> (try split_ifs at hT) <;> simp_all
    have hΛ' := hΛ
    unfold LargeEvenInLambda2 at hΛ'
    rw [htag] at hΛ'
    obtain ⟨-, hr, hn⟩ := hΛ'
    have hrk : markRank lab = 0 := by simp [markRank, htag, hr]
    have hdg : markDeg lab = 1 := by simp [markDeg, htag, hn]
    rw [hT, hrk, hdg] at hX
    rcases hX with ⟨hc, -⟩ | ⟨-, hc, -⟩ | ⟨-, -, hR⟩ | ⟨-, hc, -⟩
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hR
      have : Nat.card D = 17971200 := by
        rw [Nat.card_congr eT.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
      omega
    · exact absurd hc (by decide)
  · rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType_of_ne_Tits hX hT hodd with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    ·
      rw [h1, h2, h3] at hX
      rcases hX with ⟨-, hS⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
      · obtain ⟨hadm, K, hf, hfin, hK, ⟨θ⟩⟩ := hS
        have hc : Nat.card D = 60 := by
          rw [Nat.card_congr θ.toEquiv,
            CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 2) (by norm_num), hK]
          norm_num [Finset.prod_Icc_succ_top]
        omega
      · exact absurd h0 (by decide)
      · exact absurd h0 (by decide)
      · exact absurd h0 (by decide)
    ·
      rw [h1, h2, h3] at hX
      rcases hX with ⟨-, hS⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
      · obtain ⟨hadm, K, hf, hfin, hK, ⟨θ⟩⟩ := hS
        have hc : Nat.card D = 168 := by
          rw [Nat.card_congr θ.toEquiv,
            CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3) (by norm_num), hK]
          norm_num [Finset.prod_Icc_succ_top]
        omega
      · exact absurd h0 (by decide)
      · exact absurd h0 (by decide)
      · exact absurd h0 (by decide)
    ·
      rw [h1, h2, h3] at hX
      rcases hX with ⟨-, hS⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
      · obtain ⟨hadm, K, hf, hfin, hK, ⟨θ⟩⟩ := hS
        have hU4 : catalogIs D S9.isU4two :=
          catalogIs_u4two_of_statedProj (by rw [hK]; norm_num) θ
        exact (catDistinctAt_holds.u42_a6 D hU4 hA6').elim
      · exact absurd h0 (by decide)
      · exact absurd h0 (by decide)
      · exact absurd h0 (by decide)

end A6Distinct

end I91T

end CFSG.LocalAnalysis.GLTheoremA
