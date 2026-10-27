module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8OmDescPlus
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8OmRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8OmMain
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8ClsUni
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.LargeExtraspecial.S4CEA6Basic
public import CFSG.LargeExtraspecial.S4CESmallThree
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8LnMain
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8SpMain
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs273d2
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.LieType.SeitzGeneration
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadMinus StatedQuadPlus
  StatedLieAdmissible StatedLieTag StatedClassicalModel)

theorem four_le_pRank_of_card {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 4 ≤ Nat.card E) : 4 ≤ CFSG.Open.pRank 3 E := by
  obtain ⟨j, hj⟩ := X1Sp.Gen.card_eq_three_pow' hE
  have hj4 : 4 ≤ j := by
    rw [hj] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  exact le_trans hj4 (X1Sp.Gen.le_pRank_of_card (le_refl E) hE hj)

theorem clsMinus_model {S : Type} [Group S] [Finite S] {n : ℕ} (hn5 : 5 ≤ n)
    (hM : StatedClassicalModel S .POmegaMinus n 2 3) (A : Subgroup (MulAut S))
    (hA : KD264F8Hyp S A) : False := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hn1 : 1 ≤ n := by omega
  have hAab : IsElemAbelian 3 A := hA.1
  have h4 : CFSG.Open.pRank 3 A ≤ 4 := hA.2.2.1
  have hnot : ¬ A ≤ innAutDerived S := hA.2.2.2.2.2
  obtain ⟨b, hbA, hbout⟩ := SetLike.not_le_iff_exists.1 hnot
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hb1 : b ≠ 1 := fun h => hbout (h ▸ one_mem _)
  have hbo : IsOuterOfOrder 3 b := by
    refine ⟨orderOf_eq_prime hb3 hb1, fun g hg => hbout ?_⟩
    rw [hg]
    exact inner_le_innAutDerived _ ⟨g, rfl⟩
  obtain ⟨e, K, _, _, k, σ, b', c', he, hf, hk, hK, hσ, hfix, hirr, ⟨ψ⟩⟩ :=
    exists_rational_model_minus_three (n := n) (ℓ := 2) (f := 3) (p := 3) hn1 hM hp rfl hbo
  have he1 : e = 1 := by omega
  subst he1
  obtain ⟨hAab', hout', hnot'⟩ := F8Trans.hyp_transport ψ A hA
  have hbo' : IsOuterOfOrder 3 (MulAut.congr ψ b) := isOuterOfOrder_congr ψ hbo
  obtain ⟨ι, hιinj, hιfix, -⟩ := exists_descent_om (n := n) (ℓ := 2) (e := 1) (by omega) hn1
    Nat.prime_two (by norm_num) le_rfl hk hK hσ hfix b' c' hirr hbo'
  have hk2 : Nat.card k = 2 := by simpa using hk
  obtain ⟨E₀, hE₀, hcard⟩ := bigElem_matrixProj_minus hk2 hn5 hn1 b' c' hirr
  have hbA' : MulAut.congr ψ b ∈ A.map (MulAut.congr ψ : MulAut S →* MulAut _) :=
    Subgroup.mem_map_of_mem _ hbA
  have hbnin : MulAut.congr ψ b ∉ (MulAut.conj : _ →* MulAut _).range := by
    rintro ⟨g, hg⟩
    exact hbo'.2 g hg.symm
  have hEfix : E₀.map ι ≤ fixSubgroup (MulAut.congr ψ b) := by
    rintro _ ⟨v, -, rfl⟩
    exact mem_fixSubgroup.2 (hιfix v)
  have hEab : IsElemAbelian 3 (E₀.map ι) := isElemAbelian_map_gen ι hE₀
  have h1 := hout' _ hbA' hbnin _ hEfix hEab
  have h2 : 4 ≤ CFSG.Open.pRank 3 (E₀.map ι) := by
    apply four_le_pRank_of_card hEab
    rw [Subgroup.card_map_of_injective hιinj]
    exact hcard
  have h3 := pRank_map_mulEquiv (p := 3) (MulAut.congr ψ) A
  omega

theorem clsPlus_model {S : Type} [Group S] [Finite S] {n : ℕ} (hn5 : 5 ≤ n)
    (hM : StatedClassicalModel S .POmegaPlus n 2 3) (A : Subgroup (MulAut S))
    (hA : KD264F8Hyp S A) : False := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hAab : IsElemAbelian 3 A := hA.1
  have h4 : CFSG.Open.pRank 3 A ≤ 4 := hA.2.2.1
  have hnot : ¬ A ≤ innAutDerived S := hA.2.2.2.2.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hM
  let ψ := coordinatePlusWitnessEquiv K e
  obtain ⟨b, hbA, hbout⟩ := SetLike.not_le_iff_exists.1 hnot
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hb1 : b ≠ 1 := fun h => hbout (h ▸ one_mem _)
  have hbo : IsOuterOfOrder 3 b := by
    refine ⟨orderOf_eq_prime hb3 hb1, fun g hg => hbout ?_⟩
    rw [hg]
    exact inner_le_innAutDerived _ ⟨g, rfl⟩
  obtain ⟨hAab', hout', hnot'⟩ := F8Trans.hyp_transport ψ A hA
  have hbo' : IsOuterOfOrder 3 (MulAut.congr ψ b) := isOuterOfOrder_congr ψ hbo
  obtain ⟨k, ι, hk, hιinj, hιfix, -⟩ := exists_descent_om_plus (n := n) (ℓ := 2) (f := 3) hn5
    Nat.prime_two (by norm_num) (by norm_num) hK hbo'
  have hk2 : Nat.card k = 2 := by simpa using hk
  obtain ⟨E₀, hE₀, hcard⟩ := bigElem_matrixProj_plus hk2 hn5
  have hbA' : MulAut.congr ψ b ∈ A.map (MulAut.congr ψ : MulAut S →* MulAut _) :=
    Subgroup.mem_map_of_mem _ hbA
  have hbnin : MulAut.congr ψ b ∉ (MulAut.conj : _ →* MulAut _).range := by
    rintro ⟨g, hg⟩
    exact hbo'.2 g hg.symm
  have hEfix : E₀.map ι ≤ fixSubgroup (MulAut.congr ψ b) := by
    rintro _ ⟨v, -, rfl⟩
    exact mem_fixSubgroup.2 (hιfix v)
  have hEab : IsElemAbelian 3 (E₀.map ι) := isElemAbelian_map_gen ι hE₀
  have h1 := hout' _ hbA' hbnin _ hEfix hEab
  have h2 : 4 ≤ CFSG.Open.pRank 3 (E₀.map ι) := by
    apply four_le_pRank_of_card hEab
    rw [Subgroup.card_map_of_injective hιinj]
    exact hcard
  have h3 := pRank_map_mulEquiv (p := 3) (MulAut.congr ψ) A
  omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

@[expose] def KD264F8ClsD4 : Prop :=
  KD264F8ClsAt fun e => ∃ q : TauCeti.PrimePower, e = .D 4 q

theorem KD264F8ClsOrthMinus_holds : KD264F8ClsOrthMinus := by
  intro d _hfin _hns _hk2 _hk3 hov hP _ _ _ A hA
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨n, q, rfl, hn5⟩ := hP
  have hq : q.card = 8 := hov
  have hp2 := primePower_p_eq_two_of_card_eight q hq
  have hexp : q.exponent = 3 := by
    have h8 : q.card = 2 ^ 3 := by rw [hq]; norm_num
    rw [TauCeti.PrimePower.card_def, hp2] at h8
    exact Nat.pow_right_injective (le_refl 2) h8
  have hm := CFSG.Models.lieModel_twistedD
    (G := (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedD n q, hd1⟩).Group) n q hd1
    (MulEquiv.refl _)
  obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := hm
  · rw [hp2, hexp] at hSC
    exact (F8Om.clsMinus_model hn5 hSC A hA).elim
  · have h4n : 4 ≤ n := hadm.2.2
    omega

theorem KD264F8ClsOrthPlus_of_D4 (hD4 : KD264F8ClsD4) : KD264F8ClsOrthPlus := by
  intro d _hfin hns hk2 hk3 hov hP hTri hTwA hTwE6 A hA
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨n, q, rfl⟩ := hP
  have hvalid := (TauCeti.LieTypeIndex.valid_iff _).1 hd1
  have hr : 4 ≤ n := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hvalid.1
  by_cases hn4 : n = 4
  · subst hn4
    exact hD4 ⟨TauCeti.LieTypeIndex.D 4 q, hd1⟩ hns hk2 hk3 hov ⟨q, rfl⟩ hTri hTwA hTwE6 A hA
  · have hn5 : 5 ≤ n := by omega
    exfalso
    have hq : q.card = 8 := hov
    have hp2 := primePower_p_eq_two_of_card_eight q hq
    have hexp : q.exponent = 3 := by
      have h8 : q.card = 2 ^ 3 := by rw [hq]; norm_num
      rw [TauCeti.PrimePower.card_def, hp2] at h8
      exact Nat.pow_right_injective (le_refl 2) h8
    have hm := CFSG.Models.lieModel_D
      (G := (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D n q, hd1⟩).Group) n q hd1
      (MulEquiv.refl _)
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := hm
    · rw [hp2, hexp] at hSC
      exact F8Om.clsPlus_model hn5 hSC A hA
    · omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
