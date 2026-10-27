module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLevi
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsParabolic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperShared
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplit
public import CFSG.RankThree.PartOne.KF.ClsSpWit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
open CFSG.RankThree.CentralCover (sl2Upper coe_sl2Upper sl2Upper_add sl2Upper_zero)
open scoped MatrixGroups

section Levi


variable {F : Type} [Field F] [Finite F]

theorem parabolicLevi_le_rootSpan_c3_or_b3 (hF : Nat.card F = 2) {J : Set (Fin Tag.F4.rank)}
    (hJ : J ≠ Set.univ) {E : Subgroup (ModGL .F4 F)} (hE : E ≤ parabolicLevi .F4 F J)
    (hE27 : Nat.card E = 27) :
    parabolicLevi .F4 F J ≤ rootSpan .F4 F c3LeviRoots ∨
      parabolicLevi .F4 F J ≤ rootSpan .F4 F b3LeviRoots := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have : Finite (ModGL .F4 F) := finite_modGL
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  have hJi : ∀ j ∈ J, j ≠ i := fun j hj h => hi (h ▸ hj)
  have hcases : ∀ i : Fin Tag.F4.rank, i = 0 ∨ i = 3 ∨ (i.val = 1 ∨ i.val = 2) := by decide
  rcases hcases i with rfl | rfl | h12
  · exact Or.inl (CFSG.StandardType.TableBF4TwoInputs.parabolicLevi_le_rootSpan hF
      fun j hj => CFSG.StandardType.F4Rest.single_mem_c3LeviRoots (hJi j hj))
  · exact Or.inr (CFSG.StandardType.TableBF4TwoInputs.parabolicLevi_le_rootSpan hF
      fun j hj => CFSG.StandardType.F4Rest.single_mem_b3LeviRoots (hJi j hj))
  · exfalso
    have hsub : J ⊆ (CFSG.Timmesfeld.ExceptionalOrders.maskSet .F4
        (CFSG.StandardType.TableBF4TwoInputs.f4CoatomMask i) :
        Set (Fin Tag.F4.rank)) := fun k hk => by
      exact_mod_cast CFSG.StandardType.TableBF4TwoInputs.f4CoatomMask_cover i k (hJi k hk)
    obtain ⟨-, -, -, hLP, -⟩ := parabolic_root_radical_Levi_factors (τ := .F4) (K := F) J
    have hPP := ((standard_parabolic_cells .F4 F).2.2.2.1 J _).2 hsub
    apply CFSG.StandardType.TableBF4TwoInputs.not_dvd_card_parabolic hF h12
    have h := Subgroup.card_dvd_of_le (hE.trans (hLP.trans hPP))
    rw [hE27] at h
    simpa using h

end Levi

section Rank


variable {F : Type} [Field F] [Finite F]

theorem glaTwoLocalRank_three_F4_le [CharP F 2] [Finite ↥(adjointGroup .F4 F)]
    (hF : Nat.card F = 2) : GLATwoLocalRank 3 ↥(adjointGroup .F4 F) ≤ 3 := by
  refine CFSG.LocalAnalysis.GLTheoremA.glaTwoLocalRank_le_of_card_le Nat.prime_three
    (fun R E hR hR2 hE hEel => CFSG.StandardType.F4Rest.twoLocal_card_le_of_levi Nat.prime_three
      (by norm_num) (by rw [hF]; norm_num)
      (CFSG.StandardType.F4Rest.ggF4LeviRankInput_holds Nat.prime_three (by norm_num)
        (by rw [hF]; norm_num)) hR hR2 hE hEel)

theorem three_le_glaTwoLocalRank_F4 [CharP F 2] [Finite ↥(adjointGroup .F4 F)] :
    3 ≤ GLATwoLocalRank 3 ↥(adjointGroup .F4 F) := by
  let φ : Fin 3 → SL(2, F) →* ↥(adjointGroup .F4 F) := fun i =>
    (c3LeviHom F).comp (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lam (k := F) i)
  have hlam : ∀ i : Fin 3, Function.Injective
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lam (k := F) i) := fun i => by
    obtain ⟨l, hl⟩ : ∃ l : Fin 3, l ≠ i := by
      fin_cases i
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    have h := CFSG.RankThree.PartOne.KFU.mk_lam_injective_of_ne (K := F) hl
    rw [MonoidHom.coe_comp] at h
    exact h.of_comp
  have hφ : ∀ i, Function.Injective (φ i) := fun i => c3LeviHom_injective.comp (hlam i)
  have hrJ : rootSL2 .F4 F rootR (sl2Upper 1) ∈ rootSL2R F := by
    rw [← range_rootSL2_rootR]
    exact ⟨_, rfl⟩
  let u : ↥(adjointGroup .F4 F) := ⟨rootSL2 .F4 F rootR (sl2Upper 1), rootSL2R_le_adjointGroup hrJ⟩
  have huJ : u ∈ (highestRootRankOne F).subgroupOf (adjointGroup .F4 F) := by
    rw [Subgroup.mem_subgroupOf, highestRootRankOne_eq_rootSL2R]
    exact hrJ
  have hu : orderOf u = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      show rootSL2 .F4 F rootR (sl2Upper 1) ^ 2 = 1
      rw [← map_pow, sq, ← sl2Upper_add, CharTwo.add_self_eq_zero, sl2Upper_zero, map_one]
    · intro h
      have h' : rootSL2 .F4 F rootR (sl2Upper 1) = rootSL2 .F4 F rootR 1 := by
        rw [map_one]
        exact congrArg Subtype.val h
      have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1)
        (rootSL2_rootR_injective h')
      simp [coe_sl2Upper] at this
  have hφC : ∀ i A, φ i A ∈ C3Levi F := fun i A => by
    rw [← range_c3LeviHom]
    exact ⟨_, rfl⟩
  have h := CFSG.RankThree.PartTwo.Census.Exceptional.card_le_localRank_three_of_commuting_SL2 φ hφ
    (fun i j hij A B => by
      change c3LeviHom F (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lam i A) *
          c3LeviHom F (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lam j B) =
        c3LeviHom F (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lam j B) *
          c3LeviHom F (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.lam i A)
      rw [← map_mul, ← map_mul,
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.commute_lam_lam hij A B).eq])
    hu (fun i A => (commute_of_mem_highestRootRankOne_of_mem_C3Levi huJ (hφC i A)).symm)
  simpa only [CFSG.Open.GLATwoLocalRank, CFSG.Assembly.RankThreeEven.localRank,
    Fintype.card_fin] using h

theorem glaTwoLocalRank_three_F4_two [Finite ↥(adjointGroup .F4 F)] (hF : Nat.card F = 2) :
    GLATwoLocalRank 3 ↥(adjointGroup .F4 F) = 3 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  exact le_antisymm (glaTwoLocalRank_three_F4_le hF) three_le_glaTwoLocalRank_F4

end Rank

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
