module

public import CFSG.LargeExtraspecial.S8CBFL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBender
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16Aux
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsAction
public import CFSG.CharacterTheory.Burnside
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def CorBSolvFamily (Y : Type) [Group Y] : Prop :=
  (∃ f, LieModel Y .PSL 2 2 f) ∨ (∃ f, LieModel Y .PSU 3 2 f) ∨
    (∃ f, LieModel Y .twistedB2 0 2 f) ∨ (∃ f, LieModel Y .PSL 3 2 f) ∨
    LieModel Y .PSU 3 3 1 ∨ Nonempty (Y ≃* alternatingGroup (Fin 6))

theorem isSolvable_centralizer_of_fusionIsBenderGroup {Y : Type} [Group Y] [Finite Y]
    (h : Open.fusionIsBenderGroup Y) {s : Y} (hs : orderOf s = 2) :
    Group.IsSolvable (centralizer ({s} : Set Y)) := by
  obtain ⟨_, _, hB⟩ := QuasithinUnique.Lin2.exists_fusionBenderBorel_of_fusionIsBenderGroup h
  exact ClassicalInvolution.isSolvable_centralizer_of_fusionBenderBorel hB hs

theorem fusionIsBenderGroup_of_lieModel_psl_two {Y : Type} [Group Y] {f : ℕ}
    (h : LieModel Y .PSL 2 2 f) : Open.fusionIsBenderGroup Y := by
  have hcl := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  obtain ⟨-, hf1, -, hne, -⟩ := hcl.1
  have hf : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    exact hne rfl
  exact QuasithinUnique.K1.fusionIsBenderGroup_of_stated_psl_two hf hcl

theorem fusionIsBenderGroup_of_lieModel_psu_three {Y : Type} [Group Y] {f : ℕ}
    (h : LieModel Y .PSU 3 2 f) : Open.fusionIsBenderGroup Y := by
  have hcl := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  obtain ⟨-, hf1, -, hne⟩ := hcl.1
  have hf : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    exact hne rfl
  exact QuasithinUnique.K1.fusionIsBenderGroup_of_stated_psu_three hf hcl

theorem fusionIsBenderGroup_of_lieModel_twistedB2 {Y : Type} [Group Y] {f : ℕ}
    (h : LieModel Y .twistedB2 0 2 f) : Open.fusionIsBenderGroup Y := by
  rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, hree, -⟩ | ⟨-, -, hsz⟩
  · exact absurd hcl (by decide)
  · exact absurd hce (by decide)
  · exact absurd hree (by decide)
  · exact QuasithinUnique.K1.fusionIsBenderGroup_of_suzukiModel hsz

theorem isSolvable_centralizer_of_alt_six {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 6)) {s : Y} (hs : orderOf s = 2) :
    Group.IsSolvable (centralizer ({s} : Set Y)) := by
  have hY : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hss : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    exact absurd hs (by norm_num)
  have h8 := (QuasithinUnique.Unc25K1.card_centralizer_eight_of_A6 e).2 s hss hs1
  have := Fact.mk Nat.prime_two
  have hp : IsPGroup 2 (centralizer ({s} : Set Y)) :=
    IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  have := hp.isNilpotent
  infer_instance

theorem isSolvable_centralizer_of_lieModel_psu_three_three {Y : Type} [Group Y]
    (h : LieModel Y .PSU 3 3 1) {s : Y} (hs : orderOf s = 2) :
    Group.IsSolvable (centralizer ({s} : Set Y)) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hF9 : Nat.card F = 9 := by rw [hF]; norm_num
  have hbot := LinearGroups.UnitaryThreeOverNine.statedScalars_subgroupOf_statedSU_eq_bot hF9
  let e' : Y ≃* StatedSU 3 3 F :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)
  refine isSolvable_centralizer_of_mulEquiv e' ?_
  have hd := LinearGroups.UnitaryThreeOverNine.unitaryFieldData_of_card hF9
  let L₀ : LinearGroups.UnitaryThreeOverNine.NonisoLine F :=
    ⟨F ∙ ![1, 0, 0], finrank_span_singleton (by simp),
      ⟨![1, 0, 0], Submodule.mem_span_singleton_self _, by simp [Fin.sum_univ_three]⟩⟩
  have hconj : IsConj (e' s)
      (LinearGroups.UnitaryThreeOverNine.tauLine hd hF9 L₀ : StatedSU 3 3 F) :=
    LinearGroups.UnitaryThreeOverNine.isConj_of_orderOf_eq_two hF9
      (by rw [MulEquiv.orderOf_eq, hs]) (LinearGroups.UnitaryThreeOverNine.tauLine hd hF9 L₀).2
  have hcard : Nat.card (centralizer ({e' s} : Set (StatedSU 3 3 F))) = 2 ^ 5 * 3 ^ 1 := by
    rw [QuasithinUnique.Unc25K1.card_centralizer_eq_of_isConj hconj,
      LinearGroups.UnitaryThreeOverNine.card_centralizer_tauLine rfl]
    norm_num
  have : Finite (centralizer ({e' s} : Set (StatedSU 3 3 F))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have := Fintype.ofFinite (centralizer ({e' s} : Set (StatedSU 3 3 F)))
  exact Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])

theorem isSolvable_centralizer_of_corBSolvFamily {Y : Type} [Group Y] [Finite Y]
    (h : CorBSolvFamily Y) {s : Y} (hs : orderOf s = 2) :
    Group.IsSolvable (centralizer ({s} : Set Y)) := by
  rcases h with ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | ⟨f, h⟩ | h | h
  · exact isSolvable_centralizer_of_fusionIsBenderGroup
      (fusionIsBenderGroup_of_lieModel_psl_two h) hs
  · exact isSolvable_centralizer_of_fusionIsBenderGroup
      (fusionIsBenderGroup_of_lieModel_psu_three h) hs
  · exact isSolvable_centralizer_of_fusionIsBenderGroup
      (fusionIsBenderGroup_of_lieModel_twistedB2 h) hs
  · exact isSolvable_centralizer_of_lieModel_psl_three h hs
  · exact isSolvable_centralizer_of_lieModel_psu_three_three h hs
  · obtain ⟨e⟩ := h
    exact isSolvable_centralizer_of_alt_six e hs

end CFSG.LargeExtraspecial.S8
