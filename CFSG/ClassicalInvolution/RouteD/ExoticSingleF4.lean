module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleF4Star
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleSplit
public import CFSG.ClassicalInvolution.RouteD.TypeENodes

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.ModelFacts (lenSq lenSq_weylAction)

section F4

variable {p f : ℕ} [Fact p.Prime]

theorem yData_F4 (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .F4 0 p f) (hq : 4 ≤ p ^ f) :
    YData p f .F4 0 := by
  have hp : p.Prime := Fact.out
  have hsc : FundamentalSingleClass .F4 (modelUniv .F4 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .F4 0 p f hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_f4Datum (F := GaloisField p f)
  have hl := ModelFacts.isLongestRoot_single .F4 0 p f hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .F4) (modelUniv .F4 0 p f Fact.out).D
    (k := ⟨0, by show 0 < 4; decide⟩) (hl ⟨0, by show 0 < 4; decide⟩ (by show 0 < 2; decide))
  have hR₁ := rankOne_mem_fundamental (t := .F4) (modelUniv .F4 0 p f Fact.out).D
    (k := ⟨1, by show 1 < 4; decide⟩) (hl ⟨1, by show 1 < 4; decide⟩ (by show 1 < 2; decide))
  exact ⟨by decide, hsc, perfectK_of_admissible hp trivial hadm,
    Gaps.fundPerfect_modelUniv hp2 trivial hadm hq, central_of_stdPair hsc hR₀ hW₁,
    std_of_stdPair hsc hR₀ hR₁ hW₁⟩

theorem modelStar_F4 (hadm : StatedLieAdmissible .F4 0 p f) :
    ModelStar (GaloisField p f) (modelFund p f .F4 0) := by
  have hp : p.Prime := Fact.out
  obtain ⟨nW, H, hct, hext⟩ := ModelFacts.hasBruhatDatum .F4 0 p f hp trivial hadm
  have hl := ModelFacts.isLongestRoot_single .F4 0 p f hp trivial hadm
  have hsc : FundamentalSingleClass .F4 (modelUniv .F4 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .F4 0 p f hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_f4Datum (F := GaloisField p f)
  exact modelStar_of_f4Nodes hct hext hsc ⟨0, by show 0 < 4; decide⟩ ⟨1, by show 1 < 4; decide⟩
    ⟨2, by show 2 < 4; decide⟩ ⟨3, by show 3 < 4; decide⟩
    (hl ⟨0, by show 0 < 4; decide⟩ (by show 0 < 2; decide))
    (hl ⟨1, by show 1 < 4; decide⟩ (by show 1 < 2; decide))
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .F4 ⟨1, by decide⟩ ⟨1, by decide⟩ = 2; decide)
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .F4 ⟨1, by decide⟩ ⟨2, by decide⟩ = -1; decide)
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .F4 ⟨2, by decide⟩ ⟨1, by decide⟩ = -2; decide)
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .F4 ⟨2, by decide⟩ ⟨2, by decide⟩ = 2; decide)
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .F4 ⟨2, by decide⟩ ⟨3, by decide⟩ = -1; decide)
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .F4 ⟨3, by decide⟩ ⟨2, by decide⟩ = -1; decide)
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .F4 ⟨1, by decide⟩ ⟨3, by decide⟩ = 0; decide)
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .F4 ⟨3, by decide⟩ ⟨1, by decide⟩ = 0; decide)
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .F4 ⟨0, by decide⟩ ⟨2, by decide⟩ = 0; decide)
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .F4 ⟨0, by decide⟩ ⟨3, by decide⟩ = 0; decide)
    ⟨W₁, hW₁.symm⟩

theorem odd_center_F4 :
    ∀ y ∈ Subgroup.center (modelUniv .F4 0 p f Fact.out).K, Odd (orderOf y) := by
  intro y hy
  have hz := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    (τ := CFSG.Blueprint.Chevalley.Tag.F4) (K := GaloisField p f)
  have hy' : y ∈ Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup
      CFSG.Blueprint.Chevalley.Tag.F4 (GaloisField p f)) := hy
  rw [hz] at hy'
  have h1 : y = 1 := Subgroup.mem_bot.mp hy'
  rw [h1, orderOf_one]
  exact odd_one

theorem rowSingleF4 : RowPiece p f ShapeSingleF4 := by
  intro a t n hs G _ _ _ _ K z S hshape
  obtain ⟨rfl, rfl⟩ := hs
  exfalso
  obtain ⟨-, hadm⟩ := admissible_of_localShapeT hshape (by decide)
  have hn : n = 0 := hadm.2.2
  subst hn
  have hY := yData_F4 S.odd hadm (by have := S.five; omega)
  have hd := (hshape.nonempty_dictT hY.ne_d4 hY.sc S.inClass (mem_conjClass_self K) S.cls).some
  let c : ETCtx p f .F4 0 (conjClass K) K z :=
    { hp2 := S.odd, hq := S.five, hΩ := S.inClass, hex := S.exact, hK := mem_conjClass_self K,
      hz := S.cls, hP1 := S.p1, d := hd,
      hF := oddCoverSL3_of_five_le S.five, hY := hY }
  have hl := ModelFacts.isLongestRoot_single .F4 0 p f Fact.out trivial hadm
  have hne : (modelFund p f .F4 0).Nonempty :=
    ⟨_, rankOne_mem_fundamental (t := .F4) (modelUniv .F4 0 p f Fact.out).D
      (k := ⟨0, by show 0 < 4; decide⟩) (hl ⟨0, by show 0 < 4; decide⟩ (by show 0 < 2; decide))⟩
  exact false_of_star c (single_class K) hshape hne (modelStar_F4 hadm) odd_center_F4

end F4

end CFSG.ClassicalInvolution.RouteD.Exotic
