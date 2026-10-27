module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleStar
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleSplit
public import CFSG.ClassicalInvolution.RouteD.TypeENodes

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld

variable {p f : ℕ} [Fact p.Prime]

section E8

theorem yData_E8 (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E8 0 p f) (hq : 4 ≤ p ^ f) :
    YData p f .E8 0 := by
  have hp : p.Prime := Fact.out
  have hsc : FundamentalSingleClass .E8 (modelUniv .E8 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .E8 0 p f hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_e8Datum (F := GaloisField p f)
  have hl := ModelFacts.isLongestRoot_single .E8 0 p f hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .E8) (modelUniv .E8 0 p f Fact.out).D
    (k := ⟨0, by show 0 < 8; decide⟩) (hl ⟨0, by show 0 < 8; decide⟩ trivial)
  have hR₁ := rankOne_mem_fundamental (t := .E8) (modelUniv .E8 0 p f Fact.out).D
    (k := ⟨2, by show 2 < 8; decide⟩) (hl ⟨2, by show 2 < 8; decide⟩ trivial)
  exact ⟨by decide, hsc, perfectK_of_admissible hp trivial hadm,
    Gaps.fundPerfect_modelUniv hp2 trivial hadm hq, central_of_stdPair hsc hR₀ hW₁,
    std_of_stdPair hsc hR₀ hR₁ hW₁⟩

theorem modelStar_E8 (hadm : StatedLieAdmissible .E8 0 p f) :
    ModelStar (GaloisField p f) (modelFund p f .E8 0) := by
  have hp : p.Prime := Fact.out
  have hl := ModelFacts.isLongestRoot_single .E8 0 p f hp trivial hadm
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E8 0 p f hp trivial hadm
  have hdiv : (modelUniv .E8 0 p f Fact.out).D.divisible = ∅ := rfl
  have hℓ := lenSq_eq_of_simplyLaced (modelUniv .E8 0 p f Fact.out).D hdiv
    (fun i => hl i trivial) ⟨0, by show 0 < 8; decide⟩
  have hsc : FundamentalSingleClass .E8 (modelUniv .E8 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .E8 0 p f hp trivial hadm (by decide) (by decide)
  have hR : ∀ a : Fin 8, rankOne (modelUniv .E8 0 p f Fact.out).D.rootGroup a ∈
      fundamentalSubgroups .E8 (modelUniv .E8 0 p f Fact.out).D :=
    fun a => rankOne_mem_fundamental _ (hl a trivial)
  have hcomm : ∀ a b : Fin 8, a ≠ b → ¬ edgeE 8 a b → ¬ edgeE 8 b a →
      Commutes (rankOne (modelUniv .E8 0 p f Fact.out).D.rootGroup a)
        (rankOne (modelUniv .E8 0 p f Fact.out).D.rootGroup b) := fun a b hab h1 h2 =>
    commutes_rankOne_of_cartan_eq_zero _ hext hℓ
      ((WeakCT.edgeE_orientation (τ := .E8) (Or.inr (Or.inr rfl))).2.2.1 a b hab h1 h2).1
  have hstd : ∀ a b : Fin 8, edgeE 8 a b → ∃ W,
      LinearBlockStandardPair (GaloisField p f) W
        (rankOne (modelUniv .E8 0 p f Fact.out).D.rootGroup a)
        (rankOne (modelUniv .E8 0 p f Fact.out).D.rootGroup b) := fun a b h =>
    stdPair_edge_E8 h
  exact ModelStar.of_node_star hsc (hR 1) (hR 2) (hR 4) (hR 3)
    (hcomm 1 2 (by decide) (by decide) (by decide))
    (hcomm 1 4 (by decide) (by decide) (by decide))
    (hcomm 2 4 (by decide) (by decide) (by decide))
    (hstd 1 3 (by decide)) (hstd 2 3 (by decide))
    (by obtain ⟨W, hW⟩ := hstd 3 4 (by decide); exact ⟨W, hW.symm⟩)

theorem odd_center_E8 :
    ∀ y ∈ Subgroup.center (modelUniv .E8 0 p f Fact.out).K, Odd (orderOf y) := by
  intro y hy
  have hz := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    (τ := CFSG.Blueprint.Chevalley.Tag.E8) (K := GaloisField p f)
  have hy' : y ∈ Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup
      CFSG.Blueprint.Chevalley.Tag.E8 (GaloisField p f)) := hy
  rw [hz] at hy'
  have h1 : y = 1 := Subgroup.mem_bot.mp hy'
  rw [h1, orderOf_one]
  exact odd_one

theorem rowSingleE8 : RowPiece p f ShapeSingleE8 := by
  intro a t n hs G _ _ _ _ K z S hshape
  obtain ⟨rfl, rfl⟩ := hs
  exfalso
  obtain ⟨-, hadm⟩ := admissible_of_localShapeT hshape (by decide)
  have hn : n = 0 := hadm.2.2
  subst hn
  have hY := yData_E8 S.odd hadm (by have := S.five; omega)
  have hd := (hshape.nonempty_dictT hY.ne_d4 hY.sc S.inClass (mem_conjClass_self K) S.cls).some
  let c : ETCtx p f .E8 0 (conjClass K) K z :=
    { hp2 := S.odd, hq := S.five, hΩ := S.inClass, hex := S.exact, hK := mem_conjClass_self K,
      hz := S.cls, hP1 := S.p1, d := hd,
      hF := oddCoverSL3_of_five_le S.five, hY := hY }
  have hl := ModelFacts.isLongestRoot_single .E8 0 p f Fact.out trivial hadm
  have hne : (modelFund p f .E8 0).Nonempty :=
    ⟨_, rankOne_mem_fundamental (t := .E8) (modelUniv .E8 0 p f Fact.out).D
      (k := ⟨0, by show 0 < 8; decide⟩) (hl ⟨0, by show 0 < 8; decide⟩ trivial)⟩
  exact false_of_star c (single_class K) hshape hne (modelStar_E8 hadm) odd_center_E8

end E8

end CFSG.ClassicalInvolution.RouteD.Exotic
