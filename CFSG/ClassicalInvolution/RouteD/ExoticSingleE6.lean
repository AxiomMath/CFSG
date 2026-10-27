module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleStar
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleSplit
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleTorus
public import CFSG.ClassicalInvolution.RouteD.TypeENodes

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld

variable {p f : ℕ} [Fact p.Prime]

section E6

theorem yData_E6 (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E6 0 p f) (hq : 4 ≤ p ^ f) :
    YData p f .E6 0 := by
  have hp : p.Prime := Fact.out
  have hsc : FundamentalSingleClass .E6 (modelUniv .E6 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .E6 0 p f hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_e6Datum (F := GaloisField p f)
  have hl := ModelFacts.isLongestRoot_single .E6 0 p f hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .E6) (modelUniv .E6 0 p f Fact.out).D
    (k := ⟨0, by show 0 < 6; decide⟩) (hl ⟨0, by show 0 < 6; decide⟩ trivial)
  have hR₁ := rankOne_mem_fundamental (t := .E6) (modelUniv .E6 0 p f Fact.out).D
    (k := ⟨2, by show 2 < 6; decide⟩) (hl ⟨2, by show 2 < 6; decide⟩ trivial)
  exact ⟨by decide, hsc, perfectK_of_admissible hp trivial hadm,
    Gaps.fundPerfect_modelUniv hp2 trivial hadm hq, central_of_stdPair hsc hR₀ hW₁,
    std_of_stdPair hsc hR₀ hR₁ hW₁⟩

theorem modelStar_E6 (hadm : StatedLieAdmissible .E6 0 p f) :
    ModelStar (GaloisField p f) (modelFund p f .E6 0) := by
  have hp : p.Prime := Fact.out
  have hl := ModelFacts.isLongestRoot_single .E6 0 p f hp trivial hadm
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E6 0 p f hp trivial hadm
  have hdiv : (modelUniv .E6 0 p f Fact.out).D.divisible = ∅ := rfl
  have hℓ := lenSq_eq_of_simplyLaced (modelUniv .E6 0 p f Fact.out).D hdiv
    (fun i => hl i trivial) ⟨0, by show 0 < 6; decide⟩
  have hsc : FundamentalSingleClass .E6 (modelUniv .E6 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .E6 0 p f hp trivial hadm (by decide) (by decide)
  have hR : ∀ a : Fin 6, rankOne (modelUniv .E6 0 p f Fact.out).D.rootGroup a ∈
      fundamentalSubgroups .E6 (modelUniv .E6 0 p f Fact.out).D :=
    fun a => rankOne_mem_fundamental _ (hl a trivial)
  have hcomm : ∀ a b : Fin 6, a ≠ b → ¬ edgeE 6 a b → ¬ edgeE 6 b a →
      Commutes (rankOne (modelUniv .E6 0 p f Fact.out).D.rootGroup a)
        (rankOne (modelUniv .E6 0 p f Fact.out).D.rootGroup b) := fun a b hab h1 h2 =>
    commutes_rankOne_of_cartan_eq_zero _ hext hℓ
      ((WeakCT.edgeE_orientation (τ := .E6) (Or.inl rfl)).2.2.1 a b hab h1 h2).1
  have hstd : ∀ a b : Fin 6, edgeE 6 a b → ∃ W,
      LinearBlockStandardPair (GaloisField p f) W
        (rankOne (modelUniv .E6 0 p f Fact.out).D.rootGroup a)
        (rankOne (modelUniv .E6 0 p f Fact.out).D.rootGroup b) := fun a b h =>
    stdPair_edge_E6 h
  exact ModelStar.of_node_star hsc (hR 1) (hR 2) (hR 4) (hR 3)
    (hcomm 1 2 (by decide) (by decide) (by decide))
    (hcomm 1 4 (by decide) (by decide) (by decide))
    (hcomm 2 4 (by decide) (by decide) (by decide))
    (hstd 1 3 (by decide)) (hstd 2 3 (by decide))
    (by obtain ⟨W, hW⟩ := hstd 3 4 (by decide); exact ⟨W, hW.symm⟩)

theorem odd_center_E6 :
    ∀ y ∈ Subgroup.center (modelUniv .E6 0 p f Fact.out).K, Odd (orderOf y) := by
  intro y hy
  have hy' : y ∈ Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
      (GaloisField p f)) := hy
  have h3 : y ^ 3 = 1 := center_pow_three (GaloisField p f) hy'
  exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)

theorem rowSingleE6 : RowPiece p f ShapeSingleE6 := by
  intro a t n hs G _ _ _ _ K z S hshape
  obtain ⟨rfl, rfl⟩ := hs
  exfalso
  obtain ⟨-, hadm⟩ := admissible_of_localShapeT hshape (by decide)
  have hn : n = 0 := hadm.2.2
  subst hn
  have hY := yData_E6 S.odd hadm (by have := S.five; omega)
  have hd := (hshape.nonempty_dictT hY.ne_d4 hY.sc S.inClass (mem_conjClass_self K) S.cls).some
  let c : ETCtx p f .E6 0 (conjClass K) K z :=
    { hp2 := S.odd, hq := S.five, hΩ := S.inClass, hex := S.exact, hK := mem_conjClass_self K,
      hz := S.cls, hP1 := S.p1, d := hd,
      hF := oddCoverSL3_of_five_le S.five, hY := hY }
  have hl := ModelFacts.isLongestRoot_single .E6 0 p f Fact.out trivial hadm
  have hne : (modelFund p f .E6 0).Nonempty :=
    ⟨_, rankOne_mem_fundamental (t := .E6) (modelUniv .E6 0 p f Fact.out).D
      (k := ⟨0, by show 0 < 6; decide⟩) (hl ⟨0, by show 0 < 6; decide⟩ trivial)⟩
  exact false_of_star c (single_class K) hshape hne (modelStar_E6 hadm) odd_center_E6

end E6

end CFSG.ClassicalInvolution.RouteD.Exotic
