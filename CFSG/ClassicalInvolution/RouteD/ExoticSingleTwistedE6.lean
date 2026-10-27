module

public import CFSG.ClassicalInvolution.Balance.BootstrapExoticE6
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleF4Star
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleSplit
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleTorus
public import CFSG.ClassicalInvolution.RouteD.TypeENodes

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld
open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley

section Centre

variable {k : Type} [Field k] (θ : k →+* k)

theorem center_le_iSup_torus_twisted (hθ : ∀ c, θ (θ c) = c) {z : fixedGroup k θ}
    (hz : z ∈ Subgroup.center (fixedGroup k θ)) :
    (z : e6Data_valid.minGroup k) ∈ ⨆ i, e6Data_valid.torus k i := by
  have hct := twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)
  have hext := twistedDatum_steinbergExtras θ hθ
  have hBU := twistedDatum_bruhatExtras θ
  rw [CFSG.LieType.TitsSimplicity.center_eq_normalCore_borel hct hext hBU] at hz
  have h1 := CFSG.LieType.TitsSimplicity.normalCore_borel_le_iSup hct hBU hz
  have h2 : (z : e6Data_valid.minGroup k) ∈ (⨆ i, hHat k θ i).map (fixedGroup k θ).subtype :=
    ⟨z, h1, rfl⟩
  rw [Subgroup.map_iSup] at h2
  refine (iSup_le (fun i => ?_) : (⨆ i, (hHat k θ i).map (fixedGroup k θ).subtype) ≤
    ⨆ i, e6Data_valid.torus k i) h2
  rintro _ ⟨y, hy, rfl⟩
  exact hHatE_le_iSup_torus θ i (show (y : e6Data_valid.minGroup k) ∈ hHatE k θ i from hy)

theorem center_pow_three_twisted (hθ : ∀ c, θ (θ c) = c) {z : fixedGroup k θ}
    (hz : z ∈ Subgroup.center (fixedGroup k θ)) : z ^ 3 = 1 := by
  obtain ⟨t, ht⟩ : (z : e6Data_valid.minGroup k) ∈ (torusProd k).range := by
    rw [range_torusProd]
    exact center_le_iSup_torus_twisted θ hθ hz
  have hconj : ∀ x : fixedGroup k θ, (z : e6Data_valid.minGroup k) * x = x * z := fun x =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz x).symm
  have hχ : ∀ j, rootChar k (Pi.single j 1) t = 1 := by
    intro j
    have hα : IsRoot .E6 (Pi.single j 1) := isRoot_single .E6 j
    have h1 := torusProd_conj_xm k hα t 1
    rw [ht] at h1
    by_cases hfix : rho (Pi.single j 1) = Pi.single j 1
    · have hx := hconj (xFixed θ hα hfix 1 (map_one θ))
      rw [xFixed_val] at hx
      have h5 : (z : e6Data_valid.minGroup k) * e6Data_valid.xm k (Pi.single j 1) 1 *
          (z : e6Data_valid.minGroup k)⁻¹ = e6Data_valid.xm k (Pi.single j 1) 1 := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hx
      have := e6Data_valid.xm_injective k hα (h1.symm.trans h5)
      exact Units.ext (by simpa using this)
    · have h2 := torusProd_conj_xm k (isRoot_rho hα) t ((twistSign (Pi.single j 1) : k) * θ 1)
      rw [ht] at h2
      have hx := hconj (xPair θ hθ hα hfix 1)
      rw [xPair_val] at hx
      have h3 : e6Data_valid.xm k (Pi.single j 1) (((rootChar k (Pi.single j 1) t : kˣ) : k) * 1) *
          e6Data_valid.xm k (rho (Pi.single j 1))
            (((rootChar k (rho (Pi.single j 1)) t : kˣ) : k) *
              ((twistSign (Pi.single j 1) : k) * θ 1)) =
          e6Data_valid.xm k (Pi.single j 1) 1 *
            e6Data_valid.xm k (rho (Pi.single j 1)) ((twistSign (Pi.single j 1) : k) * θ 1) := by
        rw [← h1, ← h2]
        calc _ = (z : e6Data_valid.minGroup k) * (e6Data_valid.xm k (Pi.single j 1) 1 *
              e6Data_valid.xm k (rho (Pi.single j 1))
                ((twistSign (Pi.single j 1) : k) * θ 1)) * (z : e6Data_valid.minGroup k)⁻¹ := by
              group
          _ = _ := by rw [mul_inv_eq_iff_eq_mul]; exact hx
      have h4 := (xm_mul_xm_rho_inj hα hfix h3).1
      exact Units.ext (by simpa using h4)
  have h3 : ((z : e6Data_valid.minGroup k)) ^ 3 = 1 := by
    rw [← ht]
    exact torusProd_pow_three k hχ
  exact Subtype.ext h3

end Centre

variable {p f : ℕ} [Fact p.Prime]

section TwistedE6

theorem yData_twistedE6 (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .twistedE6 0 p f)
    (hq : 4 ≤ p ^ f) : YData p f .twistedE6 0 := by
  have hp : p.Prime := Fact.out
  have hsc : FundamentalSingleClass .twistedE6 (modelUniv .twistedE6 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .twistedE6 0 p f hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := Balance.standardPair_twistedE6_nodes hadm
  have hl := ModelFacts.isLongestRoot_single .twistedE6 0 p f hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .twistedE6) (modelUniv .twistedE6 0 p f Fact.out).D
    (k := nf 0) (hl (nf 0) (by show 0 < 2; decide))
  have hR₁ := rankOne_mem_fundamental (t := .twistedE6) (modelUniv .twistedE6 0 p f Fact.out).D
    (k := nf 1) (hl (nf 1) (by show 1 < 2; decide))
  exact ⟨by decide, hsc, perfectK_of_admissible hp trivial hadm,
    Gaps.fundPerfect_modelUniv hp2 trivial hadm hq, central_of_stdPair hsc hR₀ hW₁,
    std_of_stdPair hsc hR₀ hR₁ hW₁⟩

theorem modelStar_twistedE6 (hadm : StatedLieAdmissible .twistedE6 0 p f) :
    ModelStar (GaloisField p f) (modelFund p f .twistedE6 0) := by
  have hp : p.Prime := Fact.out
  obtain ⟨nW, H, hct, hext⟩ := ModelFacts.hasBruhatDatum .twistedE6 0 p f hp trivial hadm
  have hl := ModelFacts.isLongestRoot_single .twistedE6 0 p f hp trivial hadm
  have hsc : FundamentalSingleClass .twistedE6 (modelUniv .twistedE6 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .twistedE6 0 p f hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := Balance.standardPair_twistedE6_nodes hadm
  exact modelStar_of_f4Nodes hct hext hsc (nf 0) (nf 1) (nf 2) (nf 3)
    (hl (nf 0) (by show 0 < 2; decide)) (hl (nf 1) (by show 1 < 2; decide))
    (by show Tag.cartan .F4 (nf 1) (nf 1) = 2; decide)
    (by show Tag.cartan .F4 (nf 1) (nf 2) = -1; decide)
    (by show Tag.cartan .F4 (nf 2) (nf 1) = -2; decide)
    (by show Tag.cartan .F4 (nf 2) (nf 2) = 2; decide)
    (by show Tag.cartan .F4 (nf 2) (nf 3) = -1; decide)
    (by show Tag.cartan .F4 (nf 3) (nf 2) = -1; decide)
    (by show Tag.cartan .F4 (nf 1) (nf 3) = 0; decide)
    (by show Tag.cartan .F4 (nf 3) (nf 1) = 0; decide)
    (by show Tag.cartan .F4 (nf 0) (nf 2) = 0; decide)
    (by show Tag.cartan .F4 (nf 0) (nf 3) = 0; decide)
    ⟨W₁, hW₁.symm⟩

theorem odd_center_twistedE6 (hf : 1 ≤ f) :
    ∀ y ∈ Subgroup.center (modelUniv .twistedE6 0 p f Fact.out).K, Odd (orderOf y) := by
  intro y hy
  have hy' : y ∈ Subgroup.center (fixedGroup (GaloisField p (2 * f)) (frobQ p f)) := hy
  have h3 : y ^ 3 = 1 := center_pow_three_twisted (frobQ p f) (frobQ_frobQ p f hf) hy'
  exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)

theorem rowSingleTwistedE6 : RowPiece p f ShapeSingleTwistedE6 := by
  intro a t n hs G _ _ _ _ K z S hshape
  obtain ⟨rfl, rfl⟩ := hs
  exfalso
  obtain ⟨-, hadm⟩ := admissible_of_localShapeT hshape (by decide)
  have hn : n = 0 := hadm.2.2
  subst hn
  have hY := yData_twistedE6 S.odd hadm (by have := S.five; omega)
  have hd := (hshape.nonempty_dictT hY.ne_d4 hY.sc S.inClass (mem_conjClass_self K) S.cls).some
  let c : ETCtx p f .twistedE6 0 (conjClass K) K z :=
    { hp2 := S.odd, hq := S.five, hΩ := S.inClass, hex := S.exact, hK := mem_conjClass_self K,
      hz := S.cls, hP1 := S.p1, d := hd,
      hF := oddCoverSL3_of_five_le S.five, hY := hY }
  have hl := ModelFacts.isLongestRoot_single .twistedE6 0 p f Fact.out trivial hadm
  have hne : (modelFund p f .twistedE6 0).Nonempty :=
    ⟨_, rankOne_mem_fundamental (t := .twistedE6) (modelUniv .twistedE6 0 p f Fact.out).D
      (k := nf 0) (hl (nf 0) (by show 0 < 2; decide))⟩
  exact false_of_star c (single_class K) hshape hne (modelStar_twistedE6 hadm)
    (odd_center_twistedE6 hadm.2.1)

end TwistedE6

end CFSG.ClassicalInvolution.RouteD.Exotic
