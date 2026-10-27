module

public import CFSG.ClassicalInvolution.Asc77.AscR10E9
public import CFSG.ClassicalInvolution.Asc77.AscR10E5
public import CFSG.ClassicalInvolution.Asc77.AscR10E17
public import CFSG.ClassicalInvolution.Asc77.AscR10E2
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2TwPair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2TwMain
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryTwMain
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2InterfaceTw
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyE6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.Levi



open CFSG.ClassicalInvolution.Asc77.T3CII (GenSq eq_of_map_eq_of_genSq
  commute_of_map_commute_of_genSq)

section Pair

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional

variable {p e : ℕ} [Fact p.Prime]

local notation "kE6" => LeviE6.E6Closure p e

theorem conj_stdRankE6_of_commute_three (hp2 : p ≠ 2) (he : 1 ≤ e) (hq3 : p ^ e = 3)
    (hadm : StatedLieAdmissible .twistedE6 0 p e) {u : twistedE6Group p e}
    (hu : LeviE6.phiE6 p e u * signDiagE6 kE6 thetaE6 =
      signDiagE6 kE6 thetaE6 * LeviE6.phiE6 p e u) :
    (stdRankOne (twistedE6Datum p e) (proj thetaE6)).map (MulAut.conj u).toMonoidHom =
      stdRankOne (twistedE6Datum p e) (proj thetaE6) := by
  have hθ := stdRank_mem_longestFundamental_TwE6 (p := p) (e := e) isRoot_thetaE6 rho_thetaE6'
  have hH := phi_mem_h1E6_of_commute hp2 he hu
  refine eq_of_map_eq_of_genSq (LeviE6.phiE6 p e) (ker_twistedE6Phi_le_center p e kE6)
    (ker_twistedE6Phi_sq_three hq3 kE6)
    (genSq_of_mem_longestFundamental3 (t := .twistedE6) hq3 trivial hadm (by decide) (by decide)
      (map_conj_mem_longestFundamental u hθ))
    (genSq_of_mem_longestFundamental3 (t := .twistedE6) hq3 trivial hadm (by decide)
        (by decide) hθ) ?_
  rw [map_conj_map_of_hom, phi_stdRankE6_eq hp2 he,
    Subgroup.map_inf _ _ _ (MulAut.conj (LeviE6.phiE6 p e u)).injective,
    map_conj_rootRankOne_of_mem_h1E6 hH, map_conj_range_eq _ ⟨u, rfl⟩]

theorem eq_of_mem_longestFundamental_TwE6_three (hp2 : p ≠ 2) (he : 1 ≤ e) (hq3 : p ^ e = 3)
    (hadm : StatedLieAdmissible .twistedE6 0 p e) {R R' : Subgroup (twistedE6Group p e)}
    (hR : R ∈ longestFundamental (twistedE6Datum p e))
    (hR' : R' ∈ longestFundamental (twistedE6Datum p e)) {c c' : twistedE6Group p e}
    (hc : c ∈ R) (hc' : c' ∈ R') (ho : orderOf c = 2) (ho' : orderOf c' = 2)
    (h : LeviE6.phiE6 p e c = LeviE6.phiE6 p e c') : R = R' := by
  have hsingle : Generic.FundamentalSingleClass .twistedE6 (twistedE6Datum p e) :=
    fundamentalSingleClass .twistedE6 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (twistedE6Datum p e) (proj thetaE6) ∈
      Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e) :=
    ⟨1, proj thetaE6, Or.inl (isLongestRoot_twistedDatum_proj (frobQ p e) isRoot_thetaE6
      rho_thetaE6'), (Generic.conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := hsingle _ hθmem R (longestFundamental_subset .twistedE6 _ hR)
  obtain ⟨g', hg'⟩ := hsingle _ hθmem R' (longestFundamental_subset .twistedE6 _ hR')
  have hd : g⁻¹ * c * g ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6) :=
    Generic.mem_conjSub_iff.1 (hg ▸ hc)
  have hd' : g'⁻¹ * c' * g' ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6) :=
    Generic.mem_conjSub_iff.1 (hg' ▸ hc')
  have ord : ∀ (y x : twistedE6Group p e), orderOf x = 2 → orderOf (y⁻¹ * x * y) = 2 :=
    fun y x hx => by
      have := a2_orderOf_conj_eq_two hx y⁻¹
      simpa using this
  have z1 := phi_involution hp2 he hadm isRoot_thetaE6 rho_thetaE6' hd (ord g c ho)
  have z1' := phi_involution hp2 he hadm isRoot_thetaE6 rho_thetaE6' hd' (ord g' c' ho')
  simp only [map_mul, map_inv] at z1 z1'
  have hcg : LeviE6.phiE6 p e c = LeviE6.phiE6 p e g * signDiagE6 kE6 thetaE6 *
      (LeviE6.phiE6 p e g)⁻¹ := by
    rw [← z1]
    group
  have hcg' : LeviE6.phiE6 p e c' = LeviE6.phiE6 p e g' * signDiagE6 kE6 thetaE6 *
      (LeviE6.phiE6 p e g')⁻¹ := by
    rw [← z1']
    group
  have hu : LeviE6.phiE6 p e (g'⁻¹ * g) * signDiagE6 kE6 thetaE6 =
      signDiagE6 kE6 thetaE6 * LeviE6.phiE6 p e (g'⁻¹ * g) := by
    rw [map_mul, map_inv]
    have h2 := hcg.symm.trans (h.trans hcg')
    calc (LeviE6.phiE6 p e g')⁻¹ * LeviE6.phiE6 p e g * signDiagE6 kE6 thetaE6 =
        (LeviE6.phiE6 p e g')⁻¹ * (LeviE6.phiE6 p e g * signDiagE6 kE6 thetaE6 *
          (LeviE6.phiE6 p e g)⁻¹) * LeviE6.phiE6 p e g := by group
      _ = (LeviE6.phiE6 p e g')⁻¹ * (LeviE6.phiE6 p e g' * signDiagE6 kE6 thetaE6 *
          (LeviE6.phiE6 p e g')⁻¹) * LeviE6.phiE6 p e g := by rw [h2]
      _ = signDiagE6 kE6 thetaE6 * ((LeviE6.phiE6 p e g')⁻¹ * LeviE6.phiE6 p e g) := by group
  have hconj := conj_stdRankE6_of_commute_three hp2 he hq3 hadm hu
  calc R = Generic.conjSub g (stdRankOne (twistedE6Datum p e) (proj thetaE6)) := hg
    _ = Generic.conjSub (g' * (g'⁻¹ * g)) (stdRankOne (twistedE6Datum p e) (proj thetaE6)) := by
      rw [mul_inv_cancel_left]
    _ = Generic.conjSub g' (Generic.conjSub (g'⁻¹ * g)
          (stdRankOne (twistedE6Datum p e) (proj thetaE6))) := Generic.conjSub_mul _ _ _
    _ = Generic.conjSub g' (stdRankOne (twistedE6Datum p e) (proj thetaE6)) := by
      rw [show Generic.conjSub (g'⁻¹ * g) (stdRankOne (twistedE6Datum p e) (proj thetaE6)) =
        stdRankOne (twistedE6Datum p e) (proj thetaE6) from hconj]
    _ = R' := hg'.symm

end Pair

section Split

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

variable {p e : ℕ} [Fact p.Prime]

local notation "kE6" => LeviE6.E6Closure p e

theorem linearBlockStandardPair_of_split_TwE6_three (hp2 : p ≠ 2) (he : 1 ≤ e) (hq3 : p ^ e = 3)
    (hadm : StatedLieAdmissible .twistedE6 0 p e) {c₁ : twistedE6Group p e}
    (hc₁ : c₁ ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6)) (ho₁ : orderOf c₁ = 2)
    {R₂ : Subgroup (twistedE6Group p e)} (hR₂ : R₂ ∈ longestFundamental (twistedE6Datum p e))
    {c₂ x : twistedE6Group p e} (hc₂ : c₂ ∈ R₂) (ho₂ : orderOf c₂ = 2)
    (hxd : LeviE6.phiE6 p e x * signDiagE6 kE6 thetaE6 =
      signDiagE6 kE6 thetaE6 * LeviE6.phiE6 p e x)
    (hxy : LeviE6.phiE6 p e x * LeviE6.phiE6 p e c₂ * (LeviE6.phiE6 p e x)⁻¹ =
      signDiagE6 kE6 deltaE6) :
    ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (twistedE6Datum p e) (proj thetaE6)) R₂ := by
  have hx := conj_stdRankE6_of_commute_three hp2 he hq3 hadm hxd
  obtain ⟨c₀, hc₀R, hc₀o, hc₀Φ⟩ := exists_involution_stdRank_TwE6 hp2 he hadm hc₁ ho₁
    isPartnerE6_deltaE6.1 perm_deltaE6'
  have hRδ := stdRank_mem_longestFundamental_TwE6 (p := p) (e := e) isPartnerE6_deltaE6.1
    perm_deltaE6'
  have hΦ : LeviE6.phiE6 p e (x * c₂ * x⁻¹) = LeviE6.phiE6 p e c₀ := by
    rw [map_mul, map_mul, map_inv, hc₀Φ]
    exact hxy
  have hR₂x : R₂.map (MulAut.conj x).toMonoidHom =
      stdRankOne (twistedE6Datum p e) (proj deltaE6) :=
    eq_of_mem_longestFundamental_TwE6_three hp2 he hq3 hadm (map_conj_mem_longestFundamental x hR₂)
      hRδ ⟨c₂, hc₂, rfl⟩ hc₀R (a2_orderOf_conj_eq_two ho₂ x) hc₀o hΦ
  obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_theta_deltaTwE6 hadm
  have hxinv : (stdRankOne (twistedE6Datum p e) (proj thetaE6)).map
      (MulAut.conj x⁻¹).toMonoidHom = stdRankOne (twistedE6Datum p e) (proj thetaE6) := by
    have := a2_map_conj_inv_map_conj x (stdRankOne (twistedE6Datum p e) (proj thetaE6))
    rwa [hx] at this
  have hfin := linearBlockStandardPair_map_conj hW₁ x⁻¹
  rw [hxinv, ← hR₂x, a2_map_conj_inv_map_conj] at hfin
  exact ⟨_, hfin⟩

theorem not_commute_rootSL2_of_not_commute_TwE6_three (hp2 : p ≠ 2) (he : 1 ≤ e) (hq3 : p ^ e = 3)
    (hadm : StatedLieAdmissible .twistedE6 0 p e) {c₂ : twistedE6Group p e}
    (hn : ¬ ∀ r ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6), c₂ * r = r * c₂) :
    ¬ ∀ A : SL2 kE6, LeviE6.phiE6 p e c₂ * rootSL2 .E6 kE6 thetaE6 A =
      rootSL2 .E6 kE6 thetaE6 A * LeviE6.phiE6 p e c₂ := by
  intro hA
  apply hn
  have hθl := stdRank_mem_longestFundamental_TwE6 (p := p) (e := e) isRoot_thetaE6
    rho_thetaE6'
  refine fun r hr => (commute_of_map_commute_of_genSq (LeviE6.phiE6 p e)
    (ker_twistedE6Phi_le_center p e kE6) (ker_twistedE6Phi_sq_three hq3 kE6)
    (genSq_of_mem_longestFundamental3 (t := .twistedE6) hq3 trivial hadm (by decide)
        (by decide) hθl) (b := c₂) (fun r hr => ?_) r hr).symm
  have hmem : LeviE6.phiE6 p e r ∈ rootRankOneGroup .E6 kE6 thetaE6 :=
    phi_map_stdRank_le hp2 he isRoot_thetaE6 rho_thetaE6' (Subgroup.mem_map_of_mem _ hr)
  obtain ⟨A, hAr⟩ := hmem
  rw [← hAr]
  exact (hA A).symm

end Split

end CFSG.ClassicalInvolution.ModelFacts.Levi
