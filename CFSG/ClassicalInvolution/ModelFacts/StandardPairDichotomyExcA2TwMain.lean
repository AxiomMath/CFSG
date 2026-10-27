module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2TwPair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2InterfaceTw
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrth
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

section Main

variable {p e : ℕ} [Fact p.Prime]

local notation "kE6" => LeviE6.E6Closure p e

theorem perm_deltaE6' : rho deltaE6 = deltaE6 := perm_deltaE6

theorem linearBlockStandardPair_of_split_TwE6 (hp2 : p ≠ 2) (he : 1 ≤ e) (hq : 5 ≤ p ^ e)
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
  have hx := conj_stdRankE6_of_commute hp2 he hq hadm hxd
  obtain ⟨c₀, hc₀R, hc₀o, hc₀Φ⟩ := exists_involution_stdRank_TwE6 hp2 he hadm hc₁ ho₁
    isPartnerE6_deltaE6.1 perm_deltaE6'
  have hRδ := stdRank_mem_longestFundamental_TwE6 (p := p) (e := e) isPartnerE6_deltaE6.1
    perm_deltaE6'
  have hΦ : LeviE6.phiE6 p e (x * c₂ * x⁻¹) = LeviE6.phiE6 p e c₀ := by
    rw [map_mul, map_mul, map_inv, hc₀Φ]
    exact hxy
  have hR₂x : R₂.map (MulAut.conj x).toMonoidHom =
      stdRankOne (twistedE6Datum p e) (proj deltaE6) :=
    eq_of_mem_longestFundamental_TwE6 hp2 he hq hadm (map_conj_mem_longestFundamental x hR₂)
      hRδ ⟨c₂, hc₂, rfl⟩ hc₀R (a2_orderOf_conj_eq_two ho₂ x) hc₀o hΦ
  obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_theta_deltaTwE6 hadm
  have hxinv : (stdRankOne (twistedE6Datum p e) (proj thetaE6)).map
      (MulAut.conj x⁻¹).toMonoidHom = stdRankOne (twistedE6Datum p e) (proj thetaE6) := by
    have := a2_map_conj_inv_map_conj x (stdRankOne (twistedE6Datum p e) (proj thetaE6))
    rwa [hx] at this
  have hfin := linearBlockStandardPair_map_conj hW₁ x⁻¹
  rw [hxinv, ← hR₂x, a2_map_conj_inv_map_conj] at hfin
  exact ⟨_, hfin⟩

theorem not_commute_rootSL2_of_not_commute_TwE6 (hp2 : p ≠ 2) (he : 1 ≤ e) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .twistedE6 0 p e) {c₂ : twistedE6Group p e}
    (hn : ¬ ∀ r ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6), c₂ * r = r * c₂) :
    ¬ ∀ A : SL2 kE6, LeviE6.phiE6 p e c₂ * rootSL2 .E6 kE6 thetaE6 A =
      rootSL2 .E6 kE6 thetaE6 A * LeviE6.phiE6 p e c₂ := by
  intro hA
  apply hn
  have hθl := stdRank_mem_longestFundamental_TwE6 (p := p) (e := e) isRoot_thetaE6
    rho_thetaE6'
  refine commute_of_commutator_central _
    (le_of_eq (commutator_eq_of_mem_longestFundamental (t := .twistedE6) hp2 hq trivial hadm
      hθl).symm) c₂ fun r hr => ?_
  have hmem : LeviE6.phiE6 p e r ∈ rootRankOneGroup .E6 kE6 thetaE6 :=
    phi_map_stdRank_le hp2 he isRoot_thetaE6 rho_thetaE6' (Subgroup.mem_map_of_mem _ hr)
  obtain ⟨A, hAr⟩ := hmem
  apply ker_twistedE6Phi_le_center p e kE6
  rw [MonoidHom.mem_ker]
  show LeviE6.phiE6 p e (c₂ * r * c₂⁻¹ * r⁻¹) = 1
  simp only [map_mul, map_inv]
  rw [← hAr]
  exact mul_inv_eq_one.2 (by rw [mul_inv_eq_iff_eq_mul]; exact hA A)

theorem a2_normalized_TwE6 (hadm : StatedLieAdmissible .twistedE6 0 p e) (hU : A2UnitaryTw p e)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {R₂ : Subgroup (twistedE6Group p e)}
    (hR₂ : R₂ ∈ longestFundamental (twistedE6Datum p e)) {c₁ c₂ : twistedE6Group p e}
    (hc₁ : c₁ ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6)) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hcomm : c₁ * c₂ = c₂ * c₁)
    (hn : ¬ ∀ r ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6), c₂ * r = r * c₂) :
    (∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (twistedE6Datum p e) (proj thetaE6)) R₂) ∨
    ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
      (stdRankOne (twistedE6Datum p e) (proj thetaE6)) R₂ := by
  have he : 1 ≤ e := Nat.one_le_iff_ne_zero.2 (by
    rintro rfl
    norm_num at hq)
  have hsingle : Generic.FundamentalSingleClass .twistedE6 (twistedE6Datum p e) :=
    fundamentalSingleClass .twistedE6 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (twistedE6Datum p e) (proj thetaE6) ∈
      Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e) :=
    ⟨1, proj thetaE6, Or.inl (isLongestRoot_twistedDatum_proj (frobQ p e) isRoot_thetaE6
      rho_thetaE6'), (Generic.conjSub_one _).symm⟩
  obtain ⟨h, hh⟩ := hsingle _ hθmem R₂ (longestFundamental_subset .twistedE6 _ hR₂)
  have hd₂ : h⁻¹ * c₂ * h ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6) :=
    Generic.mem_conjSub_iff.1 (hh ▸ hc₂)
  have hord : orderOf (h⁻¹ * c₂ * h) = 2 := by
    have := a2_orderOf_conj_eq_two ho₂ h⁻¹
    simpa using this
  have z1 := phi_involution hp2 he hadm isRoot_thetaE6 rho_thetaE6' hc₁ ho₁
  have z2 := phi_involution hp2 he hadm isRoot_thetaE6 rho_thetaE6' hd₂ hord
  simp only [map_mul, map_inv] at z2
  have hgc : LeviE6.phiE6 p e h * signDiagE6 kE6 thetaE6 * (LeviE6.phiE6 p e h)⁻¹ =
      LeviE6.phiE6 p e c₂ := by
    rw [← z2]
    group
  have hcd : LeviE6.phiE6 p e c₂ * signDiagE6 kE6 thetaE6 =
      signDiagE6 kE6 thetaE6 * LeviE6.phiE6 p e c₂ := by
    have := congrArg (LeviE6.phiE6 p e) hcomm
    rw [map_mul, map_mul, z1] at this
    exact this.symm
  have hc2 : LeviE6.phiE6 p e c₂ * LeviE6.phiE6 p e c₂ = 1 := by
    have h1 := ((orderOf_eq_prime_iff (p := 2)).1 ho₂).1
    have h2 := congrArg (LeviE6.phiE6 p e) h1
    simpa [sq] using h2
  rcases exists_split_or_anti_TwE6 hp2 he hc2 hcd hgc
    (not_commute_rootSL2_of_not_commute_TwE6 hp2 he hq hadm hn) with ⟨x, hxd, hxy⟩ | hanti
  · exact Or.inl (linearBlockStandardPair_of_split_TwE6 hp2 he hq hadm hc₁ ho₁ hR₂ hc₂ ho₂ hxd hxy)
  · exact Or.inr (hU hadm hp2 hq R₂ c₂ hR₂ hc₂ ho₂ hcd hn hanti)

theorem a2BranchLeft_twistedE6_aux (hadm : StatedLieAdmissible .twistedE6 0 p e)
    (hU : A2UnitaryTw p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    {R₁ R₂ : Subgroup (twistedE6Group p e)}
    (h₁ : R₁ ∈ longestFundamental (twistedE6Datum p e))
    (h₂ : R₂ ∈ longestFundamental (twistedE6Datum p e))
    {c₁ c₂ : twistedE6Group p e} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hcomm : c₁ * c₂ = c₂ * c₁)
    (hn : ¬ ∀ r ∈ R₁, c₂ * r = r * c₂) :
    (∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂ := by
  have hsingle : Generic.FundamentalSingleClass .twistedE6 (twistedE6Datum p e) :=
    fundamentalSingleClass .twistedE6 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (twistedE6Datum p e) (proj thetaE6) ∈
      Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e) :=
    ⟨1, proj thetaE6, Or.inl (isLongestRoot_twistedDatum_proj (frobQ p e) isRoot_thetaE6
      rho_thetaE6'), (Generic.conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := hsingle _ hθmem R₁ (longestFundamental_subset .twistedE6 _ h₁)
  have hR₁ : R₁ = (stdRankOne (twistedE6Datum p e) (proj thetaE6)).map
      (MulAut.conj g).toMonoidHom := hg
  obtain ⟨r₁, hr₁, rfl⟩ : ∃ r ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6),
      c₁ = g * r * g⁻¹ := by
    rw [hR₁] at hc₁
    obtain ⟨r, hr, hrc⟩ := hc₁
    exact ⟨r, hr, hrc.symm⟩
  have hor₁ : orderOf r₁ = 2 := by
    have := a2_orderOf_conj_eq_two ho₁ g⁻¹
    simpa [mul_assoc] using this
  set R₂' := R₂.map (MulAut.conj g⁻¹).toMonoidHom with hR₂'
  set c₂' : twistedE6Group p e := g⁻¹ * c₂ * g with hc₂'
  have hR₂'l : R₂' ∈ longestFundamental (twistedE6Datum p e) :=
    map_conj_mem_longestFundamental g⁻¹ h₂
  have hc₂'R : c₂' ∈ R₂' := ⟨c₂, hc₂, by simp [hc₂']⟩
  have ho₂' : orderOf c₂' = 2 := by
    have := a2_orderOf_conj_eq_two ho₂ g⁻¹
    simpa [hc₂'] using this
  have hcomm' : r₁ * c₂' = c₂' * r₁ := by
    have h : g * r₁ * g⁻¹ * c₂ = c₂ * (g * r₁ * g⁻¹) := hcomm
    calc r₁ * c₂' = g⁻¹ * (g * r₁ * g⁻¹ * c₂) * g := by simp [hc₂']; group
      _ = g⁻¹ * (c₂ * (g * r₁ * g⁻¹)) * g := by rw [h]
      _ = c₂' * r₁ := by simp [hc₂']; group
  have hn' : ¬ ∀ r ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6), c₂' * r = r * c₂' := by
    intro h
    apply hn
    intro r hr
    rw [hR₁] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    have h' := h r' hr'
    calc c₂ * (MulAut.conj g).toMonoidHom r' = g * (c₂' * r') * g⁻¹ := by
          simp [hc₂', MulAut.conj_apply]; group
      _ = g * (r' * c₂') * g⁻¹ := by rw [h']
      _ = (MulAut.conj g).toMonoidHom r' * c₂ := by
          simp [hc₂', MulAut.conj_apply]; group
  rcases a2_normalized_TwE6 hadm hU hp2 hq hR₂'l hr₁ hc₂'R hor₁ ho₂' hcomm' hn' with
    ⟨W, hW⟩ | ⟨W, hW⟩
  · left
    have h := linearBlockStandardPair_map_conj hW g
    have e2 : R₂'.map (MulAut.conj g).toMonoidHom = R₂ := by
      have := a2_map_conj_inv_map_conj g⁻¹ R₂
      rwa [inv_inv] at this
    rw [e2, ← hR₁] at h
    exact ⟨_, h⟩
  · right
    have h := CFSG.ClassicalInvolution.Models.unitaryBlockStandardPair_map hW
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have e2 : R₂'.map (MulAut.conj g).toMonoidHom = R₂ := by
      have := a2_map_conj_inv_map_conj g⁻¹ R₂
      rwa [inv_inv] at this
    rw [e2, ← hR₁] at h
    exact ⟨_, h⟩

theorem a2BranchLeft_twistedE6 (hadm : StatedLieAdmissible .twistedE6 0 p e)
    (hU : A2UnitaryTw p e) : A2BranchLeft p .twistedE6 0 e :=
  fun hp2 hq _ h₁ _ h₂ _ _ hc₁ hc₂ ho₁ ho₂ hcomm hn =>
    a2BranchLeft_twistedE6_aux hadm hU hp2 hq h₁ h₂ hc₁ hc₂ ho₁ ho₂ hcomm hn

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
