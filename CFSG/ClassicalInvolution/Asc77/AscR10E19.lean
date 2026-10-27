module

public import CFSG.ClassicalInvolution.Asc77.AscR10E9
public import CFSG.ClassicalInvolution.Asc77.AscR10E5
public import CFSG.ClassicalInvolution.Asc77.AscR10E17
public import CFSG.ClassicalInvolution.Asc77.AscR10E2
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2TwPair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2TwMain
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryTwMain
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2InterfaceTw
public import CFSG.ClassicalInvolution.Asc77.AscR10E18

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.Levi



open CFSG.ClassicalInvolution.Asc77.T3CII (GenSq eq_of_map_eq_of_genSq
  commute_of_map_commute_of_genSq)

section Iface

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

variable {p e : ℕ} [Fact p.Prime]

@[expose] def A2UnitaryTw_three (p e : ℕ) [Fact p.Prime] : Prop :=
  StatedLieAdmissible .twistedE6 0 p e → p ≠ 2 → p ^ e = 3 →
    ∀ (R₂ : Subgroup (twistedE6Group p e)) (c₂ : twistedE6Group p e),
      R₂ ∈ longestFundamental (twistedE6Datum p e) → c₂ ∈ R₂ → orderOf c₂ = 2 →
      LeviE6.phiE6 p e c₂ * signDiagE6 (LeviE6.E6Closure p e) thetaE6 =
        signDiagE6 (LeviE6.E6Closure p e) thetaE6 * LeviE6.phiE6 p e c₂ →
      ¬ (∀ r ∈ stdRankOne (twistedE6Datum p e) (proj thetaE6), c₂ * r = r * c₂) →
      (∃ v ∈ h1E6 (LeviE6.E6Closure p e),
        v * LeviE6.phiE6 p e c₂ * v⁻¹ = signDiagE6 (LeviE6.E6Closure p e) deltaE6 ∧
        ∃ m ∈ parabolicLevi .E6 (LeviE6.E6Closure p e) JE6,
          LeviE6.frobE6 p e v * v⁻¹ = m * rootSL2 .E6 (LeviE6.E6Closure p e) thetaE6 WSL) →
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
        (stdRankOne (twistedE6Datum p e) (proj thetaE6)) R₂

end Iface

section Unit

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Universal CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule

variable {p e : ℕ} [Fact p.Prime]

local notation "kE6" => LeviE6.E6Closure p e

theorem a2UnitaryImageTw_three (hadm : StatedLieAdmissible .twistedE6 0 p e) (hp2 : p ≠ 2)
    (hq3 : p ^ e = 3) {R₂ : Subgroup (twistedE6Group p e)} {c₂ : twistedE6Group p e}
    (hR₂ : R₂ ∈ longestFundamental (twistedE6Datum p e)) (hc₂ : c₂ ∈ R₂) (ho : orderOf c₂ = 2)
    (hv : ∃ v ∈ h1E6 kE6, v * LeviE6.phiE6 p e c₂ * v⁻¹ = signDiagE6 kE6 deltaE6 ∧
      ∃ m ∈ parabolicLevi .E6 kE6 JE6,
        LeviE6.frobE6 p e v * v⁻¹ = m * rootSL2 .E6 kE6 thetaE6 WSL) :
    ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
      ((stdRankOne (twistedE6Datum p e) (proj thetaE6)).map (LeviE6.phiE6 p e))
      (R₂.map (LeviE6.phiE6 p e)) := by
  obtain ⟨v, hv, hd, m, hm, hcoc⟩ := hv
  have he : 1 ≤ e := Nat.one_le_iff_ne_zero.2 (by
    rintro rfl
    norm_num at hq3)
  have hne : NeZero e := ⟨by omega⟩
  have h2e : NeZero (2 * e) := ⟨by omega⟩
  have hcardE : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (NeZero.ne _), pow_mul' p 2 e]
  have hFc := (mem_fixedPointsIn.1 (twistedE6Phi_mem_fixedPointsIn p e hp2 he c₂)).2
  obtain ⟨α, hαinj, hαadj, hαF, hαblk, hαneg⟩ :=
    exists_unitary_alpha_Tw hp2 he hFc hv hd hm hcoc
  have hαR : α.range ≤ fixedPointsIn (adjointGroup TwistTag.E6.tag kE6) (LeviE6.frobE6 p e) := by
    rintro _ ⟨y, rfl⟩
    exact mem_fixedPointsIn.2 ⟨hαadj y, hαF y⟩
  have hαΦ : α.range ≤ (LeviE6.phiE6 p e).range := by
    have hr := range_twistedE6Phi p e hp2 he
    rw [show (LeviE6.phiE6 p e).range = _ from hr]
    exact (CFSG.ClassicalInvolution.Asc77.T3CII.su_range_le_commutator_odd hcardE hp2 α).trans
        (Subgroup.commutator_mono hαR hαR)
  have hθl := stdRank_mem_longestFundamental_TwE6 (p := p) (e := e) isRoot_thetaE6 rho_thetaE6'
  have hθf := longestFundamental_subset .twistedE6 _ hθl
  have hR₂f := longestFundamental_subset .twistedE6 _ hR₂
  have hB12 : (B12 (GaloisField p (2 * e)) p e).map α =
      (stdRankOne (twistedE6Datum p e) (proj thetaE6)).map (LeviE6.phiE6 p e) := by
    have hcard := natCard_map_phi_fundamental hp2 hadm hθf
    have : Finite ↥((stdRankOne (twistedE6Datum p e) (proj thetaE6)).map (LeviE6.phiE6 p e)) :=
      Nat.finite_of_card_ne_zero (by
        rw [hcard]
        have h5 : 1 < p ^ e := by omega
        have h6 : 0 < (p ^ e) ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero h5)
        exact Nat.mul_ne_zero (by omega) h6.ne')
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, ⟨A, rfl⟩, rfl⟩
      obtain ⟨A', hA'⟩ := hαblk A
      rw [phi_stdRankE6_eq hp2 he]
      exact ⟨⟨A', hA'.symm⟩, hαΦ ⟨_, rfl⟩⟩
    · rw [hcard, Subgroup.card_map_of_injective hαinj, natCard_B12 hcardE]
  obtain ⟨g, hg⟩ := hαΦ ⟨swapElt (GaloisField p (2 * e)) p e, rfl⟩
  have hB23' : (B23 (GaloisField p (2 * e)) p e).map α =
      ((stdRankOne (twistedE6Datum p e) (proj thetaE6)).map (MulAut.conj g).toMonoidHom).map
        (LeviE6.phiE6 p e) := by
    rw [map_conj_map_of_hom, hg, ← hB12, ← map_conj_swapElt_B12 (GaloisField p (2 * e)) p e,
      Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hR₃ := map_conj_mem_longestFundamental g hθl
  have hR₃f := longestFundamental_subset .twistedE6 _ hR₃
  have hc : LeviE6.phiE6 p e c₂ ∈
      ((stdRankOne (twistedE6Datum p e) (proj thetaE6)).map (MulAut.conj g).toMonoidHom).map
        (LeviE6.phiE6 p e) := by
    rw [← hB23']
    exact ⟨_, ⟨suNegOne (GaloisField p (2 * e)) p e, rfl⟩, hαneg⟩
  obtain ⟨c₃, hc₃, hc₃Φ⟩ := hc
  have hΦc₂ : LeviE6.phiE6 p e c₂ ≠ 1 := fun h1 => by
    have := phi_injOn_fundamental hadm hR₂f c₂ hc₂ h1
    rw [this, orderOf_one] at ho
    omega
  have ho₃ : orderOf c₃ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have h2 : LeviE6.phiE6 p e (c₃ ^ 2) = 1 := by
        have ho_sq : c₂ ^ 2 = 1 := by
          have := pow_orderOf_eq_one c₂
          rwa [ho] at this
        rw [map_pow, hc₃Φ, ← map_pow, ho_sq, map_one]
      exact phi_injOn_fundamental hadm hR₃f _ (Subgroup.pow_mem _ hc₃ 2) h2
    · intro h1
      exact hΦc₂ (by rw [← hc₃Φ, h1, map_one])
  have hRR := eq_of_mem_longestFundamental_TwE6_three hp2 he hq3 hadm hR₃ hR₂ hc₃ hc₂ ho₃ ho hc₃Φ
  refine ⟨α.range, unitaryBlockStandardPair_of_normalized ?_ rfl hB12 ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff α).mpr hαinj]
    exact bot_le
  · rw [hB23', hRR]

theorem a2UnitaryTw_three : A2UnitaryTw_three p e := by
  intro hadm hp2 hq3 R₂ c₂ hR₂ hc₂ ho _ _ hv
  have hne : NeZero e := ⟨by rintro rfl; simp at hq3⟩
  have h2e : NeZero (2 * e) := ⟨by have := NeZero.ne e; omega⟩
  have hcard : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (NeZero.ne _), pow_mul' p 2 e]
  have : Finite (twistedE6Group p e) := finite_twistedE6Group_three
  have hθl := stdRank_mem_longestFundamental_TwE6 (p := p) (e := e) isRoot_thetaE6 rho_thetaE6'
  exact exists_uni_of_map_three hq3 hcard (LeviE6.phiE6 p e)
    (ker_twistedE6Phi_le_center p e kE6) (ker_twistedE6Phi_sq_three hq3 kE6)
    (genSq_of_mem_longestFundamental3 (t := .twistedE6) hq3 trivial hadm (by decide)
        (by decide) hθl)
    (genSq_of_mem_longestFundamental3 (t := .twistedE6) hq3 trivial hadm (by decide)
        (by decide) hR₂)
    (a2UnitaryImageTw_three hadm hp2 hq3 hR₂ hc₂ ho hv)

end Unit

section Main

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

variable {p e : ℕ} [Fact p.Prime]

local notation "kE6" => LeviE6.E6Closure p e

theorem a2_normalized_TwE6_three (hadm : StatedLieAdmissible .twistedE6 0 p e)
    (hU : A2UnitaryTw_three p e)
    (hp2 : p ≠ 2) (hq3 : p ^ e = 3) {R₂ : Subgroup (twistedE6Group p e)}
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
    norm_num at hq3)
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
    (not_commute_rootSL2_of_not_commute_TwE6_three hp2 he hq3 hadm hn) with ⟨x, hxd, hxy⟩ | hanti
  · exact Or.inl
      (linearBlockStandardPair_of_split_TwE6_three hp2 he hq3 hadm hc₁ ho₁ hR₂ hc₂ ho₂ hxd hxy)
  · exact Or.inr (hU hadm hp2 hq3 R₂ c₂ hR₂ hc₂ ho₂ hcd hn hanti)

theorem a2BranchLeft_twistedE6_aux_three (hadm : StatedLieAdmissible .twistedE6 0 p e)
    (hU : A2UnitaryTw_three p e) (hp2 : p ≠ 2) (hq3 : p ^ e = 3)
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
  rcases a2_normalized_TwE6_three hadm hU hp2 hq3 hR₂'l hr₁ hc₂'R hor₁ ho₂' hcomm' hn' with
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

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
