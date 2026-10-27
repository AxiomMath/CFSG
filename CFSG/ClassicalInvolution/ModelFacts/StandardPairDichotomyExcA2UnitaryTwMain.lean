module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryTwHom
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyLift
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyCenter
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
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
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Universal CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule

variable {p e : ℕ} [Fact p.Prime]

local notation "kE6" => LeviE6.E6Closure p e

section Kernel

theorem phiE6_ker_pow_three (x : twistedE6Group p e) (hx : x ∈ (LeviE6.phiE6 p e).ker) :
    x ^ 3 = 1 := by
  have hx1 : e6IsogenyFixed (frobQ p e) x = 1 := by
    apply baseChangeGL_injective (algebraMap (GaloisField p (2 * e)) kE6)
    rw [map_one]
    exact hx
  have hker : (x : ↥(e6Data_valid.minGroup (GaloisField p (2 * e)))) ∈
      (e6IsogenyT (GaloisField p (2 * e))).ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hx1
  have hc := ker_e6IsogenyT_le_center (GaloisField p (2 * e)) hker
  exact Subtype.ext (A2Isogeny.center_pow_three_e6 _ hc)

private theorem finite_twistedE6Group : Finite (twistedE6Group p e) := by
  have : Finite ↥(e6Data_valid.minGroup (GaloisField p (2 * e))) :=
    ChevAut.finite_minGroup e6Data_valid (GaloisField p (2 * e))
  exact Subtype.finite

theorem phiE6_ker_odd : Odd (Nat.card (LeviE6.phiE6 p e).ker) := by
  have : Finite (twistedE6Group p e) := finite_twistedE6Group
  by_contra hodd
  have h2 : 2 ∣ Nat.card (LeviE6.phiE6 p e).ker :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have h4 : orderOf x ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (phiE6_ker_pow_three x.1 x.2))
  rw [hx] at h4
  omega

end Kernel

section Cardinality

theorem natCard_fundamental_twE6 (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .twistedE6 0 p e)
    {R : Subgroup (twistedE6Group p e)}
    (hR : R ∈ Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e)) :
    Nat.card R = p ^ e * ((p ^ e) ^ 2 - 1) := by
  obtain ⟨φ⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .twistedE6) trivial hadm
    (by decide) (by decide) hR
  have hne : NeZero e := ⟨by have := hadm.2.1; omega⟩
  have φ' : ↥R ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p e) := φ
  rw [Nat.card_congr φ'.toEquiv, card_specialLinearGroup_fin_two,
    GaloisField.card p e (NeZero.ne e)]

theorem natCard_map_phi_fundamental (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .twistedE6 0 p e)
    {R : Subgroup (twistedE6Group p e)}
    (hR : R ∈ Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e)) :
    Nat.card (R.map (LeviE6.phiE6 p e)) = p ^ e * ((p ^ e) ^ 2 - 1) := by
  have hinj : Function.Injective ((LeviE6.phiE6 p e).comp R.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (phi_injOn_fundamental hadm hR x.1 x.2 hx)
  have hrange : ((LeviE6.phiE6 p e).comp R.subtype).range = R.map (LeviE6.phiE6 p e) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, ← natCard_fundamental_twE6 hp2 hadm hR]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Cardinality

section Main

theorem a2UnitaryImageTw (hadm : StatedLieAdmissible .twistedE6 0 p e) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ e) {R₂ : Subgroup (twistedE6Group p e)} {c₂ : twistedE6Group p e}
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
    norm_num at hq)
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
    exact (su_range_le_commutator hcardE hq α).trans (Subgroup.commutator_mono hαR hαR)
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
  have hRR := eq_of_mem_longestFundamental_TwE6 hp2 he hq hadm hR₃ hR₂ hc₃ hc₂ ho₃ ho hc₃Φ
  refine ⟨α.range, unitaryBlockStandardPair_of_normalized ?_ rfl hB12 ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff α).mpr hαinj]
    exact bot_le
  · rw [hB23', hRR]

theorem a2UnitaryTw : A2UnitaryTw p e := by
  intro hadm hp2 hq R₂ c₂ hR₂ hc₂ ho _ _ hv
  have hne : NeZero e := ⟨by rintro rfl; simp at hq⟩
  have h2e : NeZero (2 * e) := ⟨by have := NeZero.ne e; omega⟩
  have hcard : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (NeZero.ne _), pow_mul' p 2 e]
  have : Finite (twistedE6Group p e) := finite_twistedE6Group
  have hθl := stdRank_mem_longestFundamental_TwE6 (p := p) (e := e) isRoot_thetaE6 rho_thetaE6'
  exact exists_uni_of_map_odd hp2 hcard hq (LeviE6.phiE6 p e)
    (ker_twistedE6Phi_le_center p e kE6) phiE6_ker_odd
    (commutator_eq_of_mem_longestFundamental (t := .twistedE6) hp2 hq trivial hadm hθl)
    (commutator_eq_of_mem_longestFundamental (t := .twistedE6) hp2 hq trivial hadm hR₂)
    (a2UnitaryImageTw hadm hp2 hq hR₂ hc₂ ho hv)

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
