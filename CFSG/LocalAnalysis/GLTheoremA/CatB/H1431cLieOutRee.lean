module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutCharTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutRee

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Lang.Coordinator CFSG.Sporadic.Schreier.Tits
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.ComponentClassification.CatLeaf
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (reeGamma_F4_simple_model
  nonempty_fixSubgroup_reeGammaFieldAut_equiv exists_conj_mul_reeGammaFieldAut_of_not_inner
  reeTitsModel_of_lieModel_twistedF4 exists_equiv_reeGamma_F4
  not_three_dvd_card_of_lieModel_suzuki card_eq_of_lieModel_tits
  not_mem_range_conj_of_not_mem_innAutDerived)

open CFSG.HardMathSupport.Dickson.Sec6 (FamReeF4 FamSz FamTits)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions
    large_Ree_full_inner_field_automorphism_normal_form)

variable {T Pc : TauCeti.CFSGIndex → Prop} {tm tf tN : ℕ}

section Family


theorem typeLayer_reeGammaFieldAut_F4 (hD : LieSOutType T tm tf tN) {a b : ℕ} (F : Type) [Field F]
    [Finite F] [CharP F ReeTag.F4.prime] (σ : F ≃+* F)
    (hk : Nat.card ↥(fixSubfield σ) = 2 ^ (2 * b + 1))
    (hfix : ((ReeTag.F4.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.F4.reeGamma F a).subtype =
        (ReeTag.F4.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype)) :
    TypeLayer T (ReeTag.F4.reeGammaFieldAut F a σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP ↥(fixSubfield σ) ReeTag.F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hk
  obtain ⟨eC⟩ := nonempty_fixSubgroup_reeGammaFieldAut_equiv σ hfix
  by_cases hb : b = 0
  · subst hb
    have hk2 : Nat.card ↥(fixSubfield σ) = 2 := by simpa using hk
    obtain ⟨c⟩ := nonempty_commutator_reeGamma_tits hk2
    obtain ⟨cc⟩ := nonempty_commutator_mulEquiv eC
    haveI : Nontrivial titsD := titsD_simple.toNontrivial
    exact typeLayer_of_fixed_commutator_equiv _ (cc.trans c) titsD_simple
      (exists_noncomm_of_center_bot titsD_center) fun h => by
        have h1 := hD.card_eq h
        rw [card_titsD] at h1
        exact hD.ord.not_dvd_17971200 ⟨1, by omega⟩
  · obtain ⟨hsimp, hnab, hX⟩ :=
      reeGamma_F4_simple_model (Nat.one_le_iff_ne_zero.2 hb) (fixSubfield σ) hk
    exact typeLayer_of_fixed_equiv _ eC hsimp hnab fun h =>
      absurd (hD.det h hX).1 (by decide)

theorem typeLayer_reeGamma_F4 (hD : LieSOutType T tm tf tN) {a : ℕ} (ha : 1 ≤ a) (F : Type)
    [Field F] [Finite F] [CharP F ReeTag.F4.prime] (hK : Nat.card F = 2 ^ (2 * a + 1))
    (β' : MulAut ↥(ReeTag.F4.reeGamma F a)) (hβ3 : β' ^ 3 = 1)
    (hβinn : β' ∉ inner ↥(ReeTag.F4.reeGamma F a)) : TypeLayer T β' False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, β, hβord, hxβ⟩ := exists_conj_mul_reeGammaFieldAut_of_not_inner ha F hK β' hβ3 hβinn
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK Nat.prime_three
    β hβord β' hβ3 ⟨x, hxβ⟩
  obtain ⟨b, hbp, hbcard, hfix⟩ :=
    largeRee_fixed_data_of_odd hK Nat.prime_three (by norm_num) β hβord
  refine typeLayer_of_conj_pow (r := 1) (j := 1) (δ := (MulAut.conj g)⁻¹) (by simp) ?_
    (typeLayer_reeGammaFieldAut_F4 hD F β hbcard hfix)
  rw [pow_one, hg]
  group

theorem lieSOut_reeF4 (hD : LieSOutType T tm tf tN) : TypeOuterAt T Pc FamReeF4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | reeF4 m =>
    exfalso
    have hR := reeTitsModel_of_lieModel_twistedF4
      (CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_reeF4 m hv e)
    have hm1 : 1 ≤ m := by
      have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      simpa only [TauCeti.LieTypeIndex.inStandardRange_iff] using h
    obtain ⟨F, _, _, _, hFcard, ⟨e'⟩⟩ := exists_equiv_reeGamma_F4 hR
    haveI : Finite ↥(ReeTag.F4.reeGamma F m) := Finite.of_equiv S e'.toEquiv
    have hβ3 : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    have hβinn : MulAut.congr e' α ∉ inner ↥(ReeTag.F4.reeGamma F m) := fun hin =>
      not_mem_range_conj_of_not_mem_innAutDerived hα
        ((congr_mem_inner_iff_of_equiv e' α).mp hin)
    exact hp.apply (typeLayer_congr e' (typeLayer_reeGamma_F4 hD hm1 F hFcard _ hβ3 hβinn))
  | _ => exact hF.elim

theorem lieSOut_sz (hD : LieSOutType T tm tf tN) : TypeOuterAt T Pc FamSz := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | suzuki m =>
    exfalso
    have hm1 : 1 ≤ m := by
      have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      simpa only [TauCeti.LieTypeIndex.inStandardRange_iff] using h
    exact not_three_dvd_card_of_lieModel_suzuki hm1
      (CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_suzuki m hv e)
      (hD.ord.three_dvd.trans (hp.card_dvd hD.card_eq))
  | _ => exact hF.elim

theorem lieSOut_tits (hD : LieSOutType T tm tf tN) : TypeOuterAt T Pc FamTits := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | tits =>
    exfalso
    have h := hp.card_dvd hD.card_eq
    rw [card_eq_of_lieModel_tits (CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_tits hv e)]
      at h
    exact absurd h hD.ord.not_dvd_17971200
  | _ => exact hF.elim

end Family

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end

