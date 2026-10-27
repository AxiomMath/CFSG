module

public import CFSG.GF2Type.Smith1979.CaseI25A0
public import CFSG.GF2Type.Smith1979.CaseI25IdxFour
public import CFSG.GF2Type.Smith1979.CharTwoLayer
public import CFSG.GF2Type.Smith1979.ParrottCharTwo
public import CFSG.GF2Type.Smith1979.CaseI25FilterMain
public import CFSG.GF2Type.Smith1979.CaseITwoCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44ReifartTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case25

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2
open CFSG.Open CFSG.ComponentClassification
open CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.TwoFi22
  CFSG.EvenSporadicStandard.TwoFi22.DS81
open CFSG.Assembly (InCatalog KProper)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def U43NoFaithfulTwelve : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V], Module.finrank (ZMod 2) V = 12 →
    ∀ (E : Subgroup (V ≃ₗ[ZMod 2] V)), CFSG.Open.StatedClassicalModel E .PSU 4 3 1 → False

@[expose] def FilterXInCatalog : Prop :=
  ∀ {X : Type} [Group X] [IsSimpleGroup X], InCatalog X → (∃ a b : X, a * b ≠ b * a) →
    Nat.card X ∣ 2 ^ 31 * 3 ^ 8 * 5 ^ 2 * 7 ^ 2 * 11 * 17 * 31 → 25920 ∣ Nat.card X →
    2 ^ 7 ∣ Nat.card X → ¬ 2 ^ 9 ∣ Nat.card X →
      Nonempty (X ≃* alternatingGroup (Fin 10)) ∨ Nonempty (X ≃* alternatingGroup (Fin 11)) ∨
        CFSG.Open.StatedClassicalModel X .PSU 4 3 1

section FilterBinders

theorem filterXInCatalog_of_bridge
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Assembly.InCatalog CFSG.Blueprint.Catalog) :
    FilterXInCatalog :=
  fun hX hnonab hord h1 h2 h3 => filter_X_of_inCatalog hbridge hX hnonab hord h1 h2 h3

end FilterBinders

section Shape

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def toMbar (S : Setting G) : S.M →* S.Mbar := S.ρ.rangeRestrict

theorem toMbar_surjective (S : Setting G) : Function.Surjective (toMbar S) :=
  S.ρ.rangeRestrict_surjective

theorem ker_toMbar (S : Setting G) : (toMbar S).ker = S.Q :=
  (MonoidHom.ker_rangeRestrict S.ρ).trans S.ker_ρ

theorem pCore_three_Mbar_eq (S : Setting G) (hO : Nat.card (timmesfeldOddCore S.Mbar) = 3) :
    CFSG.pCore 3 S.Mbar = timmesfeldOddCore S.Mbar := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · refine S5.le_timmesfeldOddCore CFSG.pCore_normal ?_
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := S.Mbar)).exists_card_eq
    rw [hk]
    exact (by decide : Odd 3).pow
  · refine le_sSup ⟨S5.timmesfeldOddCore_normal _, ?_⟩
    exact IsPGroup.of_card (n := 1) (by rw [hO, pow_one])

theorem comap_pCore_three_eq (S : Setting G) {Ob : Subgroup S.Mbar}
    (hOb : Ob = CFSG.pCore 3 S.Mbar) {T : Subgroup S.M} [T.Normal] (hT : T = S.Q) :
    (CFSG.pCore 3 (S.M ⧸ T)).comap (QuotientGroup.mk' T) = Ob.comap (toMbar S) := by
  subst hT
  have hmap := CFSG.pCore_map_iso 3 S.quotientEquivMbar
  rw [← hOb] at hmap
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_comap, ← hmap, Subgroup.mem_map_equiv]
  have : S.quotientEquivMbar.symm (toMbar S x) = (QuotientGroup.mk' S.Q) x := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  rw [this]

theorem card_comap_toMbar (S : Setting G) (N : Subgroup S.Mbar) :
    Nat.card (N.comap (toMbar S)) = Nat.card N * Nat.card S.Q := by
  have hsurj : Function.Surjective (toMbar S) := toMbar_surjective S
  have h1 := Subgroup.card_mul_index (N.comap (toMbar S))
  rw [Subgroup.index_comap_of_surjective _ hsurj] at h1
  have h2 := Subgroup.card_ker_mul_card_range (toMbar S)
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, ker_toMbar] at h2
  have h3 := Subgroup.card_mul_index N
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, ← h2, ← h3]
  ring

theorem parrottShape_of_data (S : Setting G) (hw : S.width = 6) (E Ob : Subgroup S.Mbar)
    (hEn : E.Normal) (hOb : Ob = CFSG.pCore 3 S.Mbar) (hO : Nat.card Ob = 3)
    (hZ : (center E).map E.subtype = Ob)
    (hX : CFSG.Open.StatedClassicalModel (E ⧸ center E) .PSU 4 3 1)
    (hi : E.index = 2) : TwoFi22.ParrottShape S.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective (toMbar S) := toMbar_surjective S
  have hO2 : TwoFi22.O2In S.M = S.Q.map S.M.subtype := by
    rw [Reifart.O2In_eq, ← S.Q_eq_pCore]
  have hO23 : TwoFi22.O23In S.M = (Ob.comap (toMbar S)).map S.M.subtype := by
    rw [Reifart.O23In_eq]
    haveI : (CFSG.pCore 2 ↥S.M).Normal := CFSG.pCore_normal
    exact congrArg (Subgroup.map S.M.subtype)
      (comap_pCore_three_eq S hOb (T := CFSG.pCore 2 ↥S.M) S.Q_eq_pCore.symm)
  have hObE : Ob ≤ E := hZ ▸ map_subtype_le _
  obtain ⟨eK, heK⟩ : ∃ eK : ↥(E.comap (toMbar S)) ≃* ↥((E.comap (toMbar S)).map S.M.subtype),
      ∀ y, ((eK y : ↥((E.comap (toMbar S)).map S.M.subtype)) : G) =
        (((y : ↥(E.comap (toMbar S))) : S.M) : G) :=
    ⟨(E.comap (toMbar S)).equivMapOfInjective S.M.subtype S.M.subtype_injective, fun y => rfl⟩
  have hcen : ∀ y : E, y ∈ center E ↔ (y : S.Mbar) ∈ Ob := by
    intro y
    constructor
    · intro h
      exact hZ ▸ (⟨y, h, rfl⟩ : (y : S.Mbar) ∈ (center E).map E.subtype)
    · intro h
      obtain ⟨z, hz, hzy⟩ := (hZ ▸ h : (y : S.Mbar) ∈ (center E).map E.subtype)
      have hzy' : z = y := Subtype.ext hzy
      exact hzy' ▸ hz
  obtain ⟨π₀, hπ₀s, hπ₀⟩ : ∃ π₀ : ↥(E.comap (toMbar S)) →* (E ⧸ center E),
      Function.Surjective π₀ ∧ ∀ k : ↥(E.comap (toMbar S)),
        π₀ k = 1 ↔ ((k : S.M)) ∈ Ob.comap (toMbar S) :=
    ⟨(QuotientGroup.mk' (center E)).comp ((toMbar S).subgroupComap E),
      (QuotientGroup.mk'_surjective _).comp
        (MonoidHom.subgroupComap_surjective_of_surjective _ _ hsurj),
      fun k => (QuotientGroup.eq_one_iff (N := center E) _).trans (hcen _)⟩
  unfold TwoFi22.ParrottShape
  refine ⟨?_, ?_, ?_, (E.comap (toMbar S)).map S.M.subtype, map_subtype_le _, ?_, ?_, ?_,
    ⟨E ⧸ center E, inferInstance, π₀.comp eK.symm.toMonoidHom, hπ₀s.comp eK.symm.surjective, ?_,
      hX⟩, ?_⟩
  · rw [hO2]
    exact Reifart.isExtraspecial_of_mulEquiv
      (S.Q.equivMapOfInjective S.M.subtype S.M.subtype_injective)
      (CFSG.isExtraspecialPGroup_iff_isExtraspecial.mp S.extraspecial)
  · rw [hO2, card_map_of_injective S.M.subtype_injective, S.card_Q_eq, hw]
  · intro x hx
    obtain ⟨hxM, hxc⟩ := mem_inf.mp hx
    rw [hO2]
    exact S.mem_QG_of_commute hxM fun y hy =>
      (mem_centralizer_iff.mp hxc y (by rw [hO2]; exact hy)).symm
  · rw [Reifart.subgroupOf_map_subtype_eq]
    exact hEn.comap _
  · rw [hO23]
    exact map_mono (comap_mono hObE)
  · rw [hO23, hO2, card_map_of_injective S.M.subtype_injective,
      card_map_of_injective S.M.subtype_injective, card_comap_toMbar, hO]
  · ext x
    have hx : ((eK.symm x : ↥(E.comap (toMbar S))) : G) = (x : G) := by
      have h := heK (eK.symm x)
      rwa [eK.apply_symm_apply, eq_comm] at h
    have hxM : (x : G) ∈ S.M := hx ▸ ((eK.symm x : ↥(E.comap (toMbar S))) : S.M).2
    have hxy : ((eK.symm x : ↥(E.comap (toMbar S))) : S.M) = ⟨x, hxM⟩ := Subtype.ext hx
    refine (hπ₀ (eK.symm x)).trans ?_
    change _ ↔ (x : G) ∈ TwoFi22.O23In S.M
    rewrite [hO23]
    refine Iff.trans ?_ Reifart.mem_map_subtype_iff.symm
    exact ⟨fun h => ⟨hxM, hxy ▸ h⟩, fun ⟨_, h⟩ => hxy ▸ h⟩
  · rw [relIndex, Reifart.subgroupOf_map_subtype_eq, Subgroup.index_comap_of_surjective E hsurj]
    exact hi

end Shape

section Center

variable {G : Type} [Group G] [Finite G]

theorem card_center_layer_ne_one (hU : U43NoFaithfulTwelve) (S : Setting G) (hw : S.width = 6)
    (hX : CFSG.Open.StatedClassicalModel
      (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) .PSU 4 3 1) :
    Nat.card (center (timmesfeldLayer S.Mbar)) ≠ 1 := by
  intro h1
  have hbot : center (timmesfeldLayer S.Mbar) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  let e0 : (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ≃*
      timmesfeldLayer S.Mbar :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let e1 : timmesfeldLayer S.Mbar ≃*
      ((timmesfeldLayer S.Mbar).map S.Mbar.subtype).map S.O.subtype :=
    ((timmesfeldLayer S.Mbar).equivMapOfInjective S.Mbar.subtype S.Mbar.subtype_injective).trans
      (((timmesfeldLayer S.Mbar).map S.Mbar.subtype).equivMapOfInjective S.O.subtype
        S.O.subtype_injective)
  have hmodel := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv (e0.trans e1) hX
  exact hU S.Qt (by rw [S.finrank_Qt_eq_two_mul_width, hw]) _ hmodel

theorem card_center_layer_eq_three (hU : U43NoFaithfulTwelve) (S : Setting G) (hw : S.width = 6)
    (hodd : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3)
    (hX : CFSG.Open.StatedClassicalModel
      (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) .PSU 4 3 1) :
    Nat.card (center (timmesfeldLayer S.Mbar)) = 3 :=
  card_center_layer_eq_three_of_ne_one hodd (card_center_layer_ne_one hU S hw hX)

end Center

theorem caseINotTwoCentral_of_U43 (hCE : CentralExtInput.{0}) (hS : SchreierFor InCatalog)
    (hF : FilterXInCatalog) (hU : U43NoFaithfulTwelve) (hMI : IdxFour.ModelInput)
    (hE0 : Nat.card IdxFour.E0 = 9797760) {OB OA : GammaU.V12 → Prop} {a0 w0 : GammaU.V12}
    (hF0 : IdxFour.E0Facts IdxFour.E0 OB OA a0 w0) : CaseINotTwoCentralStmt := by
  intro I G _ _ _ hK S hw hirr hnoAll g H C t ht ht1 hVQ hΩ h6 hN h2c
  have hNo : NoA2 S g := CFSG.LargeExtraspecial.S14.noA2_of (hnoAll g H.conj_mem H.conj_ne)
  have hΔ := (delta_six_of_not_twoCentral hCE H hNo C ht ht1 hVQ hΩ hN h6 h2c).1
  obtain ⟨hodd, hq, -⟩ := S5.timmesfeld_5_5 hCE (CFSG.LargeExtraspecial.S14.irr_of_not_isReducible
    hirr) H hNo C (S45Q.hyp45Q H C) (by omega)
  have hM : S.M ≠ ⊤ := M_ne_top_of_isSimpleGroup S
  have hperf : PerfectInLayer S := fun P hPM hP => perfect_le_layer_map hS hK hM hq hodd hPM hP
  obtain ⟨h1, h2, h3, h4⟩ := E_numerics hCE H hNo C ht ht1 hVQ hΩ hN h6 hodd hperf hΔ
  haveI : IsSimpleGroup (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) := hq.2
  have hfilter := hF (inCatalog_layer_quotient hK hM hq)
    (Helpers.quasisimple_central_quotient_nonabelian _ hq) h2 h1 h3 h4
  have hmodel : CFSG.Open.StatedClassicalModel
      (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) .PSU 4 3 1 := by
    rcases hfilter with h10 | h11 | h
    · exact (not_nonempty_mulEquiv_alternating hCE H hNo C ht ht1 hVQ hΩ hN h6 hodd hperf hΔ
        (Or.inl rfl) h10).elim
    · exact (not_nonempty_mulEquiv_alternating hCE H hNo C ht ht1 hVQ hΩ hN h6 hodd hperf hΔ
        (Or.inr rfl) h11).elim
    · exact h
  have hZ3 := card_center_layer_eq_three hU S hw hodd hmodel
  have hXcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_three hmodel
  obtain ⟨hZO, hO3, -, hidx⟩ :=
    index_and_inversion hCE H hNo C ht ht1 hVQ hΩ hN h6 hodd hZ3 hXcard hperf hΔ
  have hidx2 : (timmesfeldLayer S.Mbar).index = 2 := hidx.resolve_right
    (IdxFour.index_ne_four I.hTI hMI S hw hirr hnoAll H C _ _ (Layer.normal S.Mbar)
      (pCore_three_Mbar_eq S hO3).symm hO3 hZO hmodel)
  refine ⟨parrottShape_of_data S hw _ _ (Layer.normal S.Mbar) (pCore_three_Mbar_eq S hO3).symm
    hO3 hZO hmodel hidx2, fun hchar => ?_⟩
  exact IdxFour.false_of_charTwoFacts hchar I.hTI S hw hirr hnoAll H C
    (IdxFour.charTwoFacts_of_layer hE0 hF0 S hw H C _ _ hO3 hZO hmodel (by omega))

end Case25

end CFSG.GF2Type.Smith1979
