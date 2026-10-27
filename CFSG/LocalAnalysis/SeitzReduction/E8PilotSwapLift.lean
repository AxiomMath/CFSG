module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapCT
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLift
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial SwapComponentData
  swapDiagHom swapDiagHom_injective range_swapDiagHom swapLift_decomposition
  oddCore_quotient_oddCore_eq_bot_of_finite map_subtype_map_conj)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG)
open CFSG.LieType.Steinberg.Minuscule (e7Data_valid)


section Schur

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem oddSchurTrivial_adjointGroup_E7 {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    OddSchurTrivial (adjointGroup .E7 K) := by
  intro P _ _ hP η hη hcen _
  have := hP
  rcases Nat.lt_or_ge f 3 with h3 | h3
  ·
    have hf2 : f = 2 := by omega
    subst hf2
    set ε : e7Data_valid.minGroup K ≃* adjointGroup .E7 K := e7MinEquivAdjoint K with hε
    set η' : P →* e7Data_valid.minGroup K := ε.symm.toMonoidHom.comp η with hη'def
    have hη' : Function.Surjective η' := ε.symm.surjective.comp hη
    have hker' : η'.ker = η.ker := by
      ext x
      simp only [hη'def, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
    obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.FieldFour.e7_four_exists_section hK P η'
      hη' (hker' ▸ hcen)
    have hinj := F4Pilot.injective_of_section_of_perfect η' (hker' ▸ hcen) σ hσ
    intro a b hab
    apply hinj
    simp only [hη'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hab]
  ·
    have hF5 : 5 ≤ Nat.card K := by
      rw [hK]
      calc 5 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    exact injective_of_surjective_of_le_center_E7 hF5 η hη hcen

end Schur

section Normalize

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 K} {t : G}

theorem nonempty_swapNeighbourIso_E8 (N : E8Neighbour) {Kc : Subgroup G} (htt : t * t = 1)
    (hcomm : Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G))
    (hdisj : Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥)
    (hE : Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = neighbourCore e N)
    (hfix : neighbourCore e N ⊓ centralizer ({t} : Set G) =
      modelToG e ((N.levi K).map (adjointGroup .E8 K).subtype)) :
    Nonempty (SwapNeighbourIso e t N) := by
  obtain ⟨ε, hε⟩ : ∃ ε : N.levi K →* G, ∀ x, ε x = ((e.symm (x : adjointGroup .E8 K) : L) : G) :=
    ⟨L.subtype.comp (e.symm.toMonoidHom.comp (N.levi K).subtype), fun x => rfl⟩
  have hεinj : Function.Injective ε := by
    intro x y hxy
    rw [hε, hε] at hxy
    exact Subtype.ext (e.symm.injective (Subtype.ext hxy))
  have hεrange : ε.range = modelToG e ((N.levi K).map (adjointGroup .E8 K).subtype) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      rw [hε]
      exact symm_mem_modelToG e ⟨x, x.2, rfl⟩
    · intro hg
      obtain ⟨x, ⟨y, hy, hyx⟩, rfl⟩ := (mem_modelToG e).1 hg
      have hxy : x = y := Subtype.ext hyx.symm
      subst hxy
      exact ⟨⟨x, hy⟩, hε _⟩
  have hδrange : (swapDiagHom hcomm).range = ε.range := by
    rw [range_swapDiagHom hcomm htt hdisj, hE, hfix, hεrange]
  have hδinj := swapDiagHom_injective hcomm hdisj
  obtain ⟨lam, hlam⟩ : ∃ lam : N.levi K ≃* Kc, ∀ x, swapDiagHom hcomm (lam x) = ε x := by
    refine ⟨(MonoidHom.ofInjective hεinj).trans ((MulEquiv.subgroupCongr hδrange.symm).trans
      (MonoidHom.ofInjective hδinj).symm), fun x => ?_⟩
    have h1 := congrArg Subtype.val ((MonoidHom.ofInjective hδinj).apply_symm_apply
      ((MulEquiv.subgroupCongr hδrange.symm) (MonoidHom.ofInjective hεinj x)))
    rw [MonoidHom.ofInjective_apply, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply] at h1
    exact h1
  have hc : ∀ x y : N.levi K, Commute ((Kc.subtype.comp lam.toMonoidHom) x)
      (((MulAut.conj t).toMonoidHom.comp (Kc.subtype.comp lam.toMonoidHom)) y) := fun x y =>
    F4Pilot.commute_of_map_conj_le_centralizer hcomm _ (lam x).2 _ ⟨_, (lam y).2, rfl⟩
  set Φ₀ := (Kc.subtype.comp lam.toMonoidHom).noncommCoprod
    ((MulAut.conj t).toMonoidHom.comp (Kc.subtype.comp lam.toMonoidHom)) hc with hΦ₀
  have hΦ₀apply : ∀ x y, Φ₀ (x, y) = (lam x : G) * (t * (lam y : G) * t⁻¹) := fun x y => rfl
  have hrange1 : (Kc.subtype.comp lam.toMonoidHom).range = Kc := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 lam.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  have hrange2 : ((MulAut.conj t).toMonoidHom.comp (Kc.subtype.comp lam.toMonoidHom)).range =
      Kc.map (MulAut.conj t).toMonoidHom := by
    rw [MonoidHom.range_comp, hrange1]
  have hinj : Function.Injective Φ₀ := by
    rw [hΦ₀, MonoidHom.noncommCoprod_injective]
    refine ⟨Subtype.val_injective.comp lam.injective,
      (MulAut.conj t).injective.comp (Subtype.val_injective.comp lam.injective), ?_⟩
    rw [hrange1, hrange2]
    exact disjoint_iff.2 hdisj
  have hrange : Φ₀.range = neighbourCore e N := by
    rw [hΦ₀, MonoidHom.noncommCoprod_range, hrange1, hrange2, hE]
  refine ⟨⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun x => ?_,
    fun x y => ?_⟩⟩
  · rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply,
      hΦ₀apply, ← hε, ← hlam, F4Pilot.swapDiagHom_apply]
  · rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply,
      hΦ₀apply, hΦ₀apply]
    have hcy : (lam y : G) * (t * (lam x : G) * t⁻¹) = t * (lam x : G) * t⁻¹ * (lam y : G) :=
      F4Pilot.commute_of_map_conj_le_centralizer hcomm _ (lam y).2 _ ⟨_, (lam x).2, rfl⟩
    calc t * ((lam x : G) * (t * (lam y : G) * t⁻¹)) * t⁻¹ =
        (t * (lam x : G) * t⁻¹) * ((t * t) * (lam y : G) * (t * t)⁻¹) := by group
      _ = (lam y : G) * (t * (lam x : G) * t⁻¹) := by rw [htt, hcy]; group

end Normalize

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_swapDecomposition_high {t : G} {f : ℕ} (hw : E8Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .E8 K) (hX : HR8SwapE8 e t) :
    ∃ Kc : Subgroup G, Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G) ∧
      Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = neighbourCore e .high ∧
      neighbourCore e .high ⊓ centralizer ({t} : Set G) =
        modelToG e ((E8Neighbour.high.levi K).map (adjointGroup .E8 K).subtype) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hKt := hw.inf_eq e
  set X : Subgroup G := rootTorusG e with hXdef
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  set D : Subgroup G := rootLeviG e with hDdef
  have hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype := rfl
  obtain ⟨htX, Kb, hKb, hDK, hne, hcomm, ⟨eK⟩⟩ := hX
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  have ht't' : t' * t' = 1 := Subtype.ext htt
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_E8_highTorusLine hw.standard.standard htC
    hw.orderOf_eq hKt hf hw.card_eq e (X := X) rfl htX (D := D) rfl
  have hDH : D ≤ H :=
    F4Pilot.map_map_symm_le_centralizer e E6Pilot.highTorusLine_subgroupOf_le_centralizer_perpLevi
  have hDL : D ≤ L := map_subtype_le _
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDL hd))
  have hτD : π t' ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hdata : SwapComponentData (π t') Kb Db :=
    ⟨by rw [← map_mul, ht't', map_one], hKb, hne, hcomm, hDK, hτD, hsyl⟩
  have hO := oddCore_quotient_oddCore_eq_bot_of_finite (H := H)
  have hC := mem_center_of_mem_oddCore_of_commute_highTorusLine_E8 hw.card_eq hf
    hw.standard.standard htC hw.orderOf_eq hKt e htX
  have hZ : center Kb = ⊥ := hdata.center_eq_bot hO
  let eKD : Kb ≃* Db :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eK
  let eD : e7Levi K ≃* D :=
    ((e7Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((e7Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)
  let eD' : e7Levi K ≃* D.subgroupOf H := eD.trans (subgroupOfEquivOfLe hDH).symm
  have hD'q : CFSG.Open.IsQuasisimple (D.subgroupOf H) :=
    F4Pilot.isQuasisimple_open_of_mulEquiv eD' isQuasisimple_open_e7Levi
  have hD'Z : center (D.subgroupOf H) = ⊥ :=
    F4Pilot.center_eq_bot_congr eD' center_e7Levi_eq_bot
  let eDb : D.subgroupOf H ≃* Db :=
    F4Pilot.mapMkEquivOfInfEqBot (oddCore H) (D.subgroupOf H)
      (F4Pilot.inf_oddCore_eq_bot hD'q hD'Z)
  let eK7 : Kb ≃* adjointGroup .E7 K :=
    (eKD.trans (eDb.symm.trans eD'.symm)).trans (e7LeviEquiv K)
  have hOut : Group.IsSolvable (Outer Kb) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eK7).2.mpr
      ⟨⟨2, (exceptional_E_pinned_model_Schreier K).2.1⟩⟩
  have hSchur : OddSchurTrivial Kb :=
    (oddSchurTrivial_adjointGroup_E7 hw.card_eq hf).of_mulEquiv eK7.symm
  obtain ⟨hcH, hdH, hsH, -, -, hcardH⟩ := swapLift_decomposition ht't' hC hdata hOut hSchur
  set Kh := F4Pilot.oddCoreLift Kb with hKhdef
  have hKct : (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom =
      (Kh.map (MulAut.conj t').toMonoidHom).map H.subtype :=
    (map_subtype_map_conj Kh t').symm
  have hc1 : (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom ≤
      centralizer ((Kh.map H.subtype : Subgroup G) : Set G) := by
    rw [hKct]
    exact F4Pilot.map_le_centralizer_map H.subtype hcH
  have hd1 : Kh.map H.subtype ⊓ (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [hKct, ← Subgroup.map_inf_eq _ _ _ H.subtype_injective, hdH, Subgroup.map_bot]
  have hE : neighbourCore e .high = centralizerPerfectCore X := by
    rw [neighbourCore_high]
    rfl
  have he1 : Kh.map H.subtype ⊔ (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom =
      neighbourCore e .high := by
    rw [hKct, ← Subgroup.map_sup, hsH, CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map,
      range_subtype, hE]
    rfl
  refine ⟨Kh.map H.subtype, hc1, hd1, he1, ?_⟩
  have hlevi : modelToG e ((E8Neighbour.high.levi K).map (adjointGroup .E8 K).subtype) = D := by
    rw [E8Neighbour.levi_high, modelToG, hDdef, rootLeviG]
    congr 2
    exact Subgroup.comap_map_eq_self_of_injective (adjointGroup .E8 K).subtype_injective _
  rw [hlevi]
  have hDE : D ≤ neighbourCore e .high := modelToG_rootSpan_perpRoots_le_neighbourCore_high e
  have hrange := range_swapDiagHom hc1 htt hd1
  rw [he1] at hrange
  have hinj := swapDiagHom_injective hc1 hd1
  have hcard : Nat.card (neighbourCore e .high ⊓ centralizer ({t} : Set G) : Subgroup G) ≤
      Nat.card D := by
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      card_map_of_injective H.subtype_injective, hcardH,
      Nat.card_congr ((eKD.trans eDb.symm).trans (subgroupOfEquivOfLe hDH)).toEquiv]
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hDE hDt) hcard).symm

theorem nonempty_swapNeighbourIso_high {t : G} {f : ℕ} (hw : E8Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .E8 K) (hX : HR8SwapE8 e t) :
    Nonempty (SwapNeighbourIso e t .high) := by
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  obtain ⟨Kc, hc, hd, hE, hfix⟩ := exists_swapDecomposition_high hw hf e hX
  exact nonempty_swapNeighbourIso_E8 .high htt hc hd hE hfix

end Lift

theorem e8SwapRowCTInput_holds : E8SwapRowCTInput := by
  intro G _ _ L K _ _ _ e t f hw hf hX
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨hΦ⟩ := nonempty_swapNeighbourIso_high hw hf e hX
  exact exists_swapFactors_E8_of_high hΦ hw.mem_centralizer hq

end CFSG.SeitzReduction.E8Pilot
