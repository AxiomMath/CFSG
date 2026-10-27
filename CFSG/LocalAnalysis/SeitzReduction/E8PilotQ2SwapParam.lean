module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2BLift
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitE7
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftDecomp
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMainKinds
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionFusion
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLift
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2Diagonal

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial SwapComponentData
  HasBLift oddCoreLift swapDiagHom swapDiagHom_injective range_swapDiagHom
  oddCore_quotient_oddCore_eq_bot_of_finite map_subtype_map_conj)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)

section Generic

variable {G : Type*} [Group G] {t : G}

theorem exists_swapParam_of_decomposition (htt : t * t = 1) {Kc E D : Subgroup G}
    (hcomm : Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G))
    (hdisj : Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥)
    (hE : Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = E)
    (hfix : E ⊓ centralizer ({t} : Set G) = D) :
    ∃ P : SwapParam t D, Function.Injective P.Ψ ∧ P.Ψ.range = E := by
  have hδrange : (swapDiagHom hcomm).range = D := by
    rw [range_swapDiagHom hcomm htt hdisj, hE, hfix]
  have hδinj := swapDiagHom_injective hcomm hdisj
  obtain ⟨lam, hlam⟩ : ∃ lam : D ≃* Kc, ∀ x : D, swapDiagHom hcomm (lam x) = x := by
    refine ⟨(MulEquiv.subgroupCongr hδrange.symm).trans (MonoidHom.ofInjective hδinj).symm,
      fun x => ?_⟩
    have h1 := congrArg Subtype.val ((MonoidHom.ofInjective hδinj).apply_symm_apply
      ((MulEquiv.subgroupCongr hδrange.symm) x))
    rw [MonoidHom.ofInjective_apply, MulEquiv.subgroupCongr_apply] at h1
    exact h1
  have hc : ∀ x y : D, Commute ((Kc.subtype.comp lam.toMonoidHom) x)
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
  have hrange : Φ₀.range = E := by
    rw [hΦ₀, MonoidHom.noncommCoprod_range, hrange1, hrange2, hE]
  refine ⟨⟨Φ₀, ?_, fun x => ?_, fun x y => ?_⟩, hinj, hrange⟩
  · rw [(MonoidHom.ker_eq_bot_iff Φ₀).2 hinj]
    exact bot_le
  · rw [hΦ₀apply, ← F4Pilot.swapDiagHom_apply hcomm, hlam]
  · rw [hΦ₀apply, hΦ₀apply]
    have hcy : (lam y : G) * (t * (lam x : G) * t⁻¹) = t * (lam x : G) * t⁻¹ * (lam y : G) :=
      F4Pilot.commute_of_map_conj_le_centralizer hcomm _ (lam y).2 _ ⟨_, (lam x).2, rfl⟩
    calc t * ((lam x : G) * (t * (lam y : G) * t⁻¹)) * t⁻¹ =
        (t * (lam x : G) * t⁻¹) * ((t * t) * (lam y : G) * (t * t)⁻¹) := by group
      _ = (lam y : G) * (t * (lam x : G) * t⁻¹) := by rw [htt, hcy]; group

theorem exists_swapParam_conj {D : Subgroup G} (P : SwapParam t D)
    (hinj : Function.Injective P.Ψ) (n : G) (hn : n * t = t * n) :
    ∃ P' : SwapParam t (D.map (MulAut.conj n).toMonoidHom), Function.Injective P'.Ψ ∧
      P'.Ψ.range = P.Ψ.range.map (MulAut.conj n).toMonoidHom := by
  set ε : D ≃* D.map (MulAut.conj n).toMonoidHom :=
    D.equivMapOfInjective _ (MulAut.conj n).injective with hε
  set Ψ' : D.map (MulAut.conj n).toMonoidHom × D.map (MulAut.conj n).toMonoidHom →* G :=
    (MulAut.conj n).toMonoidHom.comp
      (P.Ψ.comp (ε.symm.toMonoidHom.prodMap ε.symm.toMonoidHom)) with hΨ'
  have hΨ'apply : ∀ x y, Ψ' (x, y) = n * P.Ψ (ε.symm x, ε.symm y) * n⁻¹ := fun x y => rfl
  have hinj' : Function.Injective Ψ' := by
    intro a b hab
    have h1 : P.Ψ (ε.symm a.1, ε.symm a.2) = P.Ψ (ε.symm b.1, ε.symm b.2) := by
      have := hab
      rw [show a = (a.1, a.2) from rfl, show b = (b.1, b.2) from rfl, hΨ'apply,
        hΨ'apply] at this
      exact mul_left_cancel (mul_right_cancel this)
    have h2 := hinj h1
    exact Prod.ext (ε.symm.injective (congrArg Prod.fst h2))
      (ε.symm.injective (congrArg Prod.snd h2))
  refine ⟨⟨Ψ', ?_, fun d => ?_, fun x y => ?_⟩, hinj', ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff Ψ').2 hinj']
    exact bot_le
  · obtain ⟨d₀, rfl⟩ := ε.surjective d
    rw [hΨ'apply, MulEquiv.symm_apply_apply, P.diag]
    rfl
  · rw [hΨ'apply, hΨ'apply, ← P.swap (ε.symm x) (ε.symm y)]
    have hn' : n⁻¹ * t = t * n⁻¹ := by
      calc n⁻¹ * t = n⁻¹ * (t * n) * n⁻¹ := by group
        _ = n⁻¹ * (n * t) * n⁻¹ := by rw [hn]
        _ = t * n⁻¹ := by group
    calc t * (n * P.Ψ (ε.symm x, ε.symm y) * n⁻¹) * t⁻¹ =
        (t * n) * P.Ψ (ε.symm x, ε.symm y) * (n⁻¹ * t⁻¹) := by group
      _ = (n * t) * P.Ψ (ε.symm x, ε.symm y) * (t⁻¹ * n⁻¹) := by
          rw [← hn, show n⁻¹ * t⁻¹ = t⁻¹ * n⁻¹ by
            rw [← mul_inv_rev, ← mul_inv_rev, hn]]
      _ = n * (t * P.Ψ (ε.symm x, ε.symm y) * t⁻¹) * n⁻¹ := by group
  · ext g
    constructor
    · rintro ⟨⟨x, y⟩, rfl⟩
      exact ⟨P.Ψ (ε.symm x, ε.symm y), ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨⟨a, b⟩, rfl⟩, rfl⟩
      refine ⟨(ε a, ε b), ?_⟩
      rw [hΨ'apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      rfl

end Generic

section Lift


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem isPGroup_outer_of_mulEquiv_E8_two (hK : Nat.card K = 2) (e : L ≃* adjointGroup .E8 K) :
    IsPGroup 2 (Outer L) := by
  have : Subsingleton (Outer L) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with
    | H α =>
      induction b using QuotientGroup.induction_on with
      | H β =>
        rw [QuotientGroup.eq]
        exact forall_mem_range_conj_of_mulEquiv_E8_two hK e _
  intro g
  exact ⟨0, by rw [pow_zero, pow_one]; exact Subsingleton.elim _ _⟩

variable [Finite G]

theorem exists_swapDecomposition_nonsplit_two {t : G} (hw : E8Work L K t 1)
    (e : L ≃* adjointGroup .E8 K) {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K)
    (hA : Nat.card A = Nat.card K + 1) {X : Subgroup G}
    (hX : X = (A.map e.symm.toMonoidHom).map L.subtype) (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hS : NeighbourOvergroupE7Swap
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))) :
    ∃ Kc : Subgroup G, Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G) ∧
      Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = centralizerPerfectCore X ∧
      centralizerPerfectCore X ⊓ centralizer ({t} : Set G) = D := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hKt := hw.inf_eq e
  have hset := hw.seitz
  have hA3 : Nat.card A = 3 := by rw [hA, hK2]
  have hcyc : IsCyclic A := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card hA3
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_E8_nonsplit hset.standardSetting.standard htC
    hw.orderOf_eq hKt hw.card_eq e hAJ hA hcyc hX htX hDe
  have hlayer : D = inSubgroup layer (L ⊓ centralizer (X : Set G)) := by
    rw [hX, hDe]
    exact (inSubgroup_layer_inf_centralizer_nonsplit_E8 e hAJ hA hcyc).symm
  have hLX : L ⊓ centralizer (X : Set G) ≤ X ⊔ D := by
    rw [hX, hDe]
    exact (inf_centralizer_nonsplit_E8 e hAJ hA hcyc).le
  obtain ⟨-, -, hAD⟩ := centralizer_nonsplit_E8 hAJ hA hcyc
  have hDH : D ≤ centralizer (X : Set G) := by
    rw [hX, hDe]
    exact F4Pilot.map_map_symm_le_centralizer e hAD
  have hDL : D ≤ L := by
    rw [hDe]
    exact map_subtype_le _
  have hDq : CFSG.IsQuasisimple D := by
    rw [hDe]
    exact isQuasisimple_map_e7Levi e
  let eD : e7Levi K ≃* D :=
    (((e7Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((e7Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype
        L.subtype_injective)).trans (MulEquiv.subgroupCongr hDe.symm)
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  obtain ⟨Kb, hKb, hDK, hne, hcomm, ⟨eK⟩⟩ := hS
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  have ht't' : t' * t' = 1 := Subtype.ext htt
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
  have hZ : center Kb = ⊥ := hdata.center_eq_bot hO
  let eKD : Kb ≃* Db :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eK
  let eD' : e7Levi K ≃* D.subgroupOf H := eD.trans (subgroupOfEquivOfLe hDH).symm
  have hD'q : CFSG.Open.IsQuasisimple (D.subgroupOf H) :=
    F4Pilot.isQuasisimple_open_of_mulEquiv eD' isQuasisimple_open_e7Levi
  have hD'Z : center (D.subgroupOf H) = ⊥ :=
    F4Pilot.center_eq_bot_congr eD' center_e7Levi_eq_bot
  let eDb : D.subgroupOf H ≃* Db :=
    F4Pilot.mapMkEquivOfInfEqBot (oddCore H) (D.subgroupOf H)
      (F4Pilot.inf_oddCore_eq_bot hD'q hD'Z)
  let eK7 : Kb ≃* e7Levi K := eKD.trans (eDb.symm.trans eD'.symm)
  have hOutK : Group.IsSolvable (Outer Kb) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism (eK7.trans (e7LeviEquiv K))).2.mpr
      ⟨⟨2, (exceptional_E_pinned_model_Schreier K).2.1⟩⟩
  have hSchur : OddSchurTrivial Kb := (SeitzQ2.oddSchurTrivial_e7Levi K).of_mulEquiv eK7.symm
  have hOutL : IsPGroup 2 (Outer L) := isPGroup_outer_of_mulEquiv_E8_two hK2 e
  have ht1 : t ≠ 1 := fun h => by
    have h2 := hw.orderOf_eq
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have htL : t ∉ L := LinearPilot.not_mem_of_mem_centralizer hset.center_eq_bot htC ht1
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC hw.orderOf_eq
  have hZD : center D = ⊥ := F4Pilot.center_eq_bot_congr eD center_e7Levi_eq_bot
  have hXD : L ⊓ centralizer (X : Set G) ⊓ centralizer (D : Set G) ≤ X :=
    SeitzQ2.inf_centralizer_le_of_le_sup hLX (le_centralizer_iff.1 hDH) hZD
  have hKp : ⁅Kb, Kb⁆ = Kb := isPerfect_iff.mp hKb.1.1
  have hKτp : ⁅Kb.map (MulAut.conj (π t')).toMonoidHom,
      Kb.map (MulAut.conj (π t')).toMonoidHom⁆ = Kb.map (MulAut.conj (π t')).toMonoidHom := by
    rw [← map_commutator, hKp]
  set E := Kb ⊔ Kb.map (MulAut.conj (π t')).toMonoidHom with hEdef
  have hEp : ⁅E, E⁆ = E :=
    le_antisymm (CFSG.Quasithin.A3.commutator_self_le E) (sup_le
      (hKp.symm.le.trans (commutator_mono le_sup_left le_sup_left))
      (hKτp.symm.le.trans (commutator_mono le_sup_right le_sup_right)))
  have hττ : π t' * π t' = 1 := by rw [← map_mul, ht't', map_one]
  have hid : (MulAut.conj (π t')).toMonoidHom.comp (MulAut.conj (π t')).toMonoidHom =
      MonoidHom.id _ := by
    ext y
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply]
    calc π t' * (π t' * y * (π t')⁻¹) * (π t')⁻¹ =
        (π t' * π t') * y * (π t' * π t')⁻¹ := by group
      _ = y := by rw [hττ]; group
  have hEmap : E.map (MulAut.conj (π t')).toMonoidHom = E := by
    rw [hEdef, Subgroup.map_sup, map_map, hid, map_id, sup_comm]
  have hτE : π t' ∈ normalizer (E : Set (H ⧸ oddCore H)) := by
    rw [mem_normalizer_iff_map_conj_eq]
    exact hEmap
  have hBsup : HasBLift E := SeitzQ2.hasBLift_of_isPGroup_outer hOutL htC hw.orderOf_eq htL hCN
    hKt htX hlayer hDq hXD hEp hτE (F4Pilot.sup_conj_le_commutator_zpowers hKp hcomm)
  have hBK : HasBLift Kb := hBsup.mono le_sup_left
  obtain ⟨hcH, hdH', hsH, hKhp, hπK⟩ :=
    UnitaryPilot.swapLift_decomposition_of_hasBLift hdata hOutK hBK hBsup
  set Kh := oddCoreLift Kb with hKhdef
  set η : Kh →* Kb := (MulEquiv.subgroupCongr hπK).toMonoidHom.comp (π.subgroupMap Kh) with hη
  have hηapp : ∀ x : Kh, ((η x : Kb) : H ⧸ oddCore H) = π x := fun x => rfl
  have hηsurj : Function.Surjective η :=
    (MulEquiv.subgroupCongr hπK).surjective.comp (π.subgroupMap_surjective Kh)
  have hηker : η.ker = (oddCore H).subgroupOf Kh := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h1
      have h2 : π x = 1 := by rw [← hηapp, h1]; rfl
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    · intro h1
      apply Subtype.ext
      rw [hηapp, hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 h1]
      rfl
  have hηinj : Function.Injective η :=
    hSchur Kh (isPerfect_iff.mpr hKhp) η hηsurj (hηker ▸ hBK.inf_le_center)
      (hηker ▸ F4Pilot.odd_card_oddCore_subgroupOf Kh)
  have hKO : Kh ⊓ oddCore H = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxO⟩
    have h1 : η ⟨x, hxK⟩ = η 1 := by
      rw [map_one]
      exact (MonoidHom.mem_ker).1 (hηker ▸ (mem_subgroupOf.2 hxO))
    exact mem_bot.2 (congrArg Subtype.val (hηinj h1))
  have hcardK : Nat.card Kh = Nat.card Kb := Nat.card_congr (Equiv.ofBijective η ⟨hηinj, hηsurj⟩)
  have hdH : Kh ⊓ Kh.map (MulAut.conj t').toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← hKO]
    exact ⟨hx.1, hdH' hx⟩
  have hKct : (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom =
      (Kh.map (MulAut.conj t').toMonoidHom).map H.subtype :=
    (map_subtype_map_conj Kh t').symm
  have hc1 : (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom ≤
      centralizer ((Kh.map H.subtype : Subgroup G) : Set G) := by
    rw [hKct]
    exact F4Pilot.map_le_centralizer_map H.subtype hcH
  have hd1 : Kh.map H.subtype ⊓ (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [hKct, ← Subgroup.map_inf_eq _ _ _ H.subtype_injective, hdH, Subgroup.map_bot]
  have he1 : Kh.map H.subtype ⊔ (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom =
      centralizerPerfectCore X := by
    rw [hKct, ← Subgroup.map_sup, hsH, CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  refine ⟨Kh.map H.subtype, hc1, hd1, he1, ?_⟩
  have hDperf : ⁅D, D⁆ = D := isPerfect_iff.mp hDq.1
  have hDE : D ≤ centralizerPerfectCore X := CFSG.Quasithin.le_perfectCore_of_perfect hDH hDperf
  have hrange := range_swapDiagHom hc1 htt hd1
  rw [he1] at hrange
  have hinj := swapDiagHom_injective hc1 hd1
  have hcard : Nat.card (centralizerPerfectCore X ⊓ centralizer ({t} : Set G) : Subgroup G) ≤
      Nat.card D := by
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      card_map_of_injective H.subtype_injective, hcardK,
      Nat.card_congr ((eKD.trans eDb.symm).trans (subgroupOfEquivOfLe hDH)).toEquiv]
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hDE hDt) hcard).symm

theorem exists_swapParam_nonsplit_two {t : G} (hw : E8Work L K t 1)
    (e : L ≃* adjointGroup .E8 K) {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K)
    (hA : Nat.card A = Nat.card K + 1) {X : Subgroup G}
    (hX : X = (A.map e.symm.toMonoidHom).map L.subtype) (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hS : NeighbourOvergroupE7Swap
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))) :
    ∃ P : SwapParam t D, Function.Injective P.Ψ ∧ P.Ψ.range = centralizerPerfectCore X := by
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  obtain ⟨Kc, hc, hd, hE, hfix⟩ := exists_swapDecomposition_nonsplit_two hw e hAJ hA hX htX hDe hS
  exact exists_swapParam_of_decomposition htt hc hd hE hfix

end Lift

end CFSG.SeitzReduction.E8Pilot
