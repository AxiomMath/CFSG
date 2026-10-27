module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowKinds
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapParam
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitLayer

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem swap_data_of_neighbourOvergroupKind_swap {Y : Type} [Group Y] {s : Y} {D : Subgroup Y}
    {f : ℕ} (h : NeighbourOvergroupKind s D f .swap) :
    ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
      Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
      ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ Nonempty (Kc ⧸ center Kc ≃* D) := by
  obtain ⟨Kc, hKc, hDK, ⟨hκ, -⟩ | ⟨-, hne, hcomm, hiso⟩⟩ := h
  · exact absurd rfl hκ
  · exact ⟨Kc, hKc, hDK, hne, hcomm, hiso⟩

theorem exists_swapDecomposition_nonsplit_F4_two {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hS : TwoKindAt e t X₀ .swap) :
    ∃ Kc : Subgroup G, Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G) ∧
      Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = centralizerPerfectCore (subgroupToG e X₀) ∧
      centralizerPerfectCore (subgroupToG e X₀) ⊓ centralizer ({t} : Set G) =
        subgroupToG e (C3Levi K) := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hKt := hw.inf_eq
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  obtain ⟨htX, hk⟩ := hS
  set X : Subgroup G := subgroupToG e X₀ with hXdef
  set D : Subgroup G := subgroupToG e (C3Levi K) with hDdef
  have hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype := rfl
  have hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype := rfl
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_nonsplit hw.standard.standard htC hw.orderOf_eq hKt
    hw.card_eq e hXJ hcyc hX₀' hX htX hDe
  have hlayer : D = inSubgroup layer (L ⊓ centralizer (X : Set G)) :=
    (inSubgroup_layer_inf_centralizer_nonsplit e hXJ hcyc hX₀').symm
  obtain ⟨hcen, -, hX₀D⟩ := centralizer_nonsplit hXJ hcyc hX₀'
  have hLX : L ⊓ centralizer (X : Set G) ≤ X ⊔ D := by
    rw [hX, hDe, inf_centralizer_map_symm, hcen, Subgroup.map_sup, Subgroup.map_sup]
  have hDH : D ≤ centralizer (X : Set G) := map_map_symm_le_centralizer e hX₀D
  have hDL : D ≤ L := map_subtype_le _
  have hDq : CFSG.IsQuasisimple D := isQuasisimple_map_C3Levi e
  let eD : C3Levi K ≃* D :=
    ((C3Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((C3Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  obtain ⟨Kb, hKb, hDK, hne, hcomm, ⟨eK⟩⟩ := swap_data_of_neighbourOvergroupKind_swap hk
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
  let eD' : C3Levi K ≃* D.subgroupOf H := eD.trans (subgroupOfEquivOfLe hDH).symm
  have hD'q : CFSG.Open.IsQuasisimple (D.subgroupOf H) :=
    isQuasisimple_open_of_mulEquiv eD' isQuasisimple_open_C3Levi
  have hD'Z : center (D.subgroupOf H) = ⊥ := center_eq_bot_congr eD' center_C3Levi_eq_bot
  let eDb : D.subgroupOf H ≃* Db :=
    mapMkEquivOfInfEqBot (oddCore H) (D.subgroupOf H) (inf_oddCore_eq_bot hD'q hD'Z)
  let eKC : Kb ≃* C3Levi K := eKD.trans (eDb.symm.trans eD'.symm)
  have hOutK : Group.IsSolvable (Outer Kb) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eKC).2.2
      (isSolvable_outer_C3Levi hw.card_eq)
  have hSchur : OddSchurTrivial Kb :=
    (oddSchurTrivial_statedSp 3 K).of_mulEquiv ((c3LeviEquiv K).trans eKC.symm)
  have hOutL : IsPGroup 2 (Outer L) := SeitzQ2.isPGroup_outer_of_mulEquiv_F4_two hK2 e
  have ht1 : t ≠ 1 := fun h => by
    have h2 := hw.orderOf_eq
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have htL : t ∉ L := LinearPilot.not_mem_of_mem_centralizer hw.center_eq_bot htC ht1
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hw.standard.standard htC hw.orderOf_eq
  have hZD : center D = ⊥ := center_eq_bot_congr eD center_C3Levi_eq_bot
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
    hKt htX hlayer hDq hXD hEp hτE (sup_conj_le_commutator_zpowers hKp hcomm)
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
      (hηker ▸ odd_card_oddCore_subgroupOf Kh)
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
    exact map_le_centralizer_map H.subtype hcH
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

theorem exists_swapParam_nonsplit_F4_two {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hS : TwoKindAt e t X₀ .swap) :
    ∃ P : SwapParam t (subgroupToG e (C3Levi K)), Function.Injective P.Ψ ∧
      P.Ψ.range = centralizerPerfectCore (subgroupToG e X₀) := by
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  obtain ⟨Kc, hc, hd, hE, hfix⟩ := exists_swapDecomposition_nonsplit_F4_two hw e hXJ hcyc hX₀ hS
  exact E8Pilot.exists_swapParam_of_decomposition htt hc hd hE hfix

end CFSG.SeitzReduction.F4Pilot
