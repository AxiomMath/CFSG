module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Work
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapParam
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial SwapComponentData
  HasBLift oddCoreLift swapDiagHom swapDiagHom_injective range_swapDiagHom
  oddCore_quotient_oddCore_eq_bot_of_finite map_subtype_map_conj)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)
open CFSG.SeitzReduction.OmegaPilot (NeighbourOvergroupOmega OmegaOvergroup)

section Kinds

variable {Y : Type} [Group Y]

@[expose] def NeighbourOvergroupOmegaField (s : Y) (D : Subgroup Y) (m f : ℕ) : Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
      ∃ hsN : s ∈ normalizer (Kc : Set Y), OmegaOvergroup Kc (Kc.normalizerMonoidHom ⟨s, hsN⟩) m f

@[expose] def NeighbourOvergroupOmegaSwap (s : Y) (D : Subgroup Y) : Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
      ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ center Kc = ⊥ ∧ Nonempty (Kc ≃* D)

theorem field_or_swap_of_neighbourOvergroupOmega {s : Y} {D : Subgroup Y} {m f : ℕ}
    (h : NeighbourOvergroupOmega s D m f) :
    NeighbourOvergroupOmegaField s D m f ∨ NeighbourOvergroupOmegaSwap s D := by
  obtain ⟨Kc, hKc, hDK, h1 | h2⟩ := h
  · exact .inl ⟨Kc, hKc, hDK, h1⟩
  · exact .inr ⟨Kc, hKc, hDK, h2⟩

end Kinds

section Lift


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_swapDecomposition_nonsplit_E7_two {t : G} (hw : E7Work L K t 1)
    (e : L ≃* adjointGroup .E7 K) {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K)
    (hA : Nat.card A = Nat.card K + 1) {X : Subgroup G}
    (hX : X = (A.map e.symm.toMonoidHom).map L.subtype) (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype)
    (hS : NeighbourOvergroupOmegaSwap
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
  obtain ⟨-, hsyl, -⟩ := hw.neighbour_standard_nonsplit_two e hAJ hA3 hX htX hDe
  have hlayer : D = inSubgroup layer (L ⊓ centralizer (X : Set G)) := by
    rw [hX, hDe]
    exact (inSubgroup_layer_inf_centralizer_nonsplit_E7_of_finite e hAJ hA hcyc).symm
  have hXD : L ⊓ centralizer (X : Set G) ⊓ centralizer (D : Set G) ≤ X := by
    rw [hX, hDe]
    exact inf_centralizer_inf_centralizer_le_nonsplit_E7 e hAJ hA hcyc
  have hDH : D ≤ centralizer (X : Set G) := by
    rw [hX, hDe]
    exact map_perpLevi_le_centralizer_E7_of_charTwo e (Subgroup.map_mono (Subgroup.map_mono hAJ))
  have hDL : D ≤ L := by
    rw [hDe]
    exact map_subtype_le _
  have hDq : CFSG.IsQuasisimple D := by
    rw [hDe]
    exact isQuasisimple_map_perpLevi_E7 e
  let eD : EPilot.perpLevi .E7 K ≃* D :=
    (((EPilot.perpLevi .E7 K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype
        L.subtype_injective)).trans (MulEquiv.subgroupCongr hDe.symm)
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  obtain ⟨Kb, hKb, hDK, hne, hcomm, -, ⟨eK⟩⟩ := hS
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
  let eD' : EPilot.perpLevi .E7 K ≃* D.subgroupOf H := eD.trans (subgroupOfEquivOfLe hDH).symm
  have hD'q : CFSG.Open.IsQuasisimple (D.subgroupOf H) :=
    F4Pilot.isQuasisimple_open_of_mulEquiv eD' isQuasisimple_open_perpLevi_E7
  have hD'Z : center (D.subgroupOf H) = ⊥ :=
    F4Pilot.center_eq_bot_congr eD' center_perpLevi_E7_eq_bot
  let eDb : D.subgroupOf H ≃* Db :=
    F4Pilot.mapMkEquivOfInfEqBot (oddCore H) (D.subgroupOf H)
      (F4Pilot.inf_oddCore_eq_bot hD'q hD'Z)
  let eK7 : Kb ≃* EPilot.perpLevi .E7 K := eK.trans (eDb.symm.trans eD'.symm)
  have hOutK : Group.IsSolvable (Outer Kb) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eK7).2.mpr isSolvable_outer_perpLevi_E7
  have hSchur : OddSchurTrivial Kb :=
    (SeitzQ2.oddSchurTrivial_perpLevi_E7_of_charTwo K).of_mulEquiv eK7.symm
  have hOutL : IsPGroup 2 (Outer L) := isPGroup_outer_of_mulEquiv_E7_two hK2 e
  have htL : t ∉ L := not_mem_of_mem_centralizer_E7 e htC hw.orderOf_eq
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC hw.orderOf_eq
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
      Nat.card_congr ((eK.trans eDb.symm).trans (subgroupOfEquivOfLe hDH)).toEquiv]
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hDE hDt) hcard).symm

theorem exists_swapParam_nonsplit_E7_two {t : G} (hw : E7Work L K t 1)
    (e : L ≃* adjointGroup .E7 K) {A : Subgroup (adjointGroup .E7 K)} (hAJ : A ≤ posJE7 K)
    (hA : Nat.card A = Nat.card K + 1) {X : Subgroup G}
    (hX : X = (A.map e.symm.toMonoidHom).map L.subtype) (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype)
    (hS : NeighbourOvergroupOmegaSwap
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))) :
    ∃ P : SwapParam t D, Function.Injective P.Ψ ∧ P.Ψ.range = centralizerPerfectCore X := by
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  obtain ⟨Kc, hc, hd, hE, hfix⟩ :=
    exists_swapDecomposition_nonsplit_E7_two hw e hAJ hA hX htX hDe hS
  exact E8Pilot.exists_swapParam_of_decomposition htt hc hd hE hfix

end Lift

end CFSG.SeitzReduction.E7Pilot
