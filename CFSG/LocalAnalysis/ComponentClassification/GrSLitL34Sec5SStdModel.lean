module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.ONAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rank
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourSylowFixed
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalSimpleFitting
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Gen
public import CFSG.Sporadic.ONOddCore.Head
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open scoped commutatorElement

section Model

variable {Y : Type} [Group Y]

theorem mul_mem_range_conj_onan
    (hY : IsSporadic Y .ONan) {α β : MulAut Y}
    (hα : α ∉ (MulAut.conj : Y →* MulAut Y).range)
    (hβ : β ∉ (MulAut.conj : Y →* MulAut Y).range) :
    α * β ∈ (MulAut.conj : Y →* MulAut Y).range := by
  have hdvd : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) ∣ 2 :=
    CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two (T := Y) hY
  have hcard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      have : Subsingleton (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) :=
        (Nat.card_eq_one_iff_unique.mp h).1
      have hone : (QuotientGroup.mk'
          (CFSG.ComponentClassification.OuterAutomorphisms.inner Y) α) = 1 :=
        Subsingleton.elim _ _
      exact hα (by
        have hmem := (QuotientGroup.eq_one_iff (N :=
          CFSG.ComponentClassification.OuterAutomorphisms.inner Y) α).mp hone
        simpa [CFSG.ComponentClassification.OuterAutomorphisms.inner] using hmem)
    · exact h
  have hindex : ((MulAut.conj : Y →* MulAut Y).range).index = 2 := by
    rw [Subgroup.index_eq_card]
    simpa [CFSG.ComponentClassification.OuterAutomorphisms.inner,
      CFSG.ComponentClassification.OuterAutomorphisms.Outer] using hcard
  exact (Subgroup.mul_mem_iff_of_index_two hindex).mpr
    ⟨fun h => (hα h).elim, fun h => (hβ h).elim⟩

theorem card_center_sylow_onan
    [Finite Y] (hY : IsSporadic Y .ONan) (T : Sylow 2 Y) :
    Nat.card (center (T : Subgroup Y)) = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.Solomon78.on_equiv_Pv hY
  let S : Sylow 2 CFSG.ONSchreier.Pv :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T
  have hS : (S : Subgroup CFSG.ONSchreier.Pv) =
      (T : Subgroup Y).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective T
  let eT : (T : Subgroup Y) ≃* (S : Subgroup CFSG.ONSchreier.Pv) :=
    (Subgroup.equivMapOfInjective (T : Subgroup Y) e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hS.symm)
  have : Finite (Sylow 2 CFSG.ONSchreier.Pv) :=
    Sylow.finite_of_finiteIndex CFSG.ONSchreier.onTSylow
  have hTS : Nat.card (Subgroup.center (T : Subgroup Y)) =
      Nat.card (Subgroup.center (S : Subgroup CFSG.ONSchreier.Pv)) :=
    Nat.card_congr (Subgroup.centerCongr eT).toEquiv
  have hS0 : Nat.card (Subgroup.center (S : Subgroup CFSG.ONSchreier.Pv)) =
      Nat.card (Subgroup.center
        (CFSG.ONSchreier.onTSylow : Subgroup CFSG.ONSchreier.Pv)) :=
    Nat.card_congr
      (Subgroup.centerCongr (Sylow.equiv S CFSG.ONSchreier.onTSylow)).toEquiv
  rw [hTS, hS0]
  have hcenter : CFSG.centerIn
      (CFSG.ONSchreier.onTSylow : Subgroup CFSG.ONSchreier.Pv) =
      (Subgroup.zpowers CFSG.ONSchreier.onz).subgroupOf CFSG.ONSchreier.Pv := by
    ext x
    rw [CFSG.ONSchreier.onTSylow_centerIn, CFSG.ONSchreier.onT_centerIn,
      Subgroup.mem_subgroupOf]
  have hcardcenter : Nat.card (Subgroup.center
        (CFSG.ONSchreier.onTSylow : Subgroup CFSG.ONSchreier.Pv)) =
      Nat.card (CFSG.centerIn
        (CFSG.ONSchreier.onTSylow : Subgroup CFSG.ONSchreier.Pv)) := by
    rw [CFSG.centerIn_eq_map_center, Subgroup.card_map_of_injective
      (CFSG.ONSchreier.onTSylow : Subgroup CFSG.ONSchreier.Pv).subtype_injective]
  rw [hcardcenter, hcenter]
  have hle : Subgroup.zpowers CFSG.ONSchreier.onz ≤ CFSG.ONSchreier.Pv :=
    Subgroup.zpowers_le.mpr (CFSG.ONSchreier.onT_le CFSG.ONSchreier.onz_mem_T)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers,
    CFSG.ONSchreier.orderOf_onz]

theorem eq_bot_of_odd_of_normalized_centralizer_onan
    [Finite Y] (hY : IsSporadic Y .ONan)
    {a : Y} (ha : orderOf a = 2) {W : Subgroup Y}
    (hWa : W ≤ centralizer ({a} : Set Y))
    (hWn : ∀ c ∈ centralizer ({a} : Set Y), ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hW : Odd (Nat.card W)) : W = ⊥ := by
  classical
  have hcenter : Subgroup.center Y = ⊥ :=
    CFSG.EvenSporadicStandard.Solomon78.center_eq_bot_of_isSporadic_on hY
  obtain ⟨eON⟩ := hY
  obtain ⟨-, -, hsimpleON⟩ := CFSG.Sporadic.ON.fam_on_simplicity
  have hsimpleY : IsSimpleGroup Y := @MulEquiv.isSimpleGroup _ _ _ _ hsimpleON eON
  have : IsSimpleGroup Y := hsimpleY
  have : Nontrivial Y := hsimpleY.toNontrivial
  have hna : ∃ a b : Y, a * b ≠ b * a := by
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := exists_ne (1 : Y)
    have hxZ : x ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun g => h g x
    rw [hcenter, Subgroup.mem_bot] at hxZ
    exact hx hxZ
  have hFtop : CFSG.generalizedFitting Y = ⊤ :=
    (CFSG.ComponentClassification.SmallLocal.simple_generalized_fitting_self Y hna).2.2.2.2
  let eF : CFSG.generalizedFitting Y ≃* Y :=
    (MulEquiv.subgroupCongr hFtop).trans Subgroup.topEquiv
  have hFs : IsSimpleGroup (CFSG.generalizedFitting Y) := eF.isSimpleGroup
  have hFON : Nonempty (CFSG.generalizedFitting Y ≃* CFSG.Blueprint.NativeSporadic.ON) :=
    ⟨eF.trans eON⟩
  have hcore : CFSG.oddCore ↥(Subgroup.centralizer ({a} : Set Y)) = ⊥ :=
    (CFSG.Sporadic.ONOddCore.ctuc_on_generalized_fitting_involution_centralizer_odd_core_trivial
      hFs hFON).2 a ha
  have hWle : W.subgroupOf (Subgroup.centralizer ({a} : Set Y)) ≤
      CFSG.oddCore ↥(Subgroup.centralizer ({a} : Set Y)) := by
    refine CFSG.ABGLocalTools.le_oddCore_of_normal ?_ ?_
    · constructor
      intro w hw c
      have hwW : (w : Y) ∈ W := Subgroup.mem_subgroupOf.mp hw
      simpa [Subgroup.mem_subgroupOf] using hWn (c : Y) c.2 (w : Y) hwW
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWa).toEquiv]
      exact hW
  rw [hcore] at hWle
  have hbot : W.subgroupOf (Subgroup.centralizer ({a} : Set Y)) = ⊥ :=
    le_bot_iff.mp hWle
  refine le_bot_iff.mp ?_
  intro w hw
  have hw' : (⟨w, hWa hw⟩ : ↥(Subgroup.centralizer ({a} : Set Y))) ∈
      W.subgroupOf (Subgroup.centralizer ({a} : Set Y)) := by
    rw [Subgroup.mem_subgroupOf]
    exact hw
  rw [hbot, Subgroup.mem_bot] at hw'
  simpa using hw'

theorem hasElemAbelianEight_onan
    (hY : IsSporadic Y .ONan) :
    EvenSporadicStandard.HypOne.HasElemAbelianEight Y := by
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.Solomon78.on_equiv_Pv hY
  have hsqP : CFSG.Sporadic.ONOddCore.sqP ≤ CFSG.ONSchreier.Pv := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨t, ht, rfl⟩
    exact Subgroup.pow_mem _ (CFSG.ONSchreier.onT_le ht) 2
  have homegaP : CFSG.Sporadic.ONOddCore.omegaP ≤ CFSG.ONSchreier.Pv := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hx, -⟩
    exact hsqP hx
  have : CFSG.IsElementaryAbelian 2 CFSG.Sporadic.ONOddCore.omegaP :=
    CFSG.Sporadic.ONOddCore.omegaP_elementary
  have homelem : CFSG.Open.IsElemAbelian 2 CFSG.Sporadic.ONOddCore.omegaP :=
    CFSG.Open.isElemAbelian_of_isElementaryAbelian
  have hPv : EvenSporadicStandard.HypOne.HasElemAbelianEight CFSG.ONSchreier.Pv :=
    EvenSporadicStandard.HypOne.HasElemAbelianEight.of_le homegaP homelem
      CFSG.Sporadic.ONOddCore.card_omegaP
  exact EvenSporadicStandard.HypOne.HasElemAbelianEight.of_mulEquiv e.symm hPv

end Model

section Commutator

open CFSG.LocalAnalysis.ComponentInitial

theorem commutator_centralizer_zP_eq_onL :
    (⁅CFSG.Sporadic.ONOddCore.Mv, CFSG.Sporadic.ONOddCore.Mv⁆ : Subgroup CFSG.ONSchreier.Pv) =
      CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.Pv := by
  apply Subgroup.map_injective CFSG.ONSchreier.Pv.subtype_injective
  rw [Subgroup.map_commutator]
  rw [show CFSG.Sporadic.ONOddCore.Mv =
      CFSG.ONSchreier.onM.subgroupOf CFSG.ONSchreier.Pv from rfl]
  rw [Subgroup.map_subgroupOf_eq_of_le CFSG.ONSchreier.onM_le,
    ← CFSG.ONSchreier.onL_eq_commutator,
    Subgroup.map_subgroupOf_eq_of_le CFSG.ONSchreier.onL_le]

theorem map_commutator_centralizer_eq_onL
    {Y : Type} [Group Y] (e : Y ≃* CFSG.ONSchreier.Pv)
    (a : Y) (he : e a = CFSG.ONSchreier.zP) :
    ((⁅Subgroup.centralizer ({a} : Set Y), Subgroup.centralizer ({a} : Set Y)⁆ :
        Subgroup Y)).map e.toMonoidHom =
      CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.Pv := by
  rw [Subgroup.map_commutator,
    CFSG.Sporadic.ONOddCore.centralizer_map_equiv e a, he,
    CFSG.Sporadic.ONOddCore.centralizer_zP, commutator_centralizer_zP_eq_onL]

theorem mem_range_conj_of_forall_mem_onL
    (β : MulAut CFSG.ONSchreier.Pv)
    (hβ : ∀ x : CFSG.ONSchreier.Pv,
      (x : Equiv.Perm (Fin CFSG.ONSchreier.N)) ∈ CFSG.ONSchreier.onL → β x = x) :
    β ∈ (MulAut.conj : CFSG.ONSchreier.Pv →* MulAut CFSG.ONSchreier.Pv).range := by
  by_contra hout
  have honzL : CFSG.ONSchreier.onz ∈ CFSG.ONSchreier.onL := by
    rw [CFSG.ONSchreier.onz_eq_q2, pow_two]
    exact CFSG.ONSchreier.onL.mul_mem CFSG.ONSchreier.onq_mem_L CFSG.ONSchreier.onq_mem_L
  have hz : β CFSG.ONSchreier.zP = CFSG.ONSchreier.zP := hβ _ honzL
  obtain ⟨-, hsurj, h⟩ :=
    CFSG.Sporadic.ONOddCore.ctuc_on_outer_local_quotient_is_graph_or_field
  obtain ⟨-, hLm, -, A, hA | hA⟩ := h β hout hz
  · refine CFSG.ComponentClassification.PSL3Four.false_of_graph_or_field_fixes_sylow
      (default : Sylow 2 (LinearFlag.projectiveSL 3 CFSG.ComponentClassification.PSL3Four.F4))
      A (Or.inl ?_)
    intro y _
    obtain ⟨a, rfl⟩ := hsurj y
    let x : CFSG.ONSchreier.Pv :=
      ⟨a, CFSG.ONSchreier.onM_le (CFSG.ONSchreier.onL_le_M a.2)⟩
    have hxL : ((β x : CFSG.ONSchreier.Pv) : Equiv.Perm (Fin CFSG.ONSchreier.N)) ∈ CFSG.ONSchreier.onL :=
      (hLm x).2 a.2
    let a' : CFSG.ONSchreier.onL :=
      ⟨((β x : CFSG.ONSchreier.Pv) : Equiv.Perm (Fin CFSG.ONSchreier.N)), hxL⟩
    have hfix := hA a a' rfl
    have ha'a : a' = a := by
      apply Subtype.ext
      show ((β x : CFSG.ONSchreier.Pv) : Equiv.Perm (Fin CFSG.ONSchreier.N)) =
        ((x : CFSG.ONSchreier.Pv) : Equiv.Perm (Fin CFSG.ONSchreier.N))
      exact congrArg (fun z : CFSG.ONSchreier.Pv =>
        (z : Equiv.Perm (Fin CFSG.ONSchreier.N))) (hβ x a.2)
    rw [ha'a] at hfix
    exact hfix.symm
  · refine CFSG.ComponentClassification.PSL3Four.false_of_graph_or_field_fixes_sylow
      (default : Sylow 2 (LinearFlag.projectiveSL 3 CFSG.ComponentClassification.PSL3Four.F4))
      A (Or.inr ?_)
    intro y _
    obtain ⟨a, rfl⟩ := hsurj y
    let x : CFSG.ONSchreier.Pv :=
      ⟨a, CFSG.ONSchreier.onM_le (CFSG.ONSchreier.onL_le_M a.2)⟩
    have hxL : ((β x : CFSG.ONSchreier.Pv) : Equiv.Perm (Fin CFSG.ONSchreier.N)) ∈ CFSG.ONSchreier.onL :=
      (hLm x).2 a.2
    let a' : CFSG.ONSchreier.onL :=
      ⟨((β x : CFSG.ONSchreier.Pv) : Equiv.Perm (Fin CFSG.ONSchreier.N)), hxL⟩
    have hfix := hA a a' rfl
    have ha'a : a' = a := by
      apply Subtype.ext
      show ((β x : CFSG.ONSchreier.Pv) : Equiv.Perm (Fin CFSG.ONSchreier.N)) =
        ((x : CFSG.ONSchreier.Pv) : Equiv.Perm (Fin CFSG.ONSchreier.N))
      exact congrArg (fun z : CFSG.ONSchreier.Pv =>
        (z : Equiv.Perm (Fin CFSG.ONSchreier.N))) (hβ x a.2)
    rw [ha'a] at hfix
    exact hfix.symm

variable {Y : Type} [Group Y]

theorem card_centralizer_commutator_centralizer_onan
    (hY : IsSporadic Y .ONan) {a : Y} (ha : orderOf a = 2) :
    Nat.card (centralizer
      ((⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ : Subgroup Y) : Set Y)) = 4 := by
  obtain ⟨e₀⟩ := hY
  let e : Y ≃* CFSG.Blueprint.NativeSporadic.ON := e₀
  let eP : Y ≃* CFSG.ONSchreier.Pv := e.trans CFSG.ONSchreier.onEquivPv
  have hb : orderOf (eP a) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ha
  obtain ⟨g, hg⟩ := CFSG.EvenSporadicStandard.Solomon78.pv_conj_zP (eP a) hb
  let e' : Y ≃* CFSG.ONSchreier.Pv := eP.trans (MulAut.conj g⁻¹)
  have he'a : e' a = CFSG.ONSchreier.zP := by
    show MulAut.conj g⁻¹ (eP a) = CFSG.ONSchreier.zP
    rw [hg, MulAut.conj_apply]
    group
  have hSmap := map_commutator_centralizer_eq_onL e' a he'a
  have honzL : CFSG.ONSchreier.onz ∈ CFSG.ONSchreier.onL := by
    rw [CFSG.ONSchreier.onz_eq_q2, pow_two]
    exact CFSG.ONSchreier.onL.mul_mem CFSG.ONSchreier.onq_mem_L CFSG.ONSchreier.onq_mem_L
  have hcent : (Subgroup.centralizer
      ((CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.Pv : Subgroup CFSG.ONSchreier.Pv) :
        Set CFSG.ONSchreier.Pv) : Subgroup CFSG.ONSchreier.Pv) =
      (Subgroup.centralizer (CFSG.ONSchreier.onL : Set (Equiv.Perm (Fin CFSG.ONSchreier.N)))).subgroupOf
        CFSG.ONSchreier.Pv :=
    CFSG.QuasiDihedralFusion.centralizer_subgroupOf CFSG.ONSchreier.onL_le
  have hPeq : (CFSG.ONSchreier.Pv ⊓
      Subgroup.centralizer (CFSG.ONSchreier.onL : Set (Equiv.Perm (Fin CFSG.ONSchreier.N))) :
        Subgroup (Equiv.Perm (Fin CFSG.ONSchreier.N))) = CFSG.ONSchreier.onQ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
      rw [← CFSG.ONSchreier.onM_centralizer_L]
      refine Subgroup.mem_inf.2 ⟨?_, hxC⟩
      rw [CFSG.ONSchreier.onM_eq_centralizer_z]
      exact Subgroup.mem_inf.2 ⟨hxP, Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hxC CFSG.ONSchreier.onz honzL).symm⟩
    · exact le_inf (CFSG.ONSchreier.onQ_le_L.trans CFSG.ONSchreier.onL_le)
        CFSG.ONSchreier.onQ_le_centralizer_L
  have hzP : Nat.card (Subgroup.centralizer
      ((CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.Pv : Subgroup CFSG.ONSchreier.Pv) :
        Set CFSG.ONSchreier.Pv)) = 4 := by
    rw [hcent, CFSG.ONSchreier.card_subgroupOf, hPeq, CFSG.ONSchreier.card_onQ]
  calc
    Nat.card (centralizer
        ((⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ : Subgroup Y) : Set Y)) =
        Nat.card ((centralizer
          ((⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ : Subgroup Y) :
            Set Y)).map e'.toMonoidHom) :=
          (Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective).symm
    _ = Nat.card (centralizer (e'.toMonoidHom ''
          ((⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ : Subgroup Y) : Set Y))) := by
          rw [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv]
    _ = Nat.card (centralizer (((⁅centralizer ({a} : Set Y),
          centralizer ({a} : Set Y)⁆ : Subgroup Y).map e'.toMonoidHom : Subgroup
            CFSG.ONSchreier.Pv) : Set CFSG.ONSchreier.Pv)) := by
          rw [Subgroup.coe_map]
    _ = Nat.card (centralizer
        ((CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.Pv : Subgroup CFSG.ONSchreier.Pv) :
          Set CFSG.ONSchreier.Pv)) := by rw [hSmap]
    _ = 4 := hzP

theorem mem_range_conj_of_forall_mem_commutator_centralizer_onan
    (hY : IsSporadic Y .ONan) {a : Y} (ha : orderOf a = 2) {α : MulAut Y}
    (hα : ∀ x ∈ ⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆, α x = x) :
    α ∈ (MulAut.conj : Y →* MulAut Y).range := by
  by_contra hout
  obtain ⟨e₀⟩ := hY
  let e : Y ≃* CFSG.Blueprint.NativeSporadic.ON := e₀
  let eP : Y ≃* CFSG.ONSchreier.Pv := e.trans CFSG.ONSchreier.onEquivPv
  have hb : orderOf (eP a) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ha
  obtain ⟨g, hg⟩ := CFSG.EvenSporadicStandard.Solomon78.pv_conj_zP (eP a) hb
  let e' : Y ≃* CFSG.ONSchreier.Pv := eP.trans (MulAut.conj g⁻¹)
  have he'a : e' a = CFSG.ONSchreier.zP := by
    show MulAut.conj g⁻¹ (eP a) = CFSG.ONSchreier.zP
    rw [hg, MulAut.conj_apply]
    group
  let β : MulAut CFSG.ONSchreier.Pv := MulAut.congr e' α
  have hβout : β ∉ (MulAut.conj : CFSG.ONSchreier.Pv →*
      MulAut CFSG.ONSchreier.Pv).range :=
    CFSG.OddStandard.GH71.S55.congr_not_mem_range_conj e' hout
  have hSmap := map_commutator_centralizer_eq_onL e' a he'a
  have hβ : ∀ x : CFSG.ONSchreier.Pv,
      (x : Equiv.Perm (Fin CFSG.ONSchreier.N)) ∈ CFSG.ONSchreier.onL → β x = x := by
    intro x hx
    have hxS : x ∈ (CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.Pv :
        Subgroup CFSG.ONSchreier.Pv) := hx
    rw [← hSmap] at hxS
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hxS
    show MulAut.congr e' α (e' y) = e' y
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hα y hy]
  exact hβout (mem_range_conj_of_forall_mem_onL β hβ)

end Commutator

section SylowFixed

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ONSchreier CFSG.Sporadic.ONOddCore
open scoped Pointwise

private theorem onan_onT_le_onM :
    onT ≤ onM := by
  rw [onM_eq_centralizer_z]
  intro t ht
  refine ⟨onT_le ht, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hz : onz ∈ CFSG.centerIn onT := by
    rw [onT_centerIn]
    exact Subgroup.mem_zpowers _
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 t ht)

private theorem onan_onQ_le_onT :
    onQ ≤ onT := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardT : Nat.card (onT.subgroupOf onM) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onan_onT_le_onM).toEquiv, card_onT]
  have hTP : IsPGroup 2 (onT.subgroupOf onM) :=
    IsPGroup.of_card (n := 9) (by rw [hcardT]; norm_num)
  have hidx : ¬ 2 ∣ (onT.subgroupOf onM).index := by
    have h := (onT.subgroupOf onM).card_mul_index
    rw [hcardT, card_onM] at h
    have hi : (onT.subgroupOf onM).index = 315 := by omega
    rw [hi]
    decide
  let T' : Sylow 2 onM := hTP.toSylow hidx
  have hQn : (onQ.subgroupOf onM).Normal := by
    rw [← rhoM_ker]
    exact rhoM.normal_ker
  have hQp : IsPGroup 2 (onQ.subgroupOf onM) :=
    IsPGroup.of_card (n := 2) (by rw [card_onQ_subgroupOf_M]; norm_num)
  have hle := hQp.le_sylow_of_normal T'
  intro x hx
  have hmem : (⟨x, onQ_le_M hx⟩ : onM) ∈ onQ.subgroupOf onM := hx
  have h := hle hmem
  rw [show (T' : Subgroup onM) = onT.subgroupOf onM from IsPGroup.toSylow_coe _ _] at h
  exact h

private theorem onan_sup_onT_onL :
    onT ⊔ onL = onM := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn : (onL.subgroupOf onM).Normal := by
    refine Subgroup.normal_of_index_eq_two ?_
    rw [← Subgroup.relIndex]
    exact onL_relIndex
  have hKidx : (onL.subgroupOf onM).index = 2 := by
    rw [← Subgroup.relIndex]
    exact onL_relIndex
  have hcardT : Nat.card (onT.subgroupOf onM) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onan_onT_le_onM).toEquiv, card_onT]
  have hTP : IsPGroup 2 (onT.subgroupOf onM) :=
    IsPGroup.of_card (n := 9) (by rw [hcardT]; norm_num)
  have hidx : ¬ 2 ∣ (onT.subgroupOf onM).index := by
    have h := (onT.subgroupOf onM).card_mul_index
    rw [hcardT, card_onM] at h
    have hi : (onT.subgroupOf onM).index = 315 := by omega
    rw [hi]
    decide
  let T' : Sylow 2 onM := hTP.toSylow hidx
  have htop : (onL.subgroupOf onM) ⊔ (T' : Subgroup onM) = ⊤ :=
    CFSG.QuasiDihedralFusion.normal_sup_sylow_eq_top (onL.subgroupOf onM) ⟨1, hKidx⟩ T'
  have hm := congrArg (Subgroup.map (Subgroup.subtype onM)) htop
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le onL_le_M,
    show (T' : Subgroup onM) = onT.subgroupOf onM from IsPGroup.toSylow_coe _ _,
    Subgroup.map_subgroupOf_eq_of_le onan_onT_le_onM, sup_comm] at hm
  exact hm

private theorem onan_card_inf_onT_onL :
    Nat.card (onT ⊓ onL : Subgroup (Equiv.Perm (Fin N))) = 256 := by
  have hLn : (onL.subgroupOf onM).Normal := by
    refine Subgroup.normal_of_index_eq_two ?_
    rw [← Subgroup.relIndex]
    exact onL_relIndex
  have hMn : onM ≤ Subgroup.normalizer (onL : Set (Equiv.Perm (Fin N))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer onL_le_M).1 hLn
  have hTN : onT ≤ Subgroup.normalizer (onL : Set (Equiv.Perm (Fin N))) :=
    onan_onT_le_onM.trans hMn
  have hprod :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := onT) (K := onL) hTN
  rw [onan_sup_onT_onL, card_onM, card_onT, card_onL] at hprod
  omega

private theorem pv_mem_range_conj_of_forall_mem_sylow
    (T : Sylow 2 Pv) {α : MulAut Pv} (hα : ∀ x ∈ (T : Subgroup Pv), α x = x) :
    α ∈ (MulAut.conj : Pv →* MulAut Pv).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hout
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Pv T onTSylow
  have hconj : (onTSylow : Subgroup Pv) = (T : Subgroup Pv).map (MulAut.conj g).toMonoidHom := by
    have h := congrArg (fun S : Sylow 2 Pv => (S : Subgroup Pv)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    convert h.symm using 2
    ext x
    rfl
  set k : MulAut Pv := MulAut.conj g with hk
  set α' : MulAut Pv := k * α * k⁻¹ with hα'def
  have hout' : α' ∉ (MulAut.conj : Pv →* MulAut Pv).range := by
    intro h
    apply hout
    have heq : α = k⁻¹ * α' * k := by rw [hα'def]; group
    rw [heq]
    have hkrange : k ∈ (MulAut.conj : Pv →* MulAut Pv).range := ⟨g, by rw [hk]⟩
    exact mul_mem (mul_mem (inv_mem hkrange) h) hkrange
  have hfixT : ∀ x ∈ (onTSylow : Subgroup Pv), α' x = x := by
    intro x hx
    rw [hconj] at hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    show (k * α * k⁻¹) (k t) = k t
    rw [MulAut.mul_apply, MulAut.mul_apply]
    have h1 : k⁻¹ (k t) = t := by
      rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rw [h1, hα t ht]
  have hz : α' zP = zP := by
    have hzT : zP ∈ (onTSylow : Subgroup Pv) := by
      rw [onTSylow_coe]
      exact Subgroup.mem_subgroupOf.mpr onz_mem_T
    exact hfixT zP hzT
  obtain ⟨-, hLm, -, A, hA⟩ :=
    CFSG.Sporadic.ONOddCore.ctuc_on_outer_local_quotient_is_graph_or_field.2.2 α' hout' hz
  let V : Subgroup onL := (onT ⊓ onL : Subgroup (Equiv.Perm (Fin N))).subgroupOf onL
  have hcardV : Nat.card V = 256 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := onT ⊓ onL) (K := onL) inf_le_right).toEquiv]
    exact onan_card_inf_onT_onL
  let φ : V →* LinearFlag.projectiveSL 3 PSL3Four.F4 := lToS.comp V.subtype
  have hQleV : onQ.subgroupOf onL ≤ V := by
    intro q hq
    rw [Subgroup.mem_subgroupOf] at hq ⊢
    exact Subgroup.mem_inf.mpr ⟨onan_onQ_le_onT hq, q.2⟩
  have hker : φ.ker = (onQ.subgroupOf onL).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change lToS (V.subtype v) = 1 ↔ (V.subtype v : onL) ∈ onQ.subgroupOf onL
    rw [← MonoidHom.mem_ker, ← ker_lToS]
  have hcardker : Nat.card φ.ker = 4 := by
    rw [hker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleV).toEquiv]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onQ_le_L).toEquiv]
    exact card_onQ
  let W : Subgroup (LinearFlag.projectiveSL 3 PSL3Four.F4) := φ.range
  have hcardW : Nat.card W = 64 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hcardker, hcardV] at h
    change 4 * Nat.card W = 256 at h
    omega
  have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 6) (by rw [hcardW]; norm_num)
  have hcardS : Nat.card (LinearFlag.projectiveSL 3 PSL3Four.F4) = 20160 := by
    have h := Subgroup.card_ker_mul_card_range lToS
    rw [ker_lToS, MonoidHom.range_eq_top.2 lToS_surjective] at h
    have hQ : Nat.card (onQ.subgroupOf onL) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onQ_le_L).toEquiv]
      exact card_onQ
    rw [hQ, Subgroup.card_top, card_onL] at h
    omega
  have hWidx : ¬ 2 ∣ W.index := by
    have h := W.card_mul_index
    rw [hcardW, hcardS] at h
    have hi : W.index = 315 := by omega
    rw [hi]; decide
  let U : Sylow 2 (LinearFlag.projectiveSL 3 PSL3Four.F4) := hWp.toSylow hWidx
  have hUcoe : (U : Subgroup _) = W := IsPGroup.toSylow_coe _ _
  have hfix : ∀ (ψ : MulAut (LinearFlag.projectiveSL 3 PSL3Four.F4)),
      (∀ a a' : onL, (a' : Equiv.Perm (Fin N)) =
        ((α' ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) : Equiv.Perm (Fin N)) →
        lToS a' = ψ (lToS a)) →
      ∀ x ∈ (U : Subgroup _), ψ x = x := by
    intro ψ hψ x hx
    rw [hUcoe] at hx
    change x ∈ φ.range at hx
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.1 hx
    have hpermT : (((v : V) : onL) : Equiv.Perm (Fin N)) ∈ onT := by
      have hv : ((v : V) : onL) ∈ (onT ⊓ onL).subgroupOf onL := v.2
      rw [Subgroup.mem_subgroupOf] at hv
      exact (Subgroup.mem_inf.1 hv).1
    have hp : α' (⟨(((v : V) : onL) : Equiv.Perm (Fin N)),
        onM_le (onL_le_M ((v : V) : onL).2)⟩ : Pv) =
        ⟨(((v : V) : onL) : Equiv.Perm (Fin N)),
          onM_le (onL_le_M ((v : V) : onL).2)⟩ := by
      apply hfixT
      rw [onTSylow_coe, Subgroup.mem_subgroupOf]
      exact hpermT
    have hcond : (((v : V) : onL) : Equiv.Perm (Fin N)) =
        ((α' ⟨((v : V) : onL), onM_le (onL_le_M ((v : V) : onL).2)⟩ : Pv) :
          Equiv.Perm (Fin N)) := by
      rw [hp]
    have h := hψ ((v : V) : onL) ((v : V) : onL) hcond
    have hφ : φ v = lToS ((v : V) : onL) := rfl
    rw [hφ]
    exact h.symm
  rcases hA with hA | hA
  · exact CFSG.ComponentClassification.PSL3Four.false_of_graph_or_field_fixes_sylow U A
      (Or.inl (hfix _ hA))
  · exact CFSG.ComponentClassification.PSL3Four.false_of_graph_or_field_fixes_sylow U A
      (Or.inr (hfix _ hA))

variable {Y : Type} [Group Y]

theorem mem_range_conj_of_forall_mem_sylow_onan
    [Finite Y] (hY : IsSporadic Y .ONan)
    (T : Sylow 2 Y) {α : MulAut Y} (hα : ∀ x ∈ (T : Subgroup Y), α x = x) :
    α ∈ (MulAut.conj : Y →* MulAut Y).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := hY
  have e₁ : Y ≃* CFSG.Blueprint.NativeSporadic.ON := e₀
  let e : Y ≃* Pv := e₁.trans onEquivPv
  set β : MulAut Pv := MulAut.congr e α with hβ
  let T' : Sylow 2 Pv := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T
  have hT'coe : (T' : Subgroup Pv) = (T : Subgroup Y).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective T
  have hfixβ : ∀ x ∈ (T' : Subgroup Pv), β x = x := by
    intro x hx
    rw [hT'coe] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    show e (α (e.symm (e y))) = e y
    rw [MulEquiv.symm_apply_apply, hα y hy]
  obtain ⟨p, hp⟩ := pv_mem_range_conj_of_forall_mem_sylow T' hfixβ
  refine ⟨e.symm p, ?_⟩
  apply (MulAut.congr e).injective
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e (e.symm p),
    MulEquiv.apply_symm_apply, ← hβ, hp]

end SylowFixed

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
