module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3Cover
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open scoped commutatorElement

section Model

variable {Y : Type} [Group Y]

private theorem exists_mulEquiv_pv_of_orderOf_eq_two
    (hY : IsSporadic Y .ONan) {a : Y} (ha : orderOf a = 2) :
    ∃ e : Y ≃* CFSG.ONSchreier.Pv, e a = CFSG.ONSchreier.zP := by
  obtain ⟨e₀⟩ := hY
  let e : Y ≃* CFSG.Blueprint.NativeSporadic.ON := e₀
  let eP : Y ≃* CFSG.ONSchreier.Pv := e.trans CFSG.ONSchreier.onEquivPv
  have hb : orderOf (eP a) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ha
  obtain ⟨g, hg⟩ := CFSG.EvenSporadicStandard.Solomon78.pv_conj_zP (eP a) hb
  refine ⟨eP.trans (MulAut.conj g⁻¹), ?_⟩
  show MulAut.conj g⁻¹ (eP a) = CFSG.ONSchreier.zP
  rw [hg, MulAut.conj_apply]
  group

theorem commutator_commutator_centralizer_onan
    (hY : IsSporadic Y .ONan) {a : Y} (ha : orderOf a = 2) :
    ⁅(⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ : Subgroup Y),
        ⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆⁆ =
      ⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ := by
  obtain ⟨e', he'a⟩ := exists_mulEquiv_pv_of_orderOf_eq_two hY ha
  have hSmap := map_commutator_centralizer_eq_onL e' a he'a
  let L : Subgroup Y := ⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆
  let S : Subgroup CFSG.ONSchreier.Pv :=
    CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.Pv
  have hSS : ⁅S, S⁆ = S := by
    apply Subgroup.map_injective CFSG.ONSchreier.Pv.subtype_injective
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le CFSG.ONSchreier.onL_le]
    exact CFSG.ONSchreier.onL_commutator
  change ⁅L, L⁆ = L
  apply Subgroup.map_injective (f := e'.toMonoidHom) e'.injective
  rw [Subgroup.map_commutator, hSmap]
  exact hSS

theorem lieModel_commutator_centralizer_onan
    (hY : IsSporadic Y .ONan) {a : Y} (ha : orderOf a = 2) :
    Blueprint.LieModel
      (↥(⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ : Subgroup Y) ⧸
        center ↥(⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ : Subgroup Y))
      .PSL 3 2 2 := by
  obtain ⟨e', he'a⟩ := exists_mulEquiv_pv_of_orderOf_eq_two hY ha
  have hSmap := map_commutator_centralizer_eq_onL e' a he'a
  let L : Subgroup Y := ⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆
  let S : Subgroup CFSG.ONSchreier.Pv :=
    CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.Pv
  have heS : L ≃* S :=
    (Subgroup.equivMapOfInjective L e'.toMonoidHom e'.injective).trans
      (MulEquiv.subgroupCongr hSmap)
  have heSL : S ≃* CFSG.ONSchreier.onL :=
    Subgroup.subgroupOfEquivOfLe CFSG.ONSchreier.onL_le
  have hcenter : Subgroup.center CFSG.ONSchreier.onL =
      CFSG.Sporadic.ONOddCore.lToS.ker := by
    rw [CFSG.ONSchreier.center_L, CFSG.ONSchreier.rhoL_ker,
      CFSG.Sporadic.ONOddCore.ker_lToS]
  let eQ1 : (L ⧸ Subgroup.center L) ≃* (S ⧸ Subgroup.center S) :=
    QuotientGroup.congr (Subgroup.center L) (Subgroup.center S) heS
      (Subgroup.map_center_eq heS)
  let eQ2 : (S ⧸ Subgroup.center S) ≃*
      (CFSG.ONSchreier.onL ⧸ Subgroup.center CFSG.ONSchreier.onL) :=
    QuotientGroup.congr (Subgroup.center S) (Subgroup.center CFSG.ONSchreier.onL) heSL
      (Subgroup.map_center_eq heSL)
  let eQ3 : (CFSG.ONSchreier.onL ⧸ Subgroup.center CFSG.ONSchreier.onL) ≃*
      (CFSG.ONSchreier.onL ⧸ CFSG.Sporadic.ONOddCore.lToS.ker) :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  let eQ4 : (CFSG.ONSchreier.onL ⧸ CFSG.Sporadic.ONOddCore.lToS.ker) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 CFSG.ComponentClassification.PSL3Four.F4 :=
    QuotientGroup.quotientKerEquivOfSurjective
      (φ := CFSG.Sporadic.ONOddCore.lToS) CFSG.Sporadic.ONOddCore.lToS_surjective
  let eQ : (L ⧸ Subgroup.center L) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 CFSG.ComponentClassification.PSL3Four.F4 :=
    eQ1.trans (eQ2.trans (eQ3.trans eQ4))
  change Blueprint.LieModel (L ⧸ Subgroup.center L) .PSL 3 2 2
  refine Blueprint.LieModel.of_mulEquiv eQ.symm ?_
  exact CFSG.QuasithinUnique.Fin257.L3.lieModel_L3 (n := 2) (by norm_num)
    (by rw [CFSG.ComponentClassification.PSL3Four.natCard_F4]; norm_num)

theorem exists_center_commutator_centralizer_onan
    (hY : IsSporadic Y .ONan) {a : Y} (ha : orderOf a = 2) :
    ∃ q : Y, orderOf q = 4 ∧ q * q = a ∧
      (center ↥(⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ : Subgroup Y)).map
        (⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ : Subgroup Y).subtype =
        zpowers q := by
  obtain ⟨e', he'a⟩ := exists_mulEquiv_pv_of_orderOf_eq_two hY ha
  have hSmap := map_commutator_centralizer_eq_onL e' a he'a
  let L : Subgroup Y := ⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆
  let S : Subgroup CFSG.ONSchreier.Pv :=
    CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.Pv
  let u : CFSG.ONSchreier.Pv :=
    ⟨CFSG.ONSchreier.onq, CFSG.ONSchreier.onL_le CFSG.ONSchreier.onq_mem_L⟩
  have huord : orderOf u = 4 := by
    rw [Subgroup.orderOf_mk, CFSG.ONSchreier.orderOf_onq]
  have hu2 : u * u = CFSG.ONSchreier.zP := by
    apply Subtype.ext
    show CFSG.ONSchreier.onq * CFSG.ONSchreier.onq = CFSG.ONSchreier.onz
    rw [CFSG.ONSchreier.onz_eq_q2, pow_two]
  have hcenterS : CFSG.centerIn S = Subgroup.zpowers u := by
    have hsub : CFSG.centerIn S = (CFSG.centerIn CFSG.ONSchreier.onL).subgroupOf
        CFSG.ONSchreier.Pv := by
      rw [CFSG.centerIn, CFSG.centerIn,
        CFSG.QuasiDihedralFusion.centralizer_subgroupOf CFSG.ONSchreier.onL_le]
      ext x
      simp only [S, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [hsub, CFSG.ONSchreier.onL_centerIn, CFSG.ONSchreier.onQ]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, Subtype.ext ?_⟩
      simpa using hk
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simpa using congrArg Subtype.val hk
  have hcenterMap : (CFSG.centerIn L).map e'.toMonoidHom = CFSG.centerIn S := by
    have himg : e'.toMonoidHom '' (L : Set Y) = (S : Set CFSG.ONSchreier.Pv) := by
      rw [← Subgroup.coe_map e'.toMonoidHom L, hSmap]
    rw [CFSG.centerIn, CFSG.centerIn, Subgroup.map_inf L _ e'.toMonoidHom e'.injective,
      CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv, himg, hSmap]
  refine ⟨e'.symm u, ?_, ?_, ?_⟩
  · rw [← MulEquiv.orderOf_eq e' (e'.symm u), MulEquiv.apply_symm_apply]
    exact huord
  · apply e'.injective
    rw [map_mul, MulEquiv.apply_symm_apply, he'a]
    exact hu2
  · rw [← CFSG.centerIn_eq_map_center]
    apply Subgroup.map_injective (f := e'.toMonoidHom) e'.injective
    rw [hcenterMap, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    exact hcenterS

theorem exists_noncentral_involution_commutator_centralizer_onan
    (hY : IsSporadic Y .ONan) {a : Y} (ha : orderOf a = 2) :
    ∃ u ∈ (⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ : Subgroup Y),
      orderOf u = 2 ∧
        ∃ x ∈ (⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ : Subgroup Y),
          u * x ≠ x * u := by
  obtain ⟨e', he'a⟩ := exists_mulEquiv_pv_of_orderOf_eq_two hY ha
  have hSmap := map_commutator_centralizer_eq_onL e' a he'a
  let L : Subgroup Y := ⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆
  let S : Subgroup CFSG.ONSchreier.Pv :=
    CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.Pv
  have hTleM : CFSG.ONSchreier.onT ≤ CFSG.ONSchreier.onM := by
    rw [CFSG.ONSchreier.onM_eq_centralizer_z]
    intro t ht
    refine ⟨CFSG.ONSchreier.onT_le ht,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hz : CFSG.ONSchreier.onz ∈ CFSG.centerIn CFSG.ONSchreier.onT := by
      rw [CFSG.ONSchreier.onT_centerIn]
      exact Subgroup.mem_zpowers _
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 t ht)
  have hsq : CFSG.Sporadic.ONOddCore.sqP ≤ CFSG.ONSchreier.onL := by
    rw [CFSG.Sporadic.ONOddCore.sqP, Subgroup.closure_le]
    rintro x ⟨t, ht, rfl⟩
    have htM : t ∈ CFSG.ONSchreier.onM := hTleM ht
    have h2 : (CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.onM).index = 2 :=
      CFSG.ONSchreier.onL_relIndex
    have hmem := Subgroup.mul_self_mem_of_index_two
      (H := CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.onM) h2
      (⟨t, htM⟩ : CFSG.ONSchreier.onM)
    exact Subgroup.mem_subgroupOf.1 hmem
  have homegaL : CFSG.Sporadic.ONOddCore.omegaP ≤ CFSG.ONSchreier.onL := by
    refine (show CFSG.Sporadic.ONOddCore.omegaP ≤ CFSG.Sporadic.ONOddCore.sqP from ?_).trans hsq
    rw [CFSG.Sporadic.ONOddCore.omegaP, Subgroup.closure_le]
    rintro x ⟨hx, -⟩
    exact hx
  have hnot : ¬ CFSG.Sporadic.ONOddCore.omegaP ≤ CFSG.ONSchreier.onQ := by
    intro h
    have hcard : Nat.card CFSG.Sporadic.ONOddCore.omegaP ≤
        Nat.card CFSG.ONSchreier.onQ := Subgroup.card_le_of_le h
    rw [CFSG.Sporadic.ONOddCore.card_omegaP, CFSG.ONSchreier.card_onQ] at hcard
    norm_num at hcard
  obtain ⟨u, huomega, huQ⟩ : ∃ u ∈ CFSG.Sporadic.ONOddCore.omegaP,
      u ∉ CFSG.ONSchreier.onQ := by
    by_contra h
    push Not at h
    exact hnot fun x hx => h x hx
  have huL : u ∈ CFSG.ONSchreier.onL := homegaL huomega
  have hu2 : u * u = 1 := by
    have hExp : Monoid.exponent CFSG.Sporadic.ONOddCore.omegaP ∣ 2 :=
      (CFSG.Sporadic.ONOddCore.omegaP_elementary).exponent_dvd_p
    have hpow : ∀ z : CFSG.Sporadic.ONOddCore.omegaP, z ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hExp
    have h := hpow ⟨u, huomega⟩
    simpa [pow_two] using congrArg Subtype.val h
  have huord : orderOf u = 2 := by
    have hne : u ≠ 1 := by
      intro h
      exact huQ (h.symm ▸ Subgroup.one_mem CFSG.ONSchreier.onQ)
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have hnc : ∃ x : Equiv.Perm (Fin CFSG.ONSchreier.N),
      x ∈ CFSG.ONSchreier.onL ∧ u * x ≠ x * u := by
    by_contra h
    push Not at h
    apply huQ
    rw [← CFSG.ONSchreier.onL_centerIn]
    refine Subgroup.mem_inf.2 ⟨huL, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (h x hx).symm
  obtain ⟨x, hxL, hux⟩ := hnc
  let uP : CFSG.ONSchreier.Pv := ⟨u, CFSG.ONSchreier.onL_le huL⟩
  let xP : CFSG.ONSchreier.Pv := ⟨x, CFSG.ONSchreier.onL_le hxL⟩
  have huS : uP ∈ S := Subgroup.mem_subgroupOf.2 huL
  have hxS : xP ∈ S := Subgroup.mem_subgroupOf.2 hxL
  have huY : e'.symm uP ∈ L := by
    rw [← Subgroup.mem_map_iff_mem (f := e'.toMonoidHom) (K := L) e'.injective, hSmap,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact huS
  have hxY : e'.symm xP ∈ L := by
    rw [← Subgroup.mem_map_iff_mem (f := e'.toMonoidHom) (K := L) e'.injective, hSmap,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact hxS
  have huYord : orderOf (e'.symm uP) = 2 := by
    rw [← MulEquiv.orderOf_eq e' (e'.symm uP), MulEquiv.apply_symm_apply]
    rw [Subgroup.orderOf_mk]
    exact huord
  have hncY : e'.symm uP * e'.symm xP ≠ e'.symm xP * e'.symm uP := by
    intro h
    apply hux
    have h' : uP * xP = xP * uP := by
      simpa using congrArg e' h
    simpa using congrArg (fun z : CFSG.ONSchreier.Pv =>
      (z : Equiv.Perm (Fin CFSG.ONSchreier.N))) h'
  exact ⟨e'.symm uP, huY, huYord, e'.symm xP, hxY, hncY⟩

theorem mul_self_mem_commutator_centralizer_onan
    (hY : IsSporadic Y .ONan) {a : Y} (ha : orderOf a = 2) {y : Y}
    (hy : y ∈ centralizer ({a} : Set Y)) :
    y * y ∈ (⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ : Subgroup Y) := by
  obtain ⟨e', he'a⟩ := exists_mulEquiv_pv_of_orderOf_eq_two hY ha
  have hSmap := map_commutator_centralizer_eq_onL e' a he'a
  let L : Subgroup Y := ⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆
  let S : Subgroup CFSG.ONSchreier.Pv :=
    CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.Pv
  have hyC : e' y ∈ Subgroup.centralizer
      ({CFSG.ONSchreier.zP} : Set CFSG.ONSchreier.Pv) := by
    rw [← he'a, ← CFSG.Sporadic.ONOddCore.centralizer_map_equiv e' a]
    exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩
  have hyM : (e' y : Equiv.Perm (Fin CFSG.ONSchreier.N)) ∈ CFSG.ONSchreier.onM := by
    rw [CFSG.ONSchreier.onM_eq_centralizer_z]
    refine Subgroup.mem_inf.2 ⟨(e' y).2, ?_⟩
    rw [CFSG.ONSchreier.centralizer_zP] at hyC
    exact Subgroup.mem_subgroupOf.1 hyC
  have hsq : e' y * e' y ∈ S := by
    rw [Subgroup.mem_subgroupOf]
    have h2 : (CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.onM).index = 2 :=
      CFSG.ONSchreier.onL_relIndex
    have hmem := Subgroup.mul_self_mem_of_index_two
      (H := CFSG.ONSchreier.onL.subgroupOf CFSG.ONSchreier.onM) h2
      (⟨e' y, hyM⟩ : CFSG.ONSchreier.onM)
    have h := Subgroup.mem_subgroupOf.1 hmem
    simpa using h
  change y * y ∈ L
  rw [← Subgroup.mem_map_iff_mem (f := e'.toMonoidHom) (K := L) e'.injective, hSmap]
  rw [map_mul]
  exact hsq

end Model

end CFSG.ComponentClassification.GrSLit.L34Sec5S
