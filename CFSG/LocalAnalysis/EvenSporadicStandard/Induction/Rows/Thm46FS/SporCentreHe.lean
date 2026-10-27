module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SporCentreTransport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZModel

public noncomputable section

namespace CFSG.EvenSporadicStandard.Induction.SporCentre

open CFSG CFSG.LocalCores Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GrSLit CFSG.PSL3Four.Native
  CFSG.ComponentClassification.UnbalancedGS

section He


theorem comap_heD_eq_layer :
    (genGroup 105 heDGens heDPerm).comap HeLay.rho0 =
      pLayer ↥(centralizerIn heP (heGenPerm 0)) 2 := by
  ext x
  constructor
  · exact fun hx => HeGS.mem_layer_of_rho0_mem hx
  · intro hx
    rw [← HeGS.layer_facts.2.2]
    exact Subgroup.mem_map_of_mem _ hx

theorem ker_rho0_le_commutator :
    HeLay.rho0.ker ≤ ⁅(genGroup 105 heDGens heDPerm).comap HeLay.rho0,
      (genGroup 105 heDGens heDPerm).comap HeLay.rho0⁆ := by
  intro x hx
  have hxD : x ∈ (genGroup 105 heDGens heDPerm).comap HeLay.rho0 := by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact one_mem _
  rw [comap_heD_eq_layer] at hxD ⊢
  rw [HeGS.layer_facts.2.1]
  exact hxD

theorem orderOf_eq_two_of_mem_conjClass {p : Equiv.Perm (Fin 8330)}
    (hp : p ∈ CFSG.Sporadic.Schreier.conjClass heP (heGenPerm 0)) : orderOf p = 2 := by
  obtain ⟨c, -, rfl⟩ := hp
  rw [orderOf_conj_eq, orderOf_heA0]

theorem ker_rho0_mul_self {k : ↥(centralizerIn heP (heGenPerm 0))} (hk : k ∈ HeLay.rho0.ker) :
    k * k = 1 := by
  rcases HeGS.mem_ker_rho0 hk with rfl | rfl | rfl | rfl
  · exact one_mul 1
  · exact Subtype.ext HeGS.heGenPerm0_sq
  · refine Subtype.ext ?_
    have h := orderOf_eq_two_of_mem_conjClass HeGS.heGSU_mem_conjClass
    rw [Subgroup.coe_mul, ← sq, ← h, pow_orderOf_eq_one]
    rfl
  · refine Subtype.ext ?_
    have h := orderOf_eq_two_of_mem_conjClass HeGS.heGST0U_mem_conjClass
    show (heGenPerm 0 * (HeGS.heGSU : Equiv.Perm (Fin 8330))) *
      (heGenPerm 0 * (HeGS.heGSU : Equiv.Perm (Fin 8330))) = 1
    rw [← sq, ← h, pow_orderOf_eq_one]

theorem nonempty_center_equiv_kleinFour_of_component_C0
    {B : Subgroup ↥(centralizerIn heP (heGenPerm 0))} (hB : IsComponent B) :
    Nonempty (center B ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  have hk4 := HeLay.card_rho0_ker
  have hsurj : Function.Surjective (HeLay.rho0.rangeRestrict) :=
    MonoidHom.rangeRestrict_surjective HeLay.rho0
  have hker : Group.IsSolvable HeLay.rho0.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have hp : IsPGroup 2 HeLay.rho0.ker := IsPGroup.of_card (n := 2) (by rw [hk4]; norm_num)
    have : Group.IsNilpotent HeLay.rho0.ker := hp.isNilpotent
    infer_instance
  have hNab : ∀ x ∈ HeLay.rho0.rangeRestrict.ker, ∀ y ∈ HeLay.rho0.rangeRestrict.ker,
      x * y = y * x := fun x hx y hy => by
    rw [MonoidHom.ker_rangeRestrict] at hx hy
    exact HeGS.ker_comm hx hy
  obtain ⟨⟨hDs, hDnab⟩, -, hDle, hDi⟩ := heD_facts
  have hDle' : genGroup 105 heDGens heDPerm ≤ HeLay.rho0.range := by
    rw [HeLay.rho0_range]
    exact hDle
  have hDi' : ((genGroup 105 heDGens heDPerm).subgroupOf HeLay.rho0.range).index = 2 := by
    rw [HeLay.rho0_range]
    exact hDi
  let eD : (genGroup 105 heDGens heDPerm).subgroupOf HeLay.rho0.range ≃*
      genGroup 105 heDGens heDPerm := subgroupOfEquivOfLe hDle'
  have hs : IsSimpleGroup ((genGroup 105 heDGens heDPerm).subgroupOf HeLay.rho0.range) :=
    eD.isSimpleGroup
  have hnc : ∃ a b : (genGroup 105 heDGens heDPerm).subgroupOf HeLay.rho0.range,
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hDnab
    refine ⟨eD.symm a, eD.symm b, fun h => hab ?_⟩
    have := congrArg eD h
    simpa using this
  have hcomap : ((genGroup 105 heDGens heDPerm).subgroupOf HeLay.rho0.range).comap
      HeLay.rho0.rangeRestrict = (genGroup 105 heDGens heDPerm).comap HeLay.rho0 := rfl
  have hle : HeLay.rho0.rangeRestrict.ker ≤
      ⁅((genGroup 105 heDGens heDPerm).subgroupOf HeLay.rho0.range).comap
        HeLay.rho0.rangeRestrict, ((genGroup 105 heDGens heDPerm).subgroupOf
        HeLay.rho0.range).comap HeLay.rho0.rangeRestrict⁆ := by
    rw [hcomap, MonoidHom.ker_rangeRestrict]
    exact ker_rho0_le_commutator
  obtain ⟨c⟩ := nonempty_center_equiv_ker HeLay.rho0.rangeRestrict hsurj hker hNab hDi' hs hnc
    hle hB
  have e1 : HeLay.rho0.rangeRestrict.ker ≃* HeLay.rho0.ker :=
    MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict _)
  have hsq : ∀ x : ↥HeLay.rho0.ker, x ^ 2 = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact ker_rho0_mul_self x.2)
  obtain ⟨e2⟩ := nonempty_mulEquiv_of_card_four hk4 hsq
  exact ⟨(c.trans e1).trans e2⟩

theorem nonempty_center_equiv_kleinFour
    {S : Type*} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.He) {a : S} (ha : orderOf a = 2) {Q : Subgroup S}
    (hQC : Q ≤ centralizer ({a} : Set S))
    (hQ : IsComponent (Q.subgroupOf (centralizer ({a} : Set S)))) :
    Nonempty (center Q ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  set f : S ≃* ↥heP := e.trans heEquivP
  have ha' : orderOf ((f a : ↥heP) : Equiv.Perm (Fin 8330)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha]
  have g1 := centralizerEquivInf heP f a
  rcases involution_conj_cases (f a).2 ha' with ⟨c, hc, hca⟩ | ⟨c, hc, hca⟩
  · have g2 : ↥(heP ⊓ centralizer ({((f a : ↥heP) : Equiv.Perm (Fin 8330))} :
        Set (Equiv.Perm (Fin 8330)))) ≃* ↥(centralizerIn heP (heGenPerm 0)) :=
      (MulEquiv.subgroupCongr (by rw [hca])).trans (infCentralizerConjEquiv hc (heGenPerm 0))
    exact nonempty_center_equiv_of_component (g1.trans g2)
      (fun B hB => nonempty_center_equiv_kleinFour_of_component_C0 hB) hQC hQ
  · exfalso
    have g2 : ↥(heP ⊓ centralizer ({((f a : ↥heP) : Equiv.Perm (Fin 8330))} :
        Set (Equiv.Perm (Fin 8330)))) ≃* ↥heInnerGrp1 :=
      ((MulEquiv.subgroupCongr (by rw [hca])).trans (infCentralizerConjEquiv hc heT1P)).trans
        (MulEquiv.subgroupCongr heInnerGrp1_eq.symm)
    exact heC1_no_component _ (isComponent_map_mulEquiv (g1.trans g2) hQ)

end He

end CFSG.EvenSporadicStandard.Induction.SporCentre
