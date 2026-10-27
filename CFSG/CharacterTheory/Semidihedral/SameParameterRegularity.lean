module

public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage
public import CFSG.CharacterTheory.Semidihedral.Local.PerfectSectionOddCore
public import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.Semidihedral.SameParameterRegularity

noncomputable section

open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.GorensteinWalter
open CFSG.Open

theorem kernel_comp_eq_of_layer_image {A B U : Type*} [Group A] [Group B] [Group U]
    (rho : A →* B) (hinj : Function.Injective rho) (theta : B →* U)
    (L : Subgroup A) (hL : L.map rho = theta.ker) : (theta.comp rho).ker = L := by
  ext x
  change theta (rho x) = 1 ↔ x ∈ L
  change rho x ∈ theta.ker ↔ x ∈ L
  rw [← hL]
  constructor
  · rintro ⟨y, hy, heq⟩
    exact hinj heq ▸ hy
  · intro hx
    exact Subgroup.mem_map_of_mem rho hx

theorem quotient_isMulCommutative_of_kernel {A U : Type*} [Group A] [Group U]
    [IsMulCommutative U] (L : Subgroup A) [L.Normal] (theta : A →* U)
    (hker : theta.ker = L) : IsMulCommutative (A ⧸ L) := by
  let f : A ⧸ L →* U := QuotientGroup.lift L theta hker.ge
  have hf : Function.Injective f :=
    (QuotientGroup.injective_lift_iff L theta hker.ge).mpr hker.symm
  exact IsMulCommutative.of_comm fun a b => hf (by
    simp only [map_mul]
    exact mul_comm' _ _)

theorem centralizer_preimage_le_ker {A B : Type*} [Group A] [Group B]
    (pi : A →* B) (hpi : Function.Surjective pi) (L : Subgroup B)
    (hcentral : Subgroup.centralizer (L : Set B) = ⊥) :
    Subgroup.centralizer (L.comap pi : Set A) ≤ pi.ker := by
  intro x hx
  have himage : pi x ∈ Subgroup.centralizer (L : Set B) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨y, rfl⟩ := hpi l
    have hxy := Subgroup.mem_centralizer_iff.mp hx y hl
    simpa only [map_mul] using congrArg pi hxy
  rw [hcentral, Subgroup.mem_bot] at himage
  exact himage

theorem odd_normal_subgroup_eq_bot_of_sl_equiv {A : Type*} [Group A]
    (F : Type*) [Field F] [Finite F]
    (e : A ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) (hF : 3 ≤ Nat.card F) :
    ∀ U : Subgroup A, U.Normal → Odd (Nat.card U) → U = ⊥ := by
  intro U hU hUodd
  have hmap := OddLinearNormals.normal_odd_specialLinear_eq_bot F hodd hF
    (U.map e.toMonoidHom) (hU.map e.toMonoidHom e.surjective)
    (by rw [Subgroup.card_map_of_injective e.injective]; exact hUodd)
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  simpa only [Subgroup.map_bot] using hmap

theorem card_specialLinear_two (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  let : Fintype F := Fintype.ofFinite F
  let q := Nat.card F
  have hq : 2 ≤ q := Finite.one_lt_card
  have hsq : q ^ 2 - q = q * (q - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
  rw [Matrix.card_SL_field 2, Fin.prod_univ_two]
  rw [← Nat.card_eq_fintype_card]
  change ((q ^ 2 - q ^ 0) * (q ^ 2 - q ^ 1)) / (q - 1) = q * (q ^ 2 - 1)
  rw [pow_zero, pow_one, hsq, ← mul_assoc, Nat.mul_div_cancel]
  · exact Nat.mul_comm _ _
  · omega

theorem actual_matrix_layer_properties {G : Type} [Group G]
    (t : G) (n p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hq : 5 ≤ p ^ f) (F : Type) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) (rho : Gamma t →* coordinateE F)
    (data : ActualMatrixData t n p f F A rho)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hz : orderOf (nu t (tInC t)) = 2) :
    let L := CFSG.generalizedFitting (Gamma t)
    let Q := L.comap (barKappa t)
    Group.IsPerfect Q ∧ Group.IsSolvable ((H t) ⧸ Q) ∧
      (∀ U : Subgroup Q, U.Normal → Odd (Nat.card U) → U = ⊥) ∧
      IsPGroup 2 (Subgroup.centralizer (Q : Set (H t))) ∧
      Nat.card Q = p ^ f * ((p ^ f) ^ 2 - 1) ∧
      ∃ eta : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F,
        ∀ h : nu t (tInC t) ∈ Q, eta ⟨nu t (tInC t), h⟩ = -1 := by
  intro L Q
  obtain ⟨eta, hetaz, -, -⟩ := data.compatible_layer
  have hFodd : Odd (Nat.card F) := data.field_card ▸ hpodd.pow
  have hF5 : 5 ≤ Nat.card F := data.field_card ▸ hq
  have hperfect : Group.IsPerfect Q := by
    have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F (by omega)
    exact Group.IsPerfect.ofSurjective (f := eta.symm.toMonoidHom) eta.symm.surjective
  let hF : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hpodd, hf, data.field_card⟩
  let theta := (SemilinearOuterQuotient.theta F hF).comp rho
  have htheta : theta.ker = L := kernel_comp_eq_of_layer_image rho data.faithful
    (SemilinearOuterQuotient.theta F hF) L
    (data.layer_image.trans (SemilinearOuterQuotient.theta_ker F hF).symm)
  let : IsCyclic (F ≃+* F) := fieldAut_isCyclic F
  have hcompker : (theta.comp (barKappa t)).ker = Q := by
    ext x
    change theta (barKappa t x) = 1 ↔ barKappa t x ∈ L
    change barKappa t x ∈ theta.ker ↔ _
    rw [htheta]
  let : IsMulCommutative ((H t) ⧸ Q) :=
    quotient_isMulCommutative_of_kernel Q (theta.comp (barKappa t)) hcompker
  have hCQ : IsPGroup 2 (Subgroup.centralizer (Q : Set (H t))) := by
    have hle := centralizer_preimage_le_ker (barKappa t) (barKappa_surjective t) L hcentral
    rw [barKappa_kernel t] at hle
    have hZ : IsPGroup 2 (Subgroup.zpowers (nu t (tInC t))) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hz, pow_one]
    exact hZ.to_le hle
  refine ⟨hperfect, inferInstance,
    odd_normal_subgroup_eq_bot_of_sl_equiv F eta hFodd (by omega), hCQ, ?_, eta, ?_⟩
  · rw [Nat.card_congr eta.toEquiv, card_specialLinear_two F, data.field_card]
  · intro h
    simpa using hetaz

@[expose] def subgroupCentralizerEquiv {G : Type*} [Group G]
    (U : Subgroup G) (t : U) : C t ≃* U.comap (C (t : G)).subtype where
  toFun x := ⟨⟨x.val.val, Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.property))⟩,
    x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.val.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem subgroupCentralizerEquiv_coe {G : Type*} [Group G]
    (U : Subgroup G) (t : U) (x : C t) :
    ((subgroupCentralizerEquiv U t x : C (t : G)) : G) = ((x : U) : G) := rfl

theorem subgroupCentralizerEquiv_oddCore {G : Type*} [Group G]
    (U : Subgroup G) (t : U) :
    (N t).map (subgroupCentralizerEquiv U t).toMonoidHom =
      CFSG.pPrimeCore 2 (U.comap (C (t : G)).subtype) :=
  CFSG.pPrimeCore_map_iso 2 (subgroupCentralizerEquiv U t)

@[expose] def subgroupCentralizerOddQuotientEquiv {G : Type*} [Group G]
    (U : Subgroup G) (t : U) :
    H t ≃* ((U.comap (C (t : G)).subtype) ⧸
      CFSG.pPrimeCore 2 (U.comap (C (t : G)).subtype)) :=
  QuotientGroup.congr (N t) _ (subgroupCentralizerEquiv U t)
    (subgroupCentralizerEquiv_oddCore U t)

theorem subgroupCentralizerOddQuotientEquiv_mk {G : Type*} [Group G]
    (U : Subgroup G) (t : U) (x : C t) :
    subgroupCentralizerOddQuotientEquiv U t (nu t x) =
      QuotientGroup.mk' (CFSG.pPrimeCore 2 (U.comap (C (t : G)).subtype))
        (subgroupCentralizerEquiv U t x) :=
  QuotientGroup.congr_mk' _ _ _ _ x

theorem odd_index_of_equal_two_parts {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) (heq : (Nat.card U).factorization 2 = (Nat.card G).factorization 2) :
    Odd U.index := by
  have hindex : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard : Nat.card U ≠ 0 := Nat.card_pos.ne'
  have hmul := congrArg (fun k : ℕ => k.factorization 2) U.card_mul_index
  rw [Nat.factorization_mul hcard hindex, Finsupp.add_apply, heq] at hmul
  have hzero : U.index.factorization 2 = 0 := by omega
  apply Nat.not_even_iff_odd.mp
  intro heven
  have hle := (Nat.prime_two.dvd_iff_one_le_factorization hindex).mp
    (even_iff_two_dvd.mp heven)
  omega

theorem semidihedral_sylow_two_part {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (e : SemidihedralGroup n ≃* S) :
    (Nat.card G).factorization 2 = n := by
  have h := S.card_eq_multiplicity
  rw [← Nat.card_congr e.toEquiv, CFSG.Semidihedral.card n (by omega)] at h
  exact ((Nat.pow_right_inj (by decide : 1 < (2 : ℕ))).mp h).symm

theorem involution_centralizer_two_part {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (e : SemidihedralGroup n ≃* S)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2) :
    (Nat.card (C t)).factorization 2 = n := by
  obtain ⟨St, et, he⟩ := InvolutionFusion.exists_centered_semidihedral_sylow
    n hn S e hG t ht
  have hc : CentralizerResidual.centeredInvolution n St et = t := he
  have := semidihedral_sylow_two_part n hn
    (CentralizerResidual.centralizerSylow n hn St et)
    (CentralizerResidual.centralizerCoordinates n hn St et)
  simpa only [CentralizerResidual.involutionCentralizer, hc] using this

theorem same_parameter_sylow_exponent {G G' : Type} [Group G] [Group G']
    (t : G) (t' : G') (n m p f : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m)
    (F F' : Type) [Field F] [Finite F] [Field F'] [Finite F']
    (A : Subgroup (F ≃+* F)) (A' : Subgroup (F' ≃+* F'))
    (rho : Gamma t →* coordinateE F) (rho' : Gamma t' →* coordinateE F')
    (data : ActualMatrixData t n p f F A rho)
    (data' : ActualMatrixData t' m p f F' A' rho') : n = m := by
  have hleft : 2 ^ (n - 1) = 2 ^ ((p ^ f) ^ 2 - 1).factorization 2 := by
    rw [← data.field_card]
    exact data.two_part.symm
  have hright : 2 ^ ((p ^ f) ^ 2 - 1).factorization 2 = 2 ^ (m - 1) := by
    rw [← data'.field_card]
    exact data'.two_part
  have h := hleft.trans hright
  have hnm := (Nat.pow_right_inj (by decide : 1 < (2 : ℕ))).mp h
  omega

theorem same_parameter_subgroup_centralizer_odd_core_intersection {G : Type}
    [Group G] [Finite G] (U : Subgroup G) (t : U) (ht : orderOf t = 2)
    (n m : ℕ) (hn : 4 ≤ n) (hm : 4 ≤ m)
    (S : Sylow 2 G) (eS : SemidihedralGroup n ≃* S)
    (SU : Sylow 2 U) (eSU : SemidihedralGroup m ≃* SU)
    (hG : ∀ V : Subgroup G, V.index ≠ 2)
    (hU : ∀ V : Subgroup U, V.index ≠ 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma (t : G)))]
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma (t : G)), a * b ≠ b * a)
    (hnonabU : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma (t : G)) : Set (Gamma (t : G))) = ⊥)
    (hcentralU : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma (t : G))), ¬ IsCyclic V)
    (hncU : ∀ V : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic V)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma (t : G))) .PSL 2 p f)
    (hmodelU : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    let B := U.comap (C (t : G)).subtype
    let Q := (CFSG.generalizedFitting (Gamma (t : G))).comap (barKappa (t : G))
    (N t).map (B.subtype.comp (subgroupCentralizerEquiv U t).toMonoidHom) =
      B ⊓ N (t : G) ∧ Q ≤ B.map (nu (t : G)) ∧
      (∃ iota : H t →* H (t : G), Function.Injective iota ∧
        (∀ b : C t, iota (nu t b) = nu (t : G) (subgroupCentralizerEquiv U t b)) ∧
        iota.range = B.map (nu (t : G))) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      n = m ∧ Odd U.index ∧ Odd B.index := by
  intro B Q
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  obtain ⟨F, fieldF, finiteF, A, rho, data⟩ := actual_simple_layer_matrix_data
    n hn S eS hG (t : G) htG hnonab hcentral hnc p f hp hpodd hf hmodel
  let : Field F := fieldF
  let : Finite F := finiteF
  obtain ⟨FU, fieldFU, finiteFU, AU, rhoU, dataU⟩ := actual_simple_layer_matrix_data
    m hm SU eSU hU t ht hnonabU hcentralU hncU p f hp hpodd hf hmodelU
  let : Field FU := fieldFU
  let : Finite FU := finiteFU
  obtain ⟨-, -, hzG, -⟩ := actual_quotient_inputs n hn S eS hG (t : G) htG
  obtain ⟨-, -, hzU, -⟩ := actual_quotient_inputs m hm SU eSU hU t ht
  obtain ⟨-, hsolv, hQodd, hCQ, hcardQ, eta, -⟩ := actual_matrix_layer_properties
    (t : G) n p f hp hpodd hf hq F A rho data hcentral hzG
  let QU := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
  obtain ⟨hperfectU, -, hQUodd, -, hcardQU, -, -⟩ := actual_matrix_layer_properties
    t m p f hp hpodd hf hq FU AU rhoU dataU hcentralU hzU
  let eb := subgroupCentralizerOddQuotientEquiv U t
  let Q0 := QU.map eb.toMonoidHom
  let : QU.Normal := inferInstance
  let : Q0.Normal := Subgroup.Normal.map inferInstance eb.toMonoidHom eb.surjective
  let : Group.IsPerfect QU := hperfectU
  have hperfect0 : Group.IsPerfect Q0 := Group.IsPerfect.map eb.toMonoidHom
  have hcard0 : Nat.card Q0 = Nat.card Q := by
    change Nat.card (QU.map eb.toMonoidHom) = Nat.card Q
    have hmap : Nat.card (QU.map eb.toMonoidHom) = Nat.card QU :=
      Subgroup.card_map_of_injective (f := eb.toMonoidHom)
        (show Function.Injective eb.toMonoidHom from eb.injective)
    exact hmap.trans (hcardQU.trans hcardQ.symm)
  have hQ0odd : ∀ V : Subgroup Q0, V.Normal → Odd (Nat.card V) → V = ⊥ := by
    let eq0 : QU ≃* Q0 := QU.equivMapOfInjective eb.toMonoidHom eb.injective
    intro V hV hVodd
    have hmap := hQUodd (V.map eq0.symm.toMonoidHom)
      (hV.map eq0.symm.toMonoidHom eq0.symm.surjective)
      (by rw [Subgroup.card_map_of_injective eq0.symm.injective]; exact hVodd)
    apply Subgroup.map_injective (f := eq0.symm.toMonoidHom) eq0.symm.injective
    simpa only [Subgroup.map_bot] using hmap
  obtain ⟨hR, hQB, iota0, hiota0, hrep0, hrange0⟩ :=
    Local.equal_perfect_section_forces_local_odd_core_intersection
      (N (t : G)) (Nat.coprime_two_left.mp
        (CFSG.pPrimeCore_coprime_card (p := 2) (G := C (t : G))))
      Q hsolv hQodd hCQ B Q0 hperfect0 hcard0 hQ0odd
  have hnm : n = m := same_parameter_sylow_exponent (t : G) t n m p f hn hm
    F FU A AU rho rhoU data dataU
  have hBcard : Nat.card B = Nat.card (C t) :=
    (Nat.card_congr (subgroupCentralizerEquiv U t).toEquiv).symm
  refine ⟨?_, hQB, ?_, ⟨F, fieldF, finiteF, data.field_card, ⟨eta⟩⟩, hnm, ?_, ?_⟩
  · rw [← Subgroup.map_map, subgroupCentralizerEquiv_oddCore]
    exact hR
  · refine ⟨iota0.comp eb.toMonoidHom, hiota0.comp eb.injective, ?_, ?_⟩
    · intro b
      change iota0 (eb (nu t b)) = _
      rw [subgroupCentralizerOddQuotientEquiv_mk]
      exact hrep0 _
    · have hr : eb.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr
        (show Function.Surjective eb.toMonoidHom from eb.surjective)
      rw [MonoidHom.range_comp, hr, Subgroup.map_top]
      exact hrange0
  · apply odd_index_of_equal_two_parts
    rw [semidihedral_sylow_two_part n hn S eS, semidihedral_sylow_two_part m hm SU eSU]
    exact hnm.symm
  · apply odd_index_of_equal_two_parts
    rw [hBcard, involution_centralizer_two_part m hm SU eSU hU t ht,
      involution_centralizer_two_part n hn S eS hG (t : G) htG]
    exact hnm.symm

end

end CFSG.Semidihedral.SameParameterRegularity
