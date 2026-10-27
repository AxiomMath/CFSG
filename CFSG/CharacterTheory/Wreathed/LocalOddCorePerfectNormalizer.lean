module

public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
public import CFSG.CharacterTheory.Wreathed.OriginalSylowCentralizerCoverage
public import CFSG.CharacterTheory.Wreathed.OriginalScalarSylowCoverage
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeNonabelian
public import CFSG.Foundations.QuasisimpleMulEquiv

public noncomputable section
open scoped Classical Pointwise
namespace CFSG.Wreathed.LocalOddCorePerfectNormalizer
universe u
variable {G : Type u} [Group G]

@[expose] def normalProductCosetEquiv (R X : Subgroup G) [R.Normal] :
    R ⧸ X.subgroupOf R ≃ ↥(R ⊔ X) ⧸ X.subgroupOf (R ⊔ X) := by
  let f : R ⧸ X.subgroupOf R → ↥(R ⊔ X) ⧸ X.subgroupOf (R ⊔ X) :=
    Quotient.map' (Subgroup.inclusion (le_sup_left : R ≤ R ⊔ X)) (by
      intro a b h
      rw [QuotientGroup.leftRel_apply] at h ⊢
      change (a : G)⁻¹ * (b : G) ∈ X at h
      change (a : G)⁻¹ * (b : G) ∈ X
      exact h)
  apply Equiv.ofBijective f
  constructor
  · intro a b
    refine Quotient.ind' (fun a => ?_) a
    refine Quotient.ind' (fun b => ?_) b
    intro h
    change QuotientGroup.mk ((Subgroup.inclusion le_sup_left) a) =
      QuotientGroup.mk ((Subgroup.inclusion le_sup_left) b) at h
    have hm := QuotientGroup.eq.mp h
    apply Quotient.eq''.mpr
    rw [QuotientGroup.leftRel_apply]
    change (a : G)⁻¹ * (b : G) ∈ X at hm
    exact hm
  · intro c
    refine Quotient.ind' (fun c => ?_) c
    obtain ⟨r, hr, x, hx, he⟩ := Subgroup.mem_sup_of_normal_left.mp c.property
    refine ⟨QuotientGroup.mk (⟨r, hr⟩ : R), ?_⟩
    apply QuotientGroup.eq.mpr
    change r⁻¹ * (c : G) ∈ X
    rw [← he, inv_mul_cancel_left]
    exact hx

theorem normalProductCosetEquiv_mk (R X : Subgroup G) [R.Normal] (r : R) :
    normalProductCosetEquiv R X (QuotientGroup.mk r) =
      QuotientGroup.mk (Subgroup.inclusion (le_sup_left : R ≤ R ⊔ X) r) := rfl

theorem relIndex_normal_product (R X : Subgroup G) [R.Normal] :
    X.relIndex (R ⊔ X) = X.relIndex R :=
  Nat.card_congr (normalProductCosetEquiv R X).symm

theorem relIndex_normal_right_dvd_index (R X : Subgroup G) [R.Normal] :
    X.relIndex R ∣ X.index := by
  rw [← relIndex_normal_product R X]
  exact Subgroup.relIndex_dvd_index_of_le le_sup_right

theorem covering_odd_index (R X : Subgroup G) [R.Normal]
    (hR : Odd (Nat.card R)) (hcover : R ⊔ X = ⊤) : Odd X.index := by
  have hi : X.index = X.relIndex R := by
    rw [← Subgroup.relIndex_top_right, ← hcover, relIndex_normal_product]
  rw [hi]
  exact hR.of_dvd_nat (Subgroup.relIndex_dvd_card X R)

theorem covering_lift_intersection_normal (R J X : Subgroup G) [J.Normal]
    (hcomm : ∀ j ∈ J, ∀ r ∈ R, Commute j r) (hcover : R ⊔ X = ⊤) :
    (X ⊓ J).Normal := by
  have hX : X ≤ Subgroup.normalizer (X ⊓ J : Subgroup G) := by
    intro x hx
    apply Subgroup.mem_normalizer_iff.mpr
    intro d
    constructor
    · intro hd
      exact ⟨X.mul_mem (X.mul_mem hx hd.1) (X.inv_mem hx),
        (inferInstance : J.Normal).conj_mem d hd.2 x⟩
    · intro hd
      have he : x⁻¹ * (x * d * x⁻¹) * x = d := by simp [mul_assoc]
      have hXconj : x⁻¹ * (x * d * x⁻¹) * x ∈ X :=
        X.mul_mem (X.mul_mem (X.inv_mem hx) hd.1) hx
      have hJconj : x⁻¹ * (x * d * x⁻¹) * x ∈ J := by
        simpa only [inv_inv] using
          (inferInstance : J.Normal).conj_mem _ hd.2 x⁻¹
      exact ⟨he ▸ hXconj, he ▸ hJconj⟩
  have hRnorm : R ≤ Subgroup.normalizer (X ⊓ J : Subgroup G) := by
    apply (show R ≤ Subgroup.centralizer (X ⊓ J : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro r hr d hd
    exact (hcomm d hd.2 r hr).eq
  apply Subgroup.normalizer_eq_top_iff.mp
  exact top_le_iff.mp (hcover ▸ sup_le hRnorm hX)

theorem odd_kernel_covering_subgroup_contains_centralizing_quasisimple_lift [Finite G]
    (R J X : Subgroup G) [R.Normal] [J.Normal] (hJ : CFSG.IsQuasisimple J)
    (heven : Even (Nat.card (J ⧸ Subgroup.center J)))
    (hR : Odd (Nat.card R)) (_hproduct : J ⊔ R = ⊤)
    (hcomm : ∀ j ∈ J, ∀ r ∈ R, Commute j r)
    (hcover : X ⊔ R = ⊤) : J ≤ X := by
  let : Group.IsPerfect J := hJ.1
  let : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.2.1
  have hc : R ⊔ X = ⊤ := sup_comm X R ▸ hcover
  let D := (X ⊓ J).subgroupOf J
  let : (X ⊓ J).Normal := covering_lift_intersection_normal R J X hcomm hc
  let : D.Normal := inferInstance
  have hXodd : Odd X.index := covering_odd_index R X hR hc
  have hDodd : Odd D.index := by
    change Odd ((X ⊓ J).subgroupOf J).index
    rw [Subgroup.inf_subgroupOf_right]
    exact hXodd.of_dvd_nat (relIndex_normal_right_dvd_index J X)
  let S : Sylow 2 J := Sylow.nonempty.some
  have hSD : (S : Subgroup J) ≤ D :=
    CFSG.Wreathed.two_subgroup_le_normal_of_odd_index (S : Subgroup J) D S.isPGroup' hDodd
  have hDtop : D = ⊤ :=
    PrimewisePerfectLift.normal_Sylow_overgroup_eq_top_of_even_simple_central_quotient
      heven D S hSD
  intro j hj
  have hd : (⟨j, hj⟩ : J) ∈ D := hDtop ▸ Subgroup.mem_top _
  exact hd.1

universe v
variable {A : Type u} {B : Type v} [Group A] [Group B]
open scoped commutatorElement

@[expose] def perfectCentralQuotientEquiv [Group.IsPerfect A]
    (f : A →* B) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center A) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B := by
  let q := (QuotientGroup.mk' (Subgroup.center B)).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have hk : q.ker = Subgroup.center A := by
    have hqker : q.ker = (Subgroup.center B).comap f := by
      ext a
      change (QuotientGroup.mk' (Subgroup.center B)) (f a) = 1 ↔ f a ∈ Subgroup.center B
      exact QuotientGroup.eq_one_iff (f a)
    rw [hqker]
    exact CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel f hf hker
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

theorem nonabelian_of_equiv (e : A ≃* B) (hB : ∃ a b : B, a * b ≠ b * a) :
    ∃ a b : A, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hB
  refine ⟨e.symm a, e.symm b, ?_⟩
  intro he
  apply hab
  have hm := congrArg e he
  simpa only [map_mul, MulEquiv.apply_symm_apply] using hm

theorem perfect_central_extension_quasisimple [Group.IsPerfect A]
    (f : A →* B) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center A) (hB : CFSG.IsQuasisimple B)
    (heven : Even (Nat.card (B ⧸ Subgroup.center B))) :
    CFSG.IsQuasisimple A ∧ Even (Nat.card (A ⧸ Subgroup.center A)) := by
  let e := perfectCentralQuotientEquiv f hf hker
  let : IsSimpleGroup (B ⧸ Subgroup.center B) := hB.2.1
  exact ⟨⟨inferInstance, e.isSimpleGroup, nonabelian_of_equiv e hB.2.2⟩,
    (Nat.card_congr e.toEquiv).symm ▸ heven⟩

theorem odd_inf_two_eq_bot (D T : Subgroup B)
    (hD : Odd (Nat.card D)) (hT : IsPGroup 2 T) : D ⊓ T = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI : IsPGroup 2 (D ⊓ T : Subgroup B) :=
    hT.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  have hodd : Odd (Nat.card (D ⊓ T : Subgroup B)) :=
    hD.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  exact (Subgroup.eq_bot_iff_card _).mpr
    (hI.card_eq_or_dvd.resolve_right hodd.not_two_dvd_nat)

theorem odd_subgroupOf (D C : Subgroup B) (hD : Odd (Nat.card D)) :
    Odd (Nat.card (D.subgroupOf C)) := by
  have he : Nat.card (D.subgroupOf C) = Nat.card (D ⊓ C : Subgroup B) := by
    rw [← Subgroup.card_map_of_injective (K := D.subgroupOf C)
      (f := C.subtype) Subtype.coe_injective, Subgroup.subgroupOf_map_subtype]
  rw [he]
  exact hD.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem normalized_odd_subgroup_eq_bot (M D : Subgroup B) [M.Normal]
    (hM : CFSG.IsQuasisimple M)
    (heven : Even (Nat.card (M ⧸ Subgroup.center M)))
    (hZ : IsPGroup 2 (Subgroup.center M))
    (hC : IsPGroup 2 (Subgroup.centralizer (M : Set B)))
    (hD : Odd (Nat.card D)) (hnorm : M ≤ Subgroup.normalizer (D : Set B)) : D = ⊥ := by
  let : Group.IsPerfect M := hM.1
  let I := D.subgroupOf M
  let : I.Normal := ⟨by
    intro d hd m
    change (m : B) * (d : B) * (m : B)⁻¹ ∈ D
    exact Subgroup.le_normalizer_iff.mp hnorm m m.property d hd⟩
  have hIodd : Odd (Nat.card I) := odd_subgroupOf D M hD
  have hIcentral : I ≤ Subgroup.center M := by
    have hq : CFSG.Open.IsQuasisimple M :=
      ⟨Group.IsPerfect.commutator_eq_top, hM.2.1⟩
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq I with h | h
    · exact h
    · have hoddM : Odd (Nat.card M) := by
        have hc : Nat.card I = Nat.card M :=
          Nat.card_congr ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv).toEquiv
        rwa [hc] at hIodd
      exact False.elim (hoddM.not_two_dvd_nat
        ((even_iff_two_dvd.mp heven).trans (Subgroup.card_quotient_dvd_card _)))
  have hItop : I = ⊥ := by
    have h := odd_inf_two_eq_bot I (Subgroup.center M) hIodd hZ
    rwa [inf_eq_left.mpr hIcentral] at h
  have hDM : D ⊓ M = ⊥ := by
    have h := congrArg (Subgroup.map M.subtype) hItop
    simpa only [I, Subgroup.subgroupOf_map_subtype, Subgroup.map_bot] using h
  have hcomm : ⁅M, D⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hDM]
    exact le_inf (Subgroup.le_normalizer_iff_commutator_le_right.mp hnorm)
      (Subgroup.commutator_le_left M D)
  have hDC : D ≤ Subgroup.centralizer (M : Set B) :=
    Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have h := odd_inf_two_eq_bot D (Subgroup.centralizer (M : Set B)) hD hC
  rwa [inf_eq_left.mpr hDC] at h

@[expose] def actualLiftMap (R J : Subgroup A) [R.Normal] (M : Subgroup (A ⧸ R))
    (himage : J.map (QuotientGroup.mk' R) = M) : J →* M :=
  ((QuotientGroup.mk' R).domRestrict J).codRestrict M (fun j => by
    rw [← himage]
    exact Subgroup.mem_map_of_mem _ j.property)

theorem actualLiftMap_surjective (R J : Subgroup A) [R.Normal]
    (M : Subgroup (A ⧸ R)) (himage : J.map (QuotientGroup.mk' R) = M) :
    Function.Surjective (actualLiftMap R J M himage) := by
  intro m
  have hm : m.val ∈ J.map (QuotientGroup.mk' R) := himage ▸ m.property
  obtain ⟨j, hj, heq⟩ := hm
  exact ⟨⟨j, hj⟩, Subtype.ext heq⟩

theorem actualLiftMap_ker (R J : Subgroup A) [R.Normal]
    (M : Subgroup (A ⧸ R)) (himage : J.map (QuotientGroup.mk' R) = M) :
    (actualLiftMap R J M himage).ker = R.subgroupOf J := by
  ext j
  change actualLiftMap R J M himage j = 1 ↔ (j : A) ∈ R
  rw [show actualLiftMap R J M himage j = 1 ↔ (QuotientGroup.mk' R) j.val = 1 from
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩]
  exact QuotientGroup.eq_one_iff j.val

theorem actual_centralizing_lift_quasisimple (R J : Subgroup A) [R.Normal]
    [Group.IsPerfect J] (M : Subgroup (A ⧸ R))
    (himage : J.map (QuotientGroup.mk' R) = M)
    (hcomm : ∀ j ∈ J, ∀ r ∈ R, Commute j r)
    (hM : CFSG.IsQuasisimple M) (heven : Even (Nat.card (M ⧸ Subgroup.center M))) :
    CFSG.IsQuasisimple J ∧ Even (Nat.card (J ⧸ Subgroup.center J)) := by
  apply perfect_central_extension_quasisimple (actualLiftMap R J M himage)
    (actualLiftMap_surjective R J M himage) _ hM heven
  rw [actualLiftMap_ker]
  intro r hr
  apply Subgroup.mem_center_iff.mpr
  intro j
  exact Subtype.ext (hcomm j j.property r.val hr).eq

theorem original_lift_preimage_eq_join (R J : Subgroup A) [R.Normal]
    (M : Subgroup (A ⧸ R)) (himage : J.map (QuotientGroup.mk' R) = M) :
    M.comap (QuotientGroup.mk' R) = J ⊔ R := by
  rw [← himage, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem original_two_subgroup_le_lift (R J Q : Subgroup A) [J.Normal]
    (hR : Odd (Nat.card R)) (hQ : IsPGroup 2 Q) (hQle : Q ≤ J ⊔ R) : Q ≤ J := by
  let q := QuotientGroup.mk' J
  have hQimage : Q.map q ≤ R.map q := by
    apply Subgroup.map_le_iff_le_comap.mpr
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
    exact hQle
  have hodd : Odd (Nat.card (Q.map q)) :=
    (hR.of_dvd_nat (R.card_map_dvd q)).of_dvd_nat (Subgroup.card_dvd_of_le hQimage)
  have hker : q.ker = J := QuotientGroup.ker_mk' J
  exact hker ▸ PrimewisePerfectLift.two_subgroup_le_kernel_of_odd_image Q hQ q hodd

theorem original_quaternion_le_actual_lift
    [Finite A] [IsSimpleGroup A]
    (hnonab : ∃ a b : A, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 A) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (himage : J.map (centralizerOddCoreMap n S e) =
      CFSG.layer (centralizerOddCoreQuotient n S e)) :
    centralizerQuaternion n hn S e ≤ J := by
  have hpre : (CFSG.layer (centralizerOddCoreQuotient n S e)).comap
      (centralizerOddCoreMap n S e) = J ⊔ centralizerOddCore n S e :=
    original_lift_preimage_eq_join (centralizerOddCore n S e) J _ himage
  have hQle : centralizerQuaternion n hn S e ≤ J ⊔ centralizerOddCore n S e := by
    rw [← hpre]
    exact Subgroup.map_le_iff_le_comap.mp
      (OriginalSylowCentralizerCoverage.original_quaternion_image_le_layer
        hnonab n hn S e hfour)
  exact original_two_subgroup_le_lift (centralizerOddCore n S e) J
    (centralizerQuaternion n hn S e) (centralizerOddCore_card_odd n S e)
    ((centralizerSylow n hn S e).isPGroup'.of_injective
      (Subgroup.inclusion (centralizerQuaternion_le_sylow n hn S e))
      (Subgroup.inclusion_injective _)) hQle

theorem original_layer_even_central_quotient
    [Finite A] [IsSimpleGroup A]
    (hnonab : ∃ a b : A, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 A) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    Even (Nat.card ((CFSG.layer (centralizerOddCoreQuotient n S e)) ⧸
      Subgroup.center (CFSG.layer (centralizerOddCoreQuotient n S e)))) := by
  have data := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  let f := centralizerLiftedLayerMap n hn S e
  have hf : Function.Surjective f := data.restriction_surjective
  have hk : f.ker = Subgroup.center (centralizerLiftedLayer n hn S e) :=
    data.restriction_kernel.trans data.center.symm
  have he : Nat.card (centralizerLiftedLayer n hn S e ⧸
      Subgroup.center (centralizerLiftedLayer n hn S e)) =
        Nat.card (centralizerSimpleLayer n hn S e) :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).toEquiv
  rw [data.layer]
  change Even (Nat.card (centralizerLiftedLayer n hn S e ⧸
    Subgroup.center (centralizerLiftedLayer n hn S e)))
  rw [he]
  exact centralizerSimpleLayer_even hnonab n hn S e hfour

theorem original_layer_center_isTwoGroup
    [Finite A] [IsSimpleGroup A]
    (hnonab : ∃ a b : A, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 A) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    IsPGroup 2 (Subgroup.center (CFSG.layer (centralizerOddCoreQuotient n S e))) := by
  have data := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  rw [data.layer, data.center]
  have hz : IsPGroup 2 (Subgroup.zpowers
      (centralizerOddCoreMap n S e (centralInvolution n S e))) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers]
    exact (OriginalScalarSylowCoverage.original_involution_image_order n S e _
      (centralizerKernelInvolution_original_order n hn S e)).trans (pow_one 2).symm
  exact hz.comap_subtype

theorem ambient_normal_intersection_normalized (H0 N : Subgroup A)
    (O : Subgroup H0) [O.Normal] (J : Subgroup N)
    (hJ0 : J.map N.subtype ≤ H0) :
    J ≤ Subgroup.normalizer ((O.map H0.subtype).subgroupOf N : Set N) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro j hj d hd
  have hj0 : (j : A) ∈ H0 := hJ0 (Subgroup.mem_map_of_mem N.subtype hj)
  obtain ⟨o, ho, heq⟩ := hd
  change ((j : A) * (d : A) * (j : A)⁻¹) ∈ O.map H0.subtype
  refine ⟨(⟨j, hj0⟩ : H0) * o * (⟨j, hj0⟩ : H0)⁻¹,
    (inferInstance : O.Normal).conj_mem o ho _, ?_⟩
  change (j : A) * (o : A) * (j : A)⁻¹ = (j : A) * (d : A) * (j : A)⁻¹
  change (o : A) = (d : A) at heq
  rw [heq]

theorem ambient_odd_core_intersection_le_kernel [Finite A] (H0 N : Subgroup A)
    (R : Subgroup N) [R.Normal] (M : Subgroup (N ⧸ R)) [M.Normal]
    (hM : CFSG.IsQuasisimple M)
    (heven : Even (Nat.card (M ⧸ Subgroup.center M)))
    (hZ : IsPGroup 2 (Subgroup.center M))
    (hC : IsPGroup 2 (Subgroup.centralizer (M : Set (N ⧸ R))))
    (J : Subgroup N) (himage : J.map (QuotientGroup.mk' R) = M)
    (hJ0 : J.map N.subtype ≤ H0) :
    ((CFSG.oddCore H0).map H0.subtype) ⊓ N ≤ R.map N.subtype := by
  let O := (CFSG.oddCore H0).map H0.subtype
  let D := O.subgroupOf N
  let q := QuotientGroup.mk' R
  have hDodd : Odd (Nat.card D) := odd_subgroupOf O N
    ((CFSG.ComponentClassification.OddCore.odd_card H0).of_dvd_nat
      ((CFSG.oddCore H0).card_map_dvd H0.subtype))
  have hJD : J ≤ Subgroup.normalizer (D : Set N) :=
    ambient_normal_intersection_normalized H0 N (CFSG.oddCore H0) J hJ0
  have hMnorm : M ≤ Subgroup.normalizer (D.map q : Set (N ⧸ R)) := by
    rw [← himage]
    exact (Subgroup.map_mono hJD).trans (Subgroup.le_normalizer_map q)
  have hDbot : D.map q = ⊥ := normalized_odd_subgroup_eq_bot M (D.map q) hM heven hZ hC
    (hDodd.of_dvd_nat (D.card_map_dvd q)) hMnorm
  have hDR : D ≤ R := by
    have hker : q.ker = R := QuotientGroup.ker_mk' R
    exact hker ▸ (D.map_eq_bot_iff.mp hDbot)
  intro d hd
  exact ⟨⟨d, hd.2⟩, hDR hd.1, rfl⟩

theorem quasisimple_of_equiv (e : A ≃* B) (hB : CFSG.IsQuasisimple B) :
    CFSG.IsQuasisimple A :=
  hB.of_mulEquiv e

theorem even_central_quotient_of_equiv (e : A ≃* B) [Group.IsPerfect B]
    (heven : Even (Nat.card (B ⧸ Subgroup.center B))) :
    Even (Nat.card (A ⧸ Subgroup.center A)) := by
  let : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hk : e.toMonoidHom.ker ≤ Subgroup.center A := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    exact bot_le
  exact (Nat.card_congr
    (perfectCentralQuotientEquiv e.toMonoidHom e.surjective hk).toEquiv).symm ▸ heven

theorem centralizing_lift_le_covering_product [Finite A]
    (R J X : Subgroup A) [R.Normal] [J.Normal]
    (hJ : CFSG.IsQuasisimple J)
    (heven : Even (Nat.card (J ⧸ Subgroup.center J)))
    (hodd : Odd (Nat.card R)) (hcomm : ∀ j ∈ J, ∀ r ∈ R, Commute j r)
    (hcover : R ⊔ X = R ⊔ J) : J ≤ X := by
  let Y := R ⊔ J
  let RJ := R.subgroupOf Y
  let JJ := J.subgroupOf Y
  let XX := X.subgroupOf Y
  have hRle : R ≤ Y := le_sup_left
  have hJle : J ≤ Y := le_sup_right
  have hXle : X ≤ Y := (le_sup_right : X ≤ R ⊔ X).trans_eq hcover
  let eJ := Subgroup.subgroupOfEquivOfLe hJle
  let : Group.IsPerfect J := hJ.1
  have hJq : CFSG.IsQuasisimple JJ := quasisimple_of_equiv eJ hJ
  have hJe : Even (Nat.card (JJ ⧸ Subgroup.center JJ)) :=
    even_central_quotient_of_equiv eJ heven
  have hRJodd : Odd (Nat.card RJ) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv).symm ▸ hodd
  have hprod : JJ ⊔ RJ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hJle hRle]
    change (J ⊔ R).subgroupOf Y = ⊤
    rw [sup_comm, show R ⊔ J = Y from rfl, Subgroup.subgroupOf_self]
  have hXR : XX ⊔ RJ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hXle hRle]
    change (X ⊔ R).subgroupOf Y = ⊤
    rw [sup_comm, hcover, show R ⊔ J = Y from rfl, Subgroup.subgroupOf_self]
  have hJRcomm : ∀ j ∈ JJ, ∀ r ∈ RJ, Commute j r := by
    intro j hj r hr
    exact show j * r = r * j from Subtype.ext (hcomm j hj r hr).eq
  have hcontain := odd_kernel_covering_subgroup_contains_centralizing_quasisimple_lift
    RJ JJ XX hJq hJe hRJodd hprod hJRcomm hXR
  intro j hj
  exact hcontain (show (⟨j, hJle hj⟩ : Y) ∈ JJ from hj)

theorem odd_kernel_centralizer_map
    (f : A →* B) (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    (T : Subgroup A) (hT : IsPGroup 2 T) :
    (Subgroup.centralizer (T : Set A)).map f =
      Subgroup.centralizer (T.map f : Set B) := by
  let sourceAction := MulAut.conj.comp T.subtype
  let targetAction := MulAut.conj.comp (f.comp T.subtype)
  let : MulDistribMulAction T A :=
    CFSG.RankThreeCoreUniqueness.Helpers.multiplicativeActionOfMulAutHom sourceAction
  let : MulDistribMulAction T B :=
    CFSG.RankThreeCoreUniqueness.Helpers.multiplicativeActionOfMulAutHom targetAction
  let : MulAction T A :=
    (CFSG.RankThreeCoreUniqueness.Helpers.multiplicativeActionOfMulAutHom
      sourceAction).toMulAction
  let : MulAction T B :=
    (CFSG.RankThreeCoreUniqueness.Helpers.multiplicativeActionOfMulAutHom
      targetAction).toMulAction
  have heq : ∀ t : T, ∀ a : A, f (t • a) = t • f a := by
    intro t a
    change f ((t : A) * a * (t : A)⁻¹) = f t * f a * (f t)⁻¹
    simp only [map_mul, map_inv]
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨t, ht, rfl⟩
    simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_iff.mp ha t ht)
  · intro b hb
    have hfix : ∀ t : T, t • b = b := by
      intro t
      change f t * b * (f t)⁻¹ = b
      rw [Subgroup.mem_centralizer_iff.mp hb (f t)
        (Subgroup.mem_map_of_mem f t.property), mul_inv_cancel_right]
    obtain ⟨a, hab, hfixa⟩ := CFSG.SignalizerFunctor.Helpers.fixed_point_lifts
      2 Nat.prime_two hT f hf heq hker.coprime_two_left b hfix
    refine ⟨a, ?_, hab⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro t ht
    have h := hfixa (⟨t, ht⟩ : T)
    change t * a * t⁻¹ = a at h
    exact mul_inv_eq_iff_eq_mul.mp h

theorem covering_involution_centralizer_factorization
    (O B : Subgroup A) [O.Normal] (hodd : Odd (Nat.card O))
    (x : A) (hx2 : orderOf x = 2) (hxB : x ∈ B)
    (hcover : O ⊔ B = ⊤)
    (hxcentral : (QuotientGroup.mk' O) x ∈ Subgroup.center (A ⧸ O)) :
    O ⊔ (B ⊓ Subgroup.centralizer {x}) = ⊤ := by
  let f := (QuotientGroup.mk' O).comp B.subtype
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O a
    have hy : y ∈ O ⊔ B := hcover ▸ Subgroup.mem_top y
    obtain ⟨o, ho, b, hb, hmul⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    refine ⟨⟨b, hb⟩, ?_⟩
    change (QuotientGroup.mk' O) b = (QuotientGroup.mk' O) y
    have hoq : (QuotientGroup.mk' O) o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    rw [← hmul, map_mul, hoq, one_mul]
  have hk : Odd (Nat.card f.ker) := by
    have he : f.ker = O.subgroupOf B := by
      ext b
      change (QuotientGroup.mk' O) (b : A) = 1 ↔ (b : A) ∈ O
      exact QuotientGroup.eq_one_iff (b : A)
    rw [he]
    have hcard : Nat.card (O.subgroupOf B) = Nat.card (O ⊓ B : Subgroup A) := by
      rw [← Subgroup.card_map_of_injective (K := O.subgroupOf B)
        (f := B.subtype) Subtype.coe_injective, Subgroup.subgroupOf_map_subtype]
    rw [hcard]
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  let xb : B := ⟨x, hxB⟩
  let T := Subgroup.zpowers xb
  have hT : IsPGroup 2 T := IsPGroup.of_card (by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe xb]
    exact hx2.trans (pow_one 2).symm)
  have hTc : T.map f ≤ Subgroup.center (A ⧸ O) := by
    dsimp only [T]
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr hxcentral
  have himage : (Subgroup.centralizer (T : Set B)).map f = ⊤ := by
    rw [odd_kernel_centralizer_map f hf hk T hT]
    apply top_le_iff.mp
    intro y _ t ht
    exact (Subgroup.mem_center_iff.mp (hTc ht) y).symm
  apply top_le_iff.mp
  intro y _
  have hymap : (QuotientGroup.mk' O) y ∈
      (Subgroup.centralizer (T : Set B)).map f := himage ▸ Subgroup.mem_top _
  obtain ⟨b, hb, heq⟩ := hymap
  have hbx : b.val ∈ Subgroup.centralizer {x} := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hb xb (Subgroup.mem_zpowers xb)).symm
  have hr : y * b.val⁻¹ ∈ O := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' O) (y * b.val⁻¹) = 1
    rw [map_mul, map_inv, show (QuotientGroup.mk' O) b.val =
      (QuotientGroup.mk' O) y from heq, mul_inv_cancel]
  have hyprod : y = (y * b.val⁻¹) * b.val := by simp [mul_assoc]
  rw [hyprod]
  exact Subgroup.mul_mem_sup hr ⟨b.property, hbx⟩


@[expose] def ambientCentralizerEquiv (H0 : Subgroup A) (x : A) (hx : x ∈ H0) :
    (Subgroup.centralizer {x}).subgroupOf H0 ≃*
      Subgroup.centralizer ({(⟨x, hx⟩ : H0)} : Set H0) where
  toFun c := ⟨c.val, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.property))⟩
  invFun c := ⟨c.val, Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp c.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem quotient_involution_central_of_factorization
    (O : Subgroup A) [O.Normal] (x : A)
    (hfactor : O ⊔ Subgroup.centralizer {x} = ⊤) :
    (QuotientGroup.mk' O) x ∈ Subgroup.center (A ⧸ O) := by
  let q := QuotientGroup.mk' O
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O y
  have hg : g ∈ O ⊔ Subgroup.centralizer {x} := hfactor ▸ Subgroup.mem_top g
  obtain ⟨o, ho, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  have hoq : q o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  change q (o * c) * q x = q x * q (o * c)
  rw [map_mul, hoq, one_mul, ← map_mul, ← map_mul,
    Subgroup.mem_centralizer_singleton_iff.mp hc]

theorem original_Sylow_normalizer_involution_factorization [Finite A]
    (H0 : Subgroup A) (x : A) (hx : x ∈ H0) (hx2 : orderOf x = 2)
    (hfactor : CFSG.oddCore H0 ⊔ (Subgroup.centralizer {x}).subgroupOf H0 = ⊤)
    (ell : ℕ) (hell : ell.Prime) (W : Sylow ell (CFSG.oddCore H0))
    (hxW : (⟨x, hx⟩ : H0) ∈ Subgroup.normalizer
      (((W : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype) : Set H0)) :
    CFSG.oddCore H0 ⊔
      (Subgroup.normalizer (((W : Subgroup (CFSG.oddCore H0)).map
        (CFSG.oddCore H0).subtype) : Set H0) ⊓
        (Subgroup.centralizer {x}).subgroupOf H0) = ⊤ := by
  let : Fact ell.Prime := ⟨hell⟩
  let B := Subgroup.normalizer (((W : Subgroup (CFSG.oddCore H0)).map
    (CFSG.oddCore H0).subtype) : Set H0)
  have hcover : CFSG.oddCore H0 ⊔ B = ⊤ := sup_comm B _ ▸ W.normalizer_sup_eq_top
  have hc : (Subgroup.centralizer {x}).subgroupOf H0 =
      Subgroup.centralizer ({(⟨x, hx⟩ : H0)} : Set H0) := by
    ext c
    change (c : A) ∈ Subgroup.centralizer {x} ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hfactor' : CFSG.oddCore H0 ⊔
      Subgroup.centralizer ({(⟨x, hx⟩ : H0)} : Set H0) = ⊤ := hc ▸ hfactor
  rw [hc]
  exact covering_involution_centralizer_factorization (CFSG.oddCore H0) B
    (CFSG.ComponentClassification.OddCore.odd_card H0) ⟨x, hx⟩
    ((Subgroup.orderOf_coe _).symm.trans hx2) hxW hcover
    (quotient_involution_central_of_factorization (CFSG.oddCore H0) ⟨x, hx⟩ hfactor')

theorem original_centralizer_intersection_factorization
    (H0 : Subgroup A) (O K : Subgroup H0) [O.Normal] (x : A)
    (hfactor : O ⊔ K = ⊤)
    (hK : K ≤ (Subgroup.centralizer {x}).subgroupOf H0) :
    (Subgroup.centralizer {x}).subgroupOf H0 =
      (O ⊓ (Subgroup.centralizer {x}).subgroupOf H0) ⊔ K := by
  apply le_antisymm
  · intro c hc
    have hcprod : c ∈ O ⊔ K := hfactor ▸ Subgroup.mem_top c
    obtain ⟨o, ho, k, hk, hprod⟩ := Subgroup.mem_sup_of_normal_left.mp hcprod
    have hoc : o ∈ (Subgroup.centralizer {x}).subgroupOf H0 := by
      have hoeq : o = c * k⁻¹ := by
        rw [← hprod]
        simp [mul_assoc]
      rw [hoeq]
      exact ((Subgroup.centralizer {x}).subgroupOf H0).mul_mem hc
        (((Subgroup.centralizer {x}).subgroupOf H0).inv_mem (hK hk))
    rw [← hprod]
    exact Subgroup.mul_mem_sup ⟨ho, hoc⟩ hk
  · exact sup_le inf_le_right hK

theorem actual_perfect_lift_normalizes_local_Sylow [Finite A]
    (H0 : Subgroup A) (x : A) (hx : x ∈ H0) (hx2 : orderOf x = 2)
    (R J : Subgroup (Subgroup.centralizer {x})) [R.Normal] [J.Normal]
    (hJ : CFSG.IsQuasisimple J)
    (heven : Even (Nat.card (J ⧸ Subgroup.center J)))
    (hR : Odd (Nat.card R))
    (hcomm : ∀ j ∈ J, ∀ r ∈ R, Commute j r)
    (hJ0 : J.map (Subgroup.centralizer {x}).subtype ≤ H0)
    (hD : ((CFSG.oddCore H0).map H0.subtype) ⊓ Subgroup.centralizer {x} ≤
      R.map (Subgroup.centralizer {x}).subtype)
    (hfactor : CFSG.oddCore H0 ⊔ (Subgroup.centralizer {x}).subgroupOf H0 = ⊤)
    (ell : ℕ) (hell : ell.Prime) (W : Sylow ell (CFSG.oddCore H0))
    (hxW : (⟨x, hx⟩ : H0) ∈ Subgroup.normalizer
      (((W : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype) : Set H0)) :
    J.map (Subgroup.centralizer {x}).subtype ≤
      (Subgroup.normalizer (((W : Subgroup (CFSG.oddCore H0)).map
        (CFSG.oddCore H0).subtype) : Set H0)).map H0.subtype := by
  let N := Subgroup.centralizer {x}
  let B := Subgroup.normalizer (((W : Subgroup (CFSG.oddCore H0)).map
    (CFSG.oddCore H0).subtype) : Set H0)
  let C := N.subgroupOf H0
  let K := B ⊓ C
  let D := ((CFSG.oddCore H0).map H0.subtype).subgroupOf N
  let K0 := K.map H0.subtype
  let KN := K0.subgroupOf N
  have hKNle : K0 ≤ N := by
    rintro a ⟨k, hk, rfl⟩
    exact hk.2
  have hDK : D ≤ R := by
    intro d hd
    have h := hD (show (d : A) ∈ ((CFSG.oddCore H0).map H0.subtype) ⊓ N from
      ⟨hd, d.property⟩)
    obtain ⟨r, hr, heq⟩ := h
    exact (Subtype.ext heq : r = d) ▸ hr
  have hfactorK : CFSG.oddCore H0 ⊔ K = ⊤ :=
    original_Sylow_normalizer_involution_factorization H0 x hx hx2 hfactor ell hell W hxW
  have hJcover : J ≤ R ⊔ KN := by
    intro j hj
    have hj0 : (j : A) ∈ H0 := hJ0 (Subgroup.mem_map_of_mem N.subtype hj)
    have hjC : (⟨j, hj0⟩ : H0) ∈ C := j.property
    have hjprod : (⟨j, hj0⟩ : H0) ∈ CFSG.oddCore H0 ⊔ K :=
      hfactorK ▸ Subgroup.mem_top _
    obtain ⟨d, hd, k, hk, hprod⟩ := Subgroup.mem_sup_of_normal_left.mp hjprod
    have hdc : d ∈ C := by
      have he : d = (⟨j, hj0⟩ : H0) * k⁻¹ := by
        rw [← hprod]
        simp [mul_assoc]
      rw [he]
      exact C.mul_mem hjC (C.inv_mem hk.2)
    have hdN : (d : A) ∈ N := hdc
    have hdR : (⟨d, hdN⟩ : N) ∈ R :=
      hDK (Subgroup.mem_map_of_mem H0.subtype hd)
    have hkN : (k : A) ∈ N := hk.2
    have hkKN : (⟨k, hkN⟩ : N) ∈ KN := ⟨k, hk, rfl⟩
    have hprodA : (d : A) * (k : A) = (j : A) := congrArg H0.subtype hprod
    have hprodN : (⟨d, hdN⟩ : N) * (⟨k, hkN⟩ : N) = j := Subtype.ext hprodA
    exact hprodN ▸ Subgroup.mul_mem_sup hdR hkKN
  let X := KN ⊓ (R ⊔ J)
  have hcover : R ⊔ X = R ⊔ J := by
    apply le_antisymm
    · exact sup_le le_sup_left inf_le_right
    · apply sup_le le_sup_left
      intro j hj
      obtain ⟨r, hr, k, hk, hprod⟩ := Subgroup.mem_sup_of_normal_left.mp (hJcover hj)
      have hkY : k ∈ R ⊔ J := by
        have hkexpr : k = r⁻¹ * j := by
          rw [← hprod]
          simp
        rw [hkexpr]
        exact (R ⊔ J).mul_mem ((R ⊔ J).inv_mem
          ((le_sup_left : R ≤ R ⊔ J) hr)) ((le_sup_right : J ≤ R ⊔ J) hj)
      rw [← hprod]
      exact Subgroup.mul_mem_sup hr ⟨hk, hkY⟩
  have hJX := centralizing_lift_le_covering_product R J X hJ heven hR hcomm hcover
  rintro a ⟨j, hj, rfl⟩
  obtain ⟨k, hk, heq⟩ := (hJX hj).1
  exact ⟨k, hk.1, heq⟩

theorem original_quaternion_literal_generators
    (n : ℕ) (S : Sylow 2 A) (e : S ≃* Wreath (2 ^ n)) :
    modelY S e = Subgroup.closure
      {wreathModelHom S e (Original.s (2 ^ n)) *
        (wreathModelHom S e (Original.t (2 ^ n)))⁻¹,
       wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2) *
        wreathModelHom S e (Original.z (2 ^ n))} := by
  rw [modelY, Original.Y, MonoidHom.map_closure, Set.image_pair]
  simp only [Original.r, Original.d, Original.x2, map_mul, map_inv, map_pow]

structure LocalOddCorePerfectNormalizerData
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 A) (e : S ≃* Wreath (2 ^ n))
    (J : Subgroup (involutionCentralizer n S e)) (H0 : Subgroup A)
    (ell : ℕ) (W : Sylow ell (CFSG.oddCore H0)) : Prop where
  odd_core_intersection : ((CFSG.oddCore H0).map H0.subtype) ⊓ involutionCentralizer n S e ≤
    (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype
  perfect_lift_normalizes : J.map (involutionCentralizer n S e).subtype ≤
    (Subgroup.normalizer (((W : Subgroup (CFSG.oddCore H0)).map
      (CFSG.oddCore H0).subtype) : Set H0)).map H0.subtype
  quaternion_in_lift : modelY S e ≤ J.map (involutionCentralizer n S e).subtype
  quaternion_in_centralizer_lift : centralizerQuaternion n hn S e ≤ J
  involution_in_lift : centralInvolution n S e ∈ J
  quaternion_literal : modelY S e = Subgroup.closure
    {wreathModelHom S e (Original.s (2 ^ n)) *
      (wreathModelHom S e (Original.t (2 ^ n)))⁻¹,
     wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2) *
      wreathModelHom S e (Original.z (2 ^ n))}
  cyclic_actor_normalizes : Subgroup.zpowers (wreathModelHom S e (Original.r (2 ^ n))) ≤
    Subgroup.normalizer ((((W : Subgroup (CFSG.oddCore H0)).map
      (CFSG.oddCore H0).subtype).map H0.subtype) : Set A)
  cyclic_actor_order :
    Nat.card (Subgroup.zpowers (wreathModelHom S e (Original.r (2 ^ n)))) = 2 ^ n

theorem local_odd_core_factorization_forces_actual_perfect_lift_to_normalize_Sylows
    [Finite A] [IsSimpleGroup A] (hnonab : ∃ a b : A, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 A) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4)))
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal] [Group.IsPerfect J]
    (himage : J.map (centralizerOddCoreMap n S e) =
      CFSG.layer (centralizerOddCoreQuotient n S e))
    (hcomm : ∀ j ∈ J, ∀ r ∈ centralizerOddCore n S e, Commute j r)
    (H0 : Subgroup A) (hJ0 : J.map (involutionCentralizer n S e).subtype ≤ H0)
    (hx0 : (centralInvolution n S e : A) ∈ H0)
    (hfactor : CFSG.oddCore H0 ⊔ (involutionCentralizer n S e).subgroupOf H0 = ⊤)
    (ell : ℕ) (hell : ell.Prime) (_hdiv : ell ∣ Nat.card (CFSG.oddCore H0))
    (W : Sylow ell (CFSG.oddCore H0))
    (hxW : (⟨(centralInvolution n S e : A), hx0⟩ : H0) ∈ Subgroup.normalizer
      (((W : Subgroup (CFSG.oddCore H0)).map (CFSG.oddCore H0).subtype) : Set H0)) :
    LocalOddCorePerfectNormalizerData n hn S e J H0 ell W := by
  have hfour' := OriginalScalarSylowCoverage.original_nonfourpoint_fullCenter n hn S e hfour
  let M := CFSG.layer (centralizerOddCoreQuotient n S e)
  have hcomponent := wreathed_centralizer_unique_component_data hnonab n hn S e hfour'
  let : M.Normal := by
    dsimp only [M]
    rw [hcomponent.layer]
    exact hcomponent.normal
  let : (centralizerOddCore n S e).Normal := centralizerOddCore_normal n S e
  have hdata := OriginalSylowCentralizerCoverage.original_layer_data hnonab n hn S e hfour'
  have hMeven := original_layer_even_central_quotient hnonab n hn S e hfour'
  have hMcenter := original_layer_center_isTwoGroup hnonab n hn S e hfour'
  have hMcent : IsPGroup 2 (Subgroup.centralizer
      (M : Set (centralizerOddCoreQuotient n S e))) := by
    rw [hdata.2]
    exact center_isTwoGroup_of_oddCore_eq_bot _ (centralizerOddCoreQuotient_oddCore_eq_bot n S e)
  have hD := @ambient_odd_core_intersection_le_kernel A _ _ H0
    (involutionCentralizer n S e) (centralizerOddCore n S e)
    (centralizerOddCore_normal n S e) M (inferInstanceAs M.Normal)
    hdata.1 hMeven hMcenter hMcent J himage hJ0
  have hJdata := actual_centralizing_lift_quasisimple (centralizerOddCore n S e) J M himage
    hcomm hdata.1 hMeven
  have hnorm := @actual_perfect_lift_normalizes_local_Sylow A _ _ H0
    (centralInvolution n S e : A) hx0 (by
      exact (Subgroup.orderOf_coe (centralInvolution n S e)).trans
        (centralizerKernelInvolution_original_order n hn S e))
    (centralizerOddCore n S e) J (centralizerOddCore_normal n S e)
    (inferInstanceAs J.Normal) hJdata.1 hJdata.2 (centralizerOddCore_card_odd n S e)
    hcomm hJ0 hD hfactor ell hell W hxW
  have hQ := original_quaternion_le_actual_lift hnonab n hn S e hfour' J himage
  have hQambient : modelY S e ≤ J.map (involutionCentralizer n S e).subtype := by
    rw [← centralizerQuaternion_map n hn S e]
    exact Subgroup.map_mono hQ
  have hactor : Subgroup.zpowers (wreathModelHom S e (Original.r (2 ^ n))) ≤ modelY S e := by
    apply Subgroup.zpowers_le.mpr
    apply Subgroup.mem_map_of_mem (wreathModelHom S e)
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hNormAmbient : J.map (involutionCentralizer n S e).subtype ≤
      Subgroup.normalizer ((((W : Subgroup (CFSG.oddCore H0)).map
        (CFSG.oddCore H0).subtype).map H0.subtype) : Set A) :=
    hnorm.trans (Subgroup.le_normalizer_map H0.subtype)
  refine ⟨hD, hnorm, hQambient, hQ,
    hQ (centralizerKernelInvolution_original_mem_quaternion n hn S e),
    original_quaternion_literal_generators n S e,
    hactor.trans (hQambient.trans hNormAmbient), ?_⟩
  rw [Nat.card_zpowers, orderOf_injective _ (wreathModelHom_injective S e), Original.orderOf_r]


end CFSG.Wreathed.LocalOddCorePerfectNormalizer
