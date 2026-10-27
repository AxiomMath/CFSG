module

public import CFSG.CharacterTheory.Wreathed.CentralizerKernelOddCore

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u v

theorem map_inf_eq_of_ker_le_right {E : Type u} [Group E] {F : Type v} [Group F]
    (f : E →* F) (A K : Subgroup E) (hK : f.ker ≤ K) :
    (A ⊓ K).map f = A.map f ⊓ K.map f := by
  apply le_antisymm (Subgroup.map_inf_le _ _ _)
  rintro b ⟨hbA, hbK⟩
  obtain ⟨a, ha, rfl⟩ := hbA
  have haK : a ∈ K := by
    change a ∈ (K.map f).comap f at hbK
    rwa [Subgroup.comap_map_eq_self hK] at hbK
  exact Subgroup.mem_map.mpr ⟨a, ⟨ha, haK⟩, rfl⟩

theorem sup_index_two_of_index_and_intersection_card {E : Type u} [Group E]
    (A T : Subgroup E) [T.Normal] (m : ℕ) (hm : m ≠ 0)
    (hindex : T.index = m) (hA : Nat.card A = m) (hAT : Nat.card (T ⊓ A : Subgroup E) = 2) :
    (A ⊔ T).index = 2 := by
  have hrel := Subgroup.relIndex_mul_card T A
  rw [hAT, hA] at hrel
  have hproduct := Subgroup.relIndex_mul_index (show T ≤ A ⊔ T from le_sup_right)
  rw [Subgroup.relIndex_sup_right, hindex] at hproduct
  have hnonzero : T.relIndex A ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrel
    exact hm hrel.symm
  exact mul_left_cancel₀ hnonzero (hproduct.trans hrel.symm)

theorem hom_to_two_group_eq_one_of_surjective {E : Type u} [Group E]
    {F : Type v} [Group F] (f : E →* F) (hf : Function.Surjective f)
    (hE : ∀ M : Subgroup E, M.index ≠ 2)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) (g : F →* P) : g = 1 := by
  have hcomp : g.comp f = 1 := hom_to_two_group_eq_one_of_no_index_two hE hP _
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := hf x
  exact congrArg (fun h : E →* P => h y) hcomp

theorem quotient_image_comap {E : Type u} [Group E] (A T : Subgroup E) [A.Normal] :
    (T.map (QuotientGroup.mk' A)).comap (QuotientGroup.mk' A) = T ⊔ A := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem quotient_image_sup {E : Type u} [Group E] (A T : Subgroup E) [A.Normal] :
    (A ⊔ T).map (QuotientGroup.mk' A) = T.map (QuotientGroup.mk' A) := by
  rw [Subgroup.map_sup]
  have hA : A.map (QuotientGroup.mk' A) = ⊥ := by
    apply le_antisymm _ bot_le
    rintro x ⟨a, ha, rfl⟩
    exact (QuotientGroup.eq_one_iff (N := A) a).mpr ha
  rw [hA, bot_sup_eq]

theorem quotient_image_index {E : Type u} [Group E] (A T : Subgroup E) [A.Normal] :
    (T.map (QuotientGroup.mk' A)).index = (A ⊔ T).index := by
  rw [← quotient_image_sup A T]
  apply Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective A)
  rw [QuotientGroup.ker_mk']
  exact le_sup_left

@[expose] def quotient_image_equiv {E : Type u} [Group E]
    (A T : Subgroup E) [A.Normal] :
    T ⧸ A.subgroupOf T ≃* T.map (QuotientGroup.mk' A) := by
  have hk : ((QuotientGroup.mk' A).subgroupMap T).ker = A.subgroupOf T := by
    ext t
    change (QuotientGroup.mk' A).subgroupMap T t = 1 ↔ (t : E) ∈ A
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  exact QuotientGroup.liftEquiv (A.subgroupOf T)
    ((QuotientGroup.mk' A).subgroupMap_surjective T) hk.symm

theorem quotient_image_equiv_mk {E : Type u} [Group E]
    (A T : Subgroup E) [A.Normal] (t : T) :
    quotient_image_equiv A T ((QuotientGroup.mk' (A.subgroupOf T)) t) =
      (QuotientGroup.mk' A).subgroupMap T t := rfl

theorem central_subgroup_restrict_le_center {E : Type u} [Group E]
    (A T : Subgroup E) (hA : A ≤ Subgroup.center E) :
    A.subgroupOf T ≤ Subgroup.center T := by
  intro t ht
  rw [Subgroup.mem_center_iff]
  intro z
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hA ht) z.val

variable {G : Type u} [Group G]

theorem centralizerFullCenter_inf_transferKernel [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerFullCenter n hn S e ⊓ centralizerTransferKernel n hn S e =
      Subgroup.zpowers (centralInvolution n S e) := by
  let P := centralizerSylow n hn S e
  let f := centralizerCoordinates n hn S e
  have hZP : modelCenter P f ≤ (P : Subgroup (involutionCentralizer n S e)) :=
    centralizerFullCenter_le_sylow n hn S e
  have h := centralizerTransferKernel_inf_eq_quaternion hnonab n hn S e
  change centralizerTransferKernel n hn S e ⊓ (P : Subgroup (involutionCentralizer n S e)) =
    modelY P f at h
  have heq : modelCenter P f ⊓ centralizerTransferKernel n hn S e =
      modelCenter P f ⊓ modelY P f := by
    rw [← h, inf_comm (centralizerTransferKernel n hn S e), ← inf_assoc,
      inf_eq_left.mpr hZP]
  change modelCenter P f ⊓ centralizerTransferKernel n hn S e = _
  rw [heq, modelCenter_inf_modelY n hn P f, centralizerModelHom_x]

theorem centralizerFullCenterImage_inf_residualImage [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerFullCenterImage n hn S e ⊓ centralizerResidualImage n hn S e =
      Subgroup.zpowers (centralizerOddCoreMap n S e (centralInvolution n S e)) := by
  have hk : (centralizerOddCoreMap n S e).ker = centralizerOddCore n S e :=
    QuotientGroup.ker_mk' _
  change (centralizerFullCenter n hn S e).map (centralizerOddCoreMap n S e) ⊓
    (centralizerTransferKernel n hn S e).map (centralizerOddCoreMap n S e) = _
  rw [← map_inf_eq_of_ker_le_right _ _ _ (by
    rw [hk]
    exact centralizerOddCore_le_transferKernel n hn S e),
    centralizerFullCenter_inf_transferKernel hnonab n hn S e, MonoidHom.map_zpowers]

@[expose] def centralizerFullQuotient [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Type u :=
  centralizerOddCoreQuotient n S e ⧸ centralizerFullCenterImage n hn S e

instance centralizerFullQuotient_group [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Group (centralizerFullQuotient n hn S e) := inferInstanceAs
      (Group (centralizerOddCoreQuotient n S e ⧸ centralizerFullCenterImage n hn S e))

instance centralizerFullQuotient_finite [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Finite (centralizerFullQuotient n hn S e) := inferInstanceAs
      (Finite (centralizerOddCoreQuotient n S e ⧸ centralizerFullCenterImage n hn S e))

@[expose] def centralizerFullQuotientMap [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerOddCoreQuotient n S e →* centralizerFullQuotient n hn S e :=
  QuotientGroup.mk' (centralizerFullCenterImage n hn S e)

theorem centralizerFullQuotientMap_surjective [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Surjective (centralizerFullQuotientMap n hn S e) :=
  QuotientGroup.mk'_surjective _

@[expose] def centralizerDihedralImage [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup (centralizerFullQuotient n hn S e) :=
  (centralizerResidualImage n hn S e).map (centralizerFullQuotientMap n hn S e)

instance centralizerDihedralImage_normal [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerDihedralImage n hn S e).Normal :=
  Subgroup.Normal.map inferInstance _ (centralizerFullQuotientMap_surjective n hn S e)

@[expose] def centralizerDihedralImageMap [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerResidualImage n hn S e →* centralizerDihedralImage n hn S e :=
  (centralizerFullQuotientMap n hn S e).subgroupMap (centralizerResidualImage n hn S e)

theorem centralizerDihedralImageMap_surjective [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Surjective (centralizerDihedralImageMap n hn S e) :=
  (centralizerFullQuotientMap n hn S e).subgroupMap_surjective _

theorem centralizerResidualImage_hom_to_two_group_eq_one [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {P : Type v} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (f : centralizerResidualImage n hn S e →* P) : f = 1 :=
  hom_to_two_group_eq_one_of_surjective (centralizerResidualMap n hn S e)
    (centralizerResidualMap_surjective n hn S e)
    (centralizerTransferKernel_no_index_two hnonab n hn S e) hP f

theorem centralizerDihedralImage_hom_to_two_group_eq_one [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {P : Type v} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (f : centralizerDihedralImage n hn S e →* P) : f = 1 := by
  let q := (centralizerDihedralImageMap n hn S e).comp (centralizerResidualMap n hn S e)
  exact hom_to_two_group_eq_one_of_surjective q
    ((centralizerDihedralImageMap_surjective n hn S e).comp
      (centralizerResidualMap_surjective n hn S e))
    (centralizerTransferKernel_no_index_two hnonab n hn S e) hP f

theorem centralizerFullQuotient_oddCore_eq_bot [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    CFSG.oddCore (centralizerFullQuotient n hn S e) = ⊥ :=
  centralizerFullCenterQuotient_oddCore_eq_bot n hn S e

theorem centralizerFullCenterImage_inf_residualImage_card [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (centralizerFullCenterImage n hn S e ⊓ centralizerResidualImage n hn S e :
      Subgroup (centralizerOddCoreQuotient n S e)) = 2 := by
  rw [centralizerFullCenterImage_inf_residualImage hnonab n hn S e, Nat.card_zpowers]
  exact (Subgroup.orderOf_coe (centralizerResidualInvolution hnonab n hn S e)).trans
    (centralizerResidualInvolution_order hnonab n hn S e)

theorem centralizerFullCenterImage_sup_residualImage_index [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerFullCenterImage n hn S e ⊔ centralizerResidualImage n hn S e).index = 2 := by
  apply sup_index_two_of_index_and_intersection_card _ _ (2 ^ n)
    (pow_ne_zero _ (by decide)) (centralizerResidualImage_index hnonab n hn S e)
    (centralizerFullCenterImage_card n hn S e)
  rw [inf_comm]
  exact centralizerFullCenterImage_inf_residualImage_card hnonab n hn S e

theorem centralizerDihedralImage_index [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerDihedralImage n hn S e).index = 2 := by
  change ((centralizerResidualImage n hn S e).map
    (QuotientGroup.mk' (centralizerFullCenterImage n hn S e))).index = 2
  rw [quotient_image_index]
  exact centralizerFullCenterImage_sup_residualImage_index hnonab n hn S e

theorem centralizerDihedralImage_oddCore_eq_bot [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    CFSG.oddCore (centralizerDihedralImage n hn S e) = ⊥ := by
  let A := centralizerFullCenterImage n hn S e
  let T := centralizerResidualImage n hn S e
  have hc : A.subgroupOf T ≤ Subgroup.center T :=
    central_subgroup_restrict_le_center A T
      (centralizerFullCenterImage_le_center_and_factorization n hn S e).1
  have ht : IsPGroup 2 (A.subgroupOf T) :=
    (centralizerFullCenterImage_isTwoGroup n hn S e).comap_subtype
  have hcore : CFSG.oddCore (T ⧸ A.subgroupOf T) = ⊥ :=
    oddCore_quotient_eq_bot_of_central_two (A.subgroupOf T) hc ht
      (centralizerResidualImage_oddCore_eq_bot n hn S e)
  have h := CFSG.ComponentClassification.OddCore.equiv_invariant (quotient_image_equiv A T)
  change (CFSG.oddCore (T ⧸ A.subgroupOf T)).map
    (quotient_image_equiv A T).toMonoidHom =
      CFSG.oddCore (centralizerDihedralImage n hn S e) at h
  rw [hcore, Subgroup.map_bot] at h
  exact h.symm

@[expose] def centralizerFullQuotientSylow [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Sylow 2 (centralizerFullQuotient n hn S e) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (centralizerOddCoreSylow n hn S e).mapSurjective
    (centralizerFullQuotientMap_surjective n hn S e)

theorem centralizerFullQuotientSylow_image [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerFullQuotientSylow n hn S e : Subgroup (centralizerFullQuotient n hn S e)) =
      (centralizerOddCoreSylow n hn S e : Subgroup (centralizerOddCoreQuotient n S e)).map
        (centralizerFullQuotientMap n hn S e) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [centralizerFullQuotientSylow, Sylow.coe_mapSurjective]

@[expose] def centralizerFullQuotientSylowEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerFullQuotientSylow n hn S e ≃* DihedralGroup (2 ^ n) := by
  let P := centralizerOddCoreSylow n hn S e
  let f := centralizerOddCoreCoordinates n hn S e
  let A := centralizerFullCenterImage n hn S e
  have hA : A.subgroupOf (P : Subgroup (centralizerOddCoreQuotient n S e)) =
      modelSylowCenter P f := by
    dsimp only [A]
    rw [centralizerFullCenterImage_eq_modelCenter]
    rfl
  exact (quotient_image_equiv A (P : Subgroup (centralizerOddCoreQuotient n S e))).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hA).trans (modelSylowDihedralEquiv n hn P f))

theorem centralizerFullQuotientSylow_card [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (centralizerFullQuotientSylow n hn S e) = 2 * 2 ^ n := by
  rw [Nat.card_congr (centralizerFullQuotientSylowEquiv n hn S e).toEquiv,
    DihedralGroup.nat_card]

theorem modelCenter_subgroupOf_modelY_eq
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelCenter S e).subgroupOf (modelY S e) = modelYCentralInvolution n hn S e := by
  rw [modelYCentralInvolution_eq]
  ext y
  change y.val ∈ modelCenter S e ↔
    y.val ∈ Subgroup.zpowers (wreathModelHom S e (Original.x (2 ^ n)))
  rw [← modelCenter_inf_modelY n hn S e]
  exact ⟨fun hy => ⟨hy, y.property⟩, fun hy => hy.1⟩

@[expose] def centralizerDihedralSylow [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Sylow 2 (centralizerDihedralImage n hn S e) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (centralizerResidualSylow hnonab n hn S e).mapSurjective
    (centralizerDihedralImageMap_surjective n hn S e)

theorem centralizerDihedralImageMap_comp [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerDihedralImage n hn S e).subtype.comp (centralizerDihedralImageMap n hn S e) =
      (centralizerFullQuotientMap n hn S e).comp (centralizerResidualImage n hn S e).subtype := rfl

theorem centralizerDihedralSylow_image [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerDihedralSylow hnonab n hn S e : Subgroup (centralizerDihedralImage n hn S e)).map
      (centralizerDihedralImage n hn S e).subtype =
        ((centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e)).map
          (centralizerFullQuotientMap n hn S e) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [centralizerDihedralSylow, Sylow.coe_mapSurjective, Subgroup.map_map,
    centralizerDihedralImageMap_comp, ← Subgroup.map_map,
    centralizerResidualSylow_image hnonab n hn S e]

@[expose] def centralizerDihedralSylowEquiv [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerDihedralSylow hnonab n hn S e ≃* DihedralGroup (2 ^ n / 2) := by
  let P := centralizerOddCoreSylow n hn S e
  let f := centralizerOddCoreCoordinates n hn S e
  let A := centralizerFullCenterImage n hn S e
  let Q := modelY P f
  have hA : A.subgroupOf Q = modelYCentralInvolution n hn P f := by
    dsimp only [A]
    rw [centralizerFullCenterImage_eq_modelCenter]
    exact modelCenter_subgroupOf_modelY_eq n hn P f
  have hmap : (centralizerDihedralSylow hnonab n hn S e :
      Subgroup (centralizerDihedralImage n hn S e)).map
        (centralizerDihedralImage n hn S e).subtype =
          Q.map (centralizerFullQuotientMap n hn S e) := by
    rw [centralizerDihedralSylow_image hnonab n hn S e,
      centralizerQuaternionImage_eq_modelY]
  let E := ((centralizerDihedralSylow hnonab n hn S e :
    Subgroup (centralizerDihedralImage n hn S e)).equivMapOfInjective
      (centralizerDihedralImage n hn S e).subtype Subtype.coe_injective).trans
        (MulEquiv.subgroupCongr hmap)
  exact E.trans ((quotient_image_equiv A Q).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hA).trans (modelYDihedralEquiv n hn P f)))

theorem centralizerDihedralSylow_card [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (centralizerDihedralSylow hnonab n hn S e) = 2 ^ n := by
  rw [Nat.card_congr (centralizerDihedralSylowEquiv hnonab n hn S e).toEquiv,
    DihedralGroup.nat_card]
  exact wreath_modulus_twice_half n (by omega)

theorem centralizerDihedralSylow_isKleinFour [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ 2)) :
    IsKleinFour (centralizerDihedralSylow hnonab 2 (by decide) S e) := by
  refine ⟨centralizerDihedralSylow_card hnonab 2 (by decide) S e, ?_⟩
  rw [Monoid.exponent_eq_of_mulEquiv (centralizerDihedralSylowEquiv hnonab 2 (by decide) S e)]
  exact DihedralGroup.exponent (n := 2) |>.trans (by decide)

structure WreathedCentralizerFullQuotientData [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Prop where
  full_center : WreathedCentralizerFullCenterData n hn S e
  quaternion_residual : WreathedCentralizerQuaternionResidualData n hn S e
  kernel_odd_core : WreathedCentralizerKernelOddCoreData n hn S e
  center_residual_intersection :
    centralizerFullCenterImage n hn S e ⊓ centralizerResidualImage n hn S e =
      Subgroup.zpowers (centralizerOddCoreMap n S e (centralInvolution n S e))
  center_residual_product_index :
    (centralizerFullCenterImage n hn S e ⊔ centralizerResidualImage n hn S e).index = 2
  quotient_residual_normal : (centralizerDihedralImage n hn S e).Normal
  quotient_residual_index : (centralizerDihedralImage n hn S e).index = 2
  quotient_corefree : CFSG.oddCore (centralizerFullQuotient n hn S e) = ⊥
  quotient_residual_corefree : CFSG.oddCore (centralizerDihedralImage n hn S e) = ⊥
  kernel_two_group_homs : ∀ {P : Type v} [Group P] [Finite P], IsPGroup 2 P →
    ∀ f : centralizerTransferKernel n hn S e →* P, f = 1
  residual_two_group_homs : ∀ {P : Type v} [Group P] [Finite P], IsPGroup 2 P →
    ∀ f : centralizerResidualImage n hn S e →* P, f = 1
  quotient_residual_two_group_homs : ∀ {P : Type v} [Group P] [Finite P], IsPGroup 2 P →
    ∀ f : centralizerDihedralImage n hn S e →* P, f = 1
  quotient_dihedral_sylow : ∃ P : Sylow 2 (centralizerFullQuotient n hn S e),
    (P : Subgroup (centralizerFullQuotient n hn S e)) =
      (centralizerOddCoreSylow n hn S e : Subgroup (centralizerOddCoreQuotient n S e)).map
        (centralizerFullQuotientMap n hn S e) ∧
    Nonempty (P ≃* DihedralGroup (2 ^ n)) ∧ Nat.card P = 2 * 2 ^ n
  residual_dihedral_sylow : ∃ P : Sylow 2 (centralizerDihedralImage n hn S e),
    (P : Subgroup (centralizerDihedralImage n hn S e)).map
      (centralizerDihedralImage n hn S e).subtype =
        ((centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e)).map
          (centralizerFullQuotientMap n hn S e) ∧
    Nonempty (P ≃* DihedralGroup (2 ^ n / 2)) ∧ Nat.card P = 2 ^ n ∧
      (n = 2 → IsKleinFour P)

theorem wreathed_centralizer_full_center_dihedral_quotient [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    WreathedCentralizerFullQuotientData.{u, v} n hn S e := by
  refine ⟨wreathed_centralizer_full_center_odd_core n hn S e,
    wreathed_involution_centralizer_quaternion_two_residual hnonab n hn S e,
    wreathed_centralizer_kernel_odd_core_data hnonab n hn S e,
    centralizerFullCenterImage_inf_residualImage hnonab n hn S e,
    centralizerFullCenterImage_sup_residualImage_index hnonab n hn S e,
    inferInstance, centralizerDihedralImage_index hnonab n hn S e,
    centralizerFullQuotient_oddCore_eq_bot n hn S e,
    centralizerDihedralImage_oddCore_eq_bot n hn S e,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro P _ _ hP f
    exact centralizerTransferKernel_hom_to_two_group_eq_one hnonab n hn S e hP f
  · intro P _ _ hP f
    exact centralizerResidualImage_hom_to_two_group_eq_one hnonab n hn S e hP f
  · intro P _ _ hP f
    exact centralizerDihedralImage_hom_to_two_group_eq_one hnonab n hn S e hP f
  · exact ⟨centralizerFullQuotientSylow n hn S e, centralizerFullQuotientSylow_image n hn S e,
      ⟨centralizerFullQuotientSylowEquiv n hn S e⟩, centralizerFullQuotientSylow_card n hn S e⟩
  · refine ⟨centralizerDihedralSylow hnonab n hn S e,
      centralizerDihedralSylow_image hnonab n hn S e,
      ⟨centralizerDihedralSylowEquiv hnonab n hn S e⟩,
      centralizerDihedralSylow_card hnonab n hn S e, ?_⟩
    intro hn2
    subst n
    exact centralizerDihedralSylow_isKleinFour hnonab S e

end CFSG.Wreathed
