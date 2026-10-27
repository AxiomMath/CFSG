module

public import CFSG.CharacterTheory.Wreathed.CentralizerFusion
public import CFSG.CharacterTheory.Semidihedral.PrimeResidual
public import CFSG.Dihedral.DisconnectedInvolutionGraph.NormalSylowIntersection

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u v

variable {G : Type u} [Group G]

@[expose] def centralizerSylowY (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup (centralizerSylow n hn S e) :=
  (centralizerQuaternion n hn S e).subgroupOf (centralizerSylow n hn S e)

theorem centralizerSylowY_map (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerSylowY n hn S e).map (centralizerSylow n hn S e :
      Subgroup (involutionCentralizer n S e)).subtype = centralizerQuaternion n hn S e :=
  Subgroup.map_subgroupOf_eq_of_le (centralizerQuaternion_le_sylow n hn S e)

theorem centralizerSylowY_eq_original_map (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerSylowY n hn S e =
      (Original.Y (2 ^ n)).map (centralizerCoordinates n hn S e).symm.toMonoidHom := by
  apply Subgroup.map_subtype_inj.mp
  rw [centralizerSylowY_map, Subgroup.map_map]
  rfl

instance centralizerSylowY_normal (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerSylowY n hn S e).Normal := by
  obtain ⟨hY, _⟩ := (wreath_center_involution_and_quaternion_coordinates n hn).quaternion_quotient
  let := hY
  rw [centralizerSylowY_eq_original_map]
  exact hY.map _ (centralizerCoordinates n hn S e).symm.surjective

@[expose] def centralizerSylowYQuotientEquiv (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerSylow n hn S e ⧸ centralizerSylowY n hn S e ≃*
      Multiplicative (ZMod (2 ^ n)) := by
  let hY := (wreath_center_involution_and_quaternion_coordinates n hn).quaternion_quotient.choose
  let := hY
  let E := (wreath_center_involution_and_quaternion_coordinates n hn).quaternion_quotient.choose_spec.1.some
  exact (QuotientGroup.congr (centralizerSylowY n hn S e) (Original.Y (2 ^ n))
    (centralizerCoordinates n hn S e)
    ((Subgroup.map_symm_eq_iff_map_eq _).mp
      (centralizerSylowY_eq_original_map n hn S e).symm)).trans E

theorem centralizerSylowY_quotient_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (centralizerSylow n hn S e ⧸ centralizerSylowY n hn S e) = 2 ^ n := by
  rw [Nat.card_congr (centralizerSylowYQuotientEquiv n hn S e).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem centralizerSylowY_quotient_isCyclic (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsCyclic (centralizerSylow n hn S e ⧸ centralizerSylowY n hn S e) :=
  (centralizerSylowYQuotientEquiv n hn S e).isCyclic.mpr inferInstance

@[expose] def centralizerQuaternionEquiv (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    QuaternionGroup (2 ^ n / 2) ≃* centralizerQuaternion n hn S e :=
  (wreath_center_involution_and_quaternion_coordinates n hn).quaternion.some.trans
    ((Original.Y (2 ^ n)).equivMapOfInjective
      (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e))
      (wreathModelHom_injective _ _))

theorem centralizerQuaternion_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (centralizerQuaternion n hn S e) = 2 * 2 ^ n := by
  rw [centralizerQuaternion, modelY,
    Subgroup.card_map_of_injective (wreathModelHom_injective _ _)]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).quaternion_card

theorem centralizerSylowY_normalClosure (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalClosure {(centralizerCoordinates n hn S e).symm (Original.d (2 ^ n))} =
      centralizerSylowY n hn S e := by
  rw [centralizerSylowY_eq_original_map,
    ← (wreath_center_involution_and_quaternion_coordinates n hn).normal_closure,
    Subgroup.map_normalClosure _ _ (centralizerCoordinates n hn S e).symm.surjective,
    Set.image_singleton]
  rfl

@[expose] def centralizerTransfer [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    involutionCentralizer n S e →*
      centralizerSylow n hn S e ⧸ CFSG.Semidihedral.FocalTransfer.conjugatePairFocal
        (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) :=
  CFSG.Semidihedral.FocalTransfer.focalTransfer (centralizerSylow n hn S e :
    Subgroup (involutionCentralizer n S e))

@[expose] def centralizerTransferKernel [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup (involutionCentralizer n S e) := (centralizerTransfer n hn S e).ker

instance centralizerTransferKernel_normal [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerTransferKernel n hn S e).Normal := inferInstanceAs
      (centralizerTransfer n hn S e).ker.Normal

theorem centralizerTransfer_surjective [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Surjective (centralizerTransfer n hn S e) :=
  CFSG.Semidihedral.FocalTransfer.focalTransfer_surjective (centralizerSylow n hn S e)

theorem centralizerTransferKernel_inf_sylow [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerTransferKernel n hn S e ⊓ (centralizerSylow n hn S e :
      Subgroup (involutionCentralizer n S e)) =
        (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)).focalSubgroup := by
  exact (CFSG.Semidihedral.FocalTransfer.ker_focalTransfer_inf
    (centralizerSylow n hn S e)).trans
      (CFSG.Semidihedral.FocalTransfer.map_conjugatePairFocal _)

theorem centralizer_conjugatePairFocal_eq_sylowY [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    CFSG.Semidihedral.FocalTransfer.conjugatePairFocal
      (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) =
        centralizerSylowY n hn S e := by
  apply Subgroup.map_subtype_inj.mp
  rw [CFSG.Semidihedral.FocalTransfer.map_conjugatePairFocal,
    centralizer_focal_eq_quaternion_of_simple hnonab, centralizerSylowY_map]

@[expose] def centralizerTransferQuotientEquiv [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    involutionCentralizer n S e ⧸ centralizerTransferKernel n hn S e ≃*
      Multiplicative (ZMod (2 ^ n)) :=
  (QuotientGroup.quotientKerEquivOfSurjective (centralizerTransfer n hn S e)
    (centralizerTransfer_surjective n hn S e)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (centralizer_conjugatePairFocal_eq_sylowY hnonab n hn S e)).trans
          (centralizerSylowYQuotientEquiv n hn S e))

theorem centralizerTransferKernel_index [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerTransferKernel n hn S e).index = 2 ^ n := by
  rw [Subgroup.index_eq_card,
    Nat.card_congr (centralizerTransferQuotientEquiv hnonab n hn S e).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem centralizerTransferKernel_quotient_isPGroup [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsPGroup 2 (involutionCentralizer n S e ⧸ centralizerTransferKernel n hn S e) :=
  ((centralizerSylow n hn S e).isPGroup'.to_quotient
    (CFSG.Semidihedral.FocalTransfer.conjugatePairFocal
      (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)))).of_equiv
        (QuotientGroup.quotientKerEquivOfSurjective (centralizerTransfer n hn S e)
          (centralizerTransfer_surjective n hn S e)).symm

theorem centralizerTransferKernel_inf_eq_quaternion [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerTransferKernel n hn S e ⊓ (centralizerSylow n hn S e :
      Subgroup (involutionCentralizer n S e)) = centralizerQuaternion n hn S e := by
  rw [centralizerTransferKernel_inf_sylow,
    centralizer_focal_eq_quaternion_of_simple hnonab]

theorem centralizerQuaternion_le_transferKernel [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerQuaternion n hn S e ≤ centralizerTransferKernel n hn S e := by
  rw [← centralizerTransferKernel_inf_eq_quaternion hnonab n hn S e]
  exact inf_le_left

theorem centralizerTransferKernel_sylow [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ∃ T : Sylow 2 (centralizerTransferKernel n hn S e),
      (T : Subgroup (centralizerTransferKernel n hn S e)) =
        (centralizerQuaternion n hn S e).subgroupOf (centralizerTransferKernel n hn S e) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection
    2 (centralizerTransferKernel n hn S e) (centralizerSylow n hn S e)
  refine ⟨T, ?_⟩
  rw [← Subgroup.inf_subgroupOf_right, inf_comm,
    centralizerTransferKernel_inf_eq_quaternion hnonab n hn S e] at hT
  exact hT

theorem centralizerTransferKernel_odd_order_mem [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : involutionCentralizer n S e) (hg : Odd (orderOf g)) :
    g ∈ centralizerTransferKernel n hn S e := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply (QuotientGroup.eq_one_iff (N := centralizerTransferKernel n hn S e) g).mp
  exact CFSG.Semidihedral.pPrime_element_hom_eq_one
    (centralizerTransferKernel_quotient_isPGroup n hn S e)
    (QuotientGroup.mk' (centralizerTransferKernel n hn S e)) hg.not_two_dvd_nat

theorem centralizerQuaternion_le_kernel_commutator [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerQuaternion n hn S e ≤
      (commutator (centralizerTransferKernel n hn S e)).map
        (centralizerTransferKernel n hn S e).subtype := by
  let P := centralizerSylow n hn S e
  let f := centralizerCoordinates n hn S e
  let K := centralizerTransferKernel n hn S e
  let D := (commutator K).map K.subtype
  obtain ⟨g, _, hodd, horder⟩ := modelVNormalizer_exists_odd_three_power_actor n hn P f
    (centralizerVNormalizerQuotient_sym3_of_simple hnonab n hn S e)
  have hgK : g.val ∈ K := centralizerTransferKernel_odd_order_mem n hn S e g.val
    (by rwa [Subgroup.orderOf_coe])
  have hQK : modelQ P f ≤ K := (modelQ_le_modelY n P f).trans
    (centralizerQuaternion_le_transferKernel hnonab n hn S e)
  have hQD : modelQ P f ≤ D :=
    modelQ_le_relative_commutator_of_order_three n hn P f g horder K hQK hgK
  have : D.Normal := by
    dsimp [D]
    rw [Subgroup.map_subtype_commutator]
    infer_instance
  rw [← centralizerSylowY_map, Subgroup.map_le_iff_le_comap,
    ← centralizerSylowY_normalClosure]
  apply Subgroup.normalClosure_le_normal
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  subst a
  change wreathModelHom P f (Original.d (2 ^ n)) ∈ D
  exact hQD (Subgroup.mem_map.mpr
    ⟨Original.d _, Subgroup.subset_closure (by simp), rfl⟩)

theorem centralizerTransferKernel_no_index_two [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ∀ H : Subgroup (centralizerTransferKernel n hn S e), H.index ≠ 2 := by
  obtain ⟨T, hT⟩ := centralizerTransferKernel_sylow hnonab n hn S e
  apply (CFSG.Semidihedral.FocalTransfer.no_index_two_iff_derived_subgroupOf_eq_top T).mpr
  apply Subgroup.subgroupOf_eq_top.mpr
  rw [hT]
  intro a ha
  have hderived := centralizerQuaternion_le_kernel_commutator hnonab n hn S e ha
  obtain ⟨b, hb, heq⟩ := hderived
  exact (Subtype.ext heq : b = a) ▸ hb

theorem hom_to_two_group_eq_one_of_no_index_two {E : Type u} [Group E]
    (hE : ∀ M : Subgroup E, M.index ≠ 2)
    {P : Type v} [Group P] [Finite P] (hP : IsPGroup 2 P) (f : E →* P) : f = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : IsPGroup 2 f.range := hP.to_subgroup _
  let : Group.IsNilpotent f.range := hR.isNilpotent
  apply MonoidHom.ext
  intro x
  change f x = 1
  by_contra hfx
  have hx : f.rangeRestrict x ≠ 1 := by
    intro h
    exact hfx (congrArg Subtype.val h)
  have hdvd : 2 ∣ Nat.card f.range := (hR.dvd_orderOf hx).trans (orderOf_dvd_natCard _)
  obtain ⟨M, hM, _⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
  exact hE (M.comap f.rangeRestrict)
    ((M.index_comap_of_surjective f.rangeRestrict_surjective).trans hM)

theorem centralizerTransferKernel_hom_to_two_group_eq_one [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {P : Type v} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (f : centralizerTransferKernel n hn S e →* P) : f = 1 :=
  hom_to_two_group_eq_one_of_no_index_two
    (centralizerTransferKernel_no_index_two hnonab n hn S e) hP f

structure WreathedCentralizerQuaternionResidualData [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Prop where
  actual_sylow : (centralizerSylow n hn S e :
    Subgroup (involutionCentralizer n S e)).map (involutionCentralizer n S e).subtype = S
  kernel_normal : (centralizerTransferKernel n hn S e).Normal
  kernel_index : (centralizerTransferKernel n hn S e).index = 2 ^ n
  kernel_intersection : centralizerTransferKernel n hn S e ⊓
    (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) =
      centralizerQuaternion n hn S e
  ambient_quaternion : (centralizerQuaternion n hn S e).map
    (involutionCentralizer n S e).subtype = modelY S e
  ambient_intersection : ((centralizerTransferKernel n hn S e).map
    (involutionCentralizer n S e).subtype) ⊓ (S : Subgroup G) = modelY S e
  quaternion_sylow : ∃ T : Sylow 2 (centralizerTransferKernel n hn S e),
    (T : Subgroup (centralizerTransferKernel n hn S e)) =
      (centralizerQuaternion n hn S e).subgroupOf (centralizerTransferKernel n hn S e)
  quaternion : Nonempty (QuaternionGroup (2 ^ n / 2) ≃* centralizerQuaternion n hn S e)
  quaternion_order : Nat.card (centralizerQuaternion n hn S e) = 2 * 2 ^ n
  no_index_two : ∀ M : Subgroup (centralizerTransferKernel n hn S e), M.index ≠ 2
  full_center_weak_closure : ∀ u g : G, u ∈ modelCenter S e →
    g ∈ involutionCentralizer n S e → g⁻¹ * u * g ∈ (S : Subgroup G) → g⁻¹ * u * g = u
  base_normalizer_order :
    Nat.card (Subgroup.normalizer
      (modelBase (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
        Set (involutionCentralizer n S e)) ⧸
      (Subgroup.centralizer
        (modelBase (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
          Set (involutionCentralizer n S e))).subgroupOf
        (Subgroup.normalizer
          (modelBase (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
            Set (involutionCentralizer n S e)))) = 2
  ambient_v_normalizer : Subgroup.normalizer (modelV S e : Set G) ≤
    involutionCentralizer n S e
  centralizer_v_normalizer : Nonempty (Subgroup.normalizer
    (modelV (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
      Set (involutionCentralizer n S e)) ⧸
    modelVInnerCentralizer (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) ≃*
      Equiv.Perm (Fin 3))

theorem wreathed_involution_centralizer_quaternion_two_residual [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    WreathedCentralizerQuaternionResidualData n hn S e := by
  refine ⟨?_, inferInstance, centralizerTransferKernel_index hnonab n hn S e,
    centralizerTransferKernel_inf_eq_quaternion hnonab n hn S e,
    centralizerQuaternion_map n hn S e, ?_,
    centralizerTransferKernel_sylow hnonab n hn S e,
    ⟨centralizerQuaternionEquiv n hn S e⟩, centralizerQuaternion_card n hn S e,
    centralizerTransferKernel_no_index_two hnonab n hn S e, ?_,
    centralizerBaseNormalizerQuotient_order_two n hn S e,
    modelVNormalizer_le_involutionCentralizer n hn S e,
    centralizerVNormalizerQuotient_sym3_of_simple hnonab n hn S e⟩
  · rw [centralizerSylow_coe]
    exact Subgroup.map_subgroupOf_eq_of_le (sylow_le_involutionCentralizer n hn S e)
  · rw [← centralizerQuaternion_map n hn S e,
      ← centralizerTransferKernel_inf_eq_quaternion hnonab n hn S e,
      Subgroup.map_inf _ _ _ Subtype.coe_injective, centralizerSylow_coe,
      Subgroup.map_subgroupOf_eq_of_le (sylow_le_involutionCentralizer n hn S e)]
  · intro u g hu hg hconj
    exact centralizer_original_center_weakly_closed_ambient n hn S e u g hu hg hconj

end CFSG.Wreathed
