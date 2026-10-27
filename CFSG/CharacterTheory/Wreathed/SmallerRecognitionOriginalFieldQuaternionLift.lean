module

public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalQuotient
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddKernelSylowEquiv

public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open ActualCentralizerSemilinear
open scoped Classical
universe u v

@[expose] def componentPreimage {N : Type u} [Group N] {H : Type v} [Group H]
    (pi : N →* H) (B : Subgroup N) (M : Subgroup H) : Subgroup N :=
  B ⊓ M.comap pi

@[expose] def componentRestriction {N : Type u} [Group N] {H : Type v} [Group H]
    (pi : N →* H) (B : Subgroup N) (M : Subgroup H) :
    componentPreimage pi B M →* M where
  toFun d := ⟨pi d.val, d.property.2⟩
  map_one' := Subtype.ext pi.map_one
  map_mul' d e := Subtype.ext (pi.map_mul d e)

theorem componentRestriction_coe {N : Type u} [Group N] {H : Type v} [Group H]
    (pi : N →* H) (B : Subgroup N) (M : Subgroup H)
    (d : componentPreimage pi B M) :
    (componentRestriction pi B M d : H) = pi d.val := rfl

theorem componentRestriction_surjective {N : Type u} [Group N] {H : Type v} [Group H]
    (pi : N →* H) (B : Subgroup N) (M : Subgroup H) (hcover : M ≤ B.map pi) :
    Function.Surjective (componentRestriction pi B M) := by
  intro m
  obtain ⟨b, hb, hbm⟩ := Subgroup.mem_map.mp (hcover m.property)
  refine ⟨⟨b, hb, ?_⟩, Subtype.ext hbm⟩
  change pi b ∈ M
  exact hbm ▸ m.property

theorem componentRestriction_ker {N : Type u} [Group N] {H : Type v} [Group H]
    (pi : N →* H) (B : Subgroup N) (M : Subgroup H) :
    (componentRestriction pi B M).ker = pi.ker.subgroupOf (componentPreimage pi B M) := by
  ext d
  change componentRestriction pi B M d = 1 ↔ pi d.val = 1
  exact Subtype.ext_iff

theorem componentRestriction_odd_kernel {N : Type u} [Group N]
    {H : Type v} [Group H] (pi : N →* H) (B : Subgroup N) (M : Subgroup H)
    (hodd : Odd (Nat.card pi.ker)) : Odd (Nat.card (componentRestriction pi B M).ker) := by
  rw [componentRestriction_ker]
  exact hodd.of_dvd_nat (Subgroup.card_comap_dvd_of_injective _
    (componentPreimage pi B M).subtype (componentPreimage pi B M).subtype_injective)

theorem central_involution_mem_sylow {N : Type u} [Group N]
    (x : N) (hx : x ∈ Subgroup.center N) (ho : orderOf x = 2) (Q : Sylow 2 N) : x ∈ Q := by
  let A := Subgroup.zpowers x
  have hAZ : A ≤ Subgroup.center N := Subgroup.zpowers_le.mpr hx
  let : A.Normal := Subgroup.normal_of_le_center hAZ
  have hA : IsPGroup 2 A := IsPGroup.of_card (by
    rw [Nat.card_zpowers, ho]
    exact (pow_one 2).symm)
  exact hA.le_sylow_of_normal Q (Subgroup.mem_zpowers x)

variable {G : Type} [Group G] [Finite G]

abbrev originalComponentPreimage (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :=
  componentPreimage (centralizerOddCoreMap n S e)
    (ComponentCoveringLocal.originalCentralizerSubgroup n S e K)
    (CFSG.layer (centralizerOddCoreQuotient n S e))

@[expose] def originalComponentRestriction (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    originalComponentPreimage n S e K →* CFSG.layer (centralizerOddCoreQuotient n S e) :=
  componentRestriction (centralizerOddCoreMap n S e)
    (ComponentCoveringLocal.originalCentralizerSubgroup n S e K)
    (CFSG.layer (centralizerOddCoreQuotient n S e))

omit [Finite G] in
theorem originalComponentRestriction_surjective (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K) :
    Function.Surjective (originalComponentRestriction n S e K) :=
  componentRestriction_surjective _ _ _ hcover

theorem originalComponentRestriction_odd_kernel (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    Odd (Nat.card (originalComponentRestriction n S e K).ker) := by
  apply componentRestriction_odd_kernel
  have hker : (centralizerOddCoreMap n S e).ker = centralizerOddCore n S e :=
    QuotientGroup.ker_mk' _
  rw [hker]
  exact CFSG.ComponentClassification.OddCore.odd_card _

variable [IsSimpleGroup G]

theorem original_involution_mem_component_preimage
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G) (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K) :
    centralInvolution n S e ∈ originalComponentPreimage n S e K :=
  ⟨hxK, ActualProjectiveLayer.centralizerActualLayer_involution_mem
    hnonab n hn S e hfour⟩

theorem original_component_preimage_central_involution
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G) (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K) :
    let xD : originalComponentPreimage n S e K :=
      ⟨centralInvolution n S e,
        original_involution_mem_component_preimage hnonab n hn S e hfour K hxK⟩
    xD ∈ Subgroup.center (originalComponentPreimage n S e K) ∧ orderOf xD = 2 := by
  let xD : originalComponentPreimage n S e K :=
    ⟨centralInvolution n S e,
      original_involution_mem_component_preimage hnonab n hn S e hfour K hxK⟩
  constructor
  · apply Subgroup.mem_center_iff.mpr
    intro d
    exact Subtype.ext (Subgroup.mem_center_iff.mp (centralInvolution_mem_center n S e) d.val)
  · rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    change orderOf (wreathModelHom S e (Original.x (2 ^ n))) = 2
    rw [orderOf_injective _ (wreathModelHom_injective S e)]
    exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1

theorem original_involution_mem_every_component_sylow
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G) (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K)
    (Q : Sylow 2 (originalComponentPreimage n S e K)) :
    (⟨centralInvolution n S e,
        original_involution_mem_component_preimage hnonab n hn S e hfour K hxK⟩ :
      originalComponentPreimage n S e K) ∈ Q := by
  obtain ⟨hZ, ho⟩ := original_component_preimage_central_involution hnonab n hn S e hfour K hxK
  exact central_involution_mem_sylow _ hZ ho Q


@[expose] def originalLayerQuaternionEquiv
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    QuaternionGroup (2 ^ n / 2) ≃* actualLayerSylow hnonab n hn S e hfour := by
  let M := CFSG.layer (centralizerOddCoreQuotient n S e)
  let T := actualLayerSylow hnonab n hn S e hfour
  let E : T ≃* modelY (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e) :=
    ((T : Subgroup M).equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr (actualLayerSylow_image hnonab n hn S e hfour))
  exact ((originalYQuaternionEquiv n hn).trans
    (modelYEquiv (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e))).trans E.symm

theorem original_component_preimage_sylow_quaternion
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
    (Q : Sylow 2 (originalComponentPreimage n S e K)) :
    Nonempty (QuaternionGroup (2 ^ n / 2) ≃* Q) := by
  let f := originalComponentRestriction n S e K
  have hf : Function.Surjective f := originalComponentRestriction_surjective n S e K hcover
  obtain ⟨E⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.odd_kernel_sylow_equiv f hf
    (originalComponentRestriction_odd_kernel n S e K) Q
  let F := Sylow.equiv (actualLayerSylow hnonab n hn S e hfour) (Q.mapSurjective hf)
  exact ⟨((originalLayerQuaternionEquiv hnonab n hn S e hfour).trans F).trans E.symm⟩


theorem original_component_preimage_quaternion_sylow_lift
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G) (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K) :
    let D := originalComponentPreimage n S e K
    let f := originalComponentRestriction n S e K
    let xD : D := ⟨centralInvolution n S e,
      original_involution_mem_component_preimage hnonab n hn S e hfour K hxK⟩
    Function.Surjective f ∧ Odd (Nat.card f.ker) ∧
      xD ∈ Subgroup.center D ∧ orderOf xD = 2 ∧
      ∀ Q : Sylow 2 D,
        xD ∈ Q ∧ Nonempty (QuaternionGroup (2 ^ n / 2) ≃* Q) ∧
          Function.Injective (f.comp (Q : Subgroup D).subtype) ∧
          (∀ q : Q, (f.comp (Q : Subgroup D).subtype q :
              centralizerOddCoreQuotient n S e) =
            centralizerOddCoreMap n S e ((q : D) : involutionCentralizer n S e)) := by
  obtain ⟨hZ, ho⟩ := original_component_preimage_central_involution hnonab n hn S e hfour K hxK
  refine ⟨originalComponentRestriction_surjective n S e K hcover,
    originalComponentRestriction_odd_kernel n S e K, hZ, ho, ?_⟩
  intro Q
  exact ⟨original_involution_mem_every_component_sylow hnonab n hn S e hfour K hxK Q,
    original_component_preimage_sylow_quaternion hnonab n hn S e hfour K hcover Q,
    CFSG.DisconnectedInvolutionGraph.Helpers.odd_kernel_two_subgroup_injective _
      (originalComponentRestriction_odd_kernel n S e K) _ Q.isPGroup', fun _ => rfl⟩

end CFSG.Wreathed.SmallerRecognitionOriginalField
