module

public import CFSG.CharacterTheory.Semidihedral.StructureTransport
public import CFSG.CharacterTheory.Semidihedral.PrimeResidual
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Dihedral.BrauerSuzuki
public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.Foundations.Basic

public section

namespace CFSG.Semidihedral.QuaternionFocalFactorization

open CFSG.Open
open scoped Pointwise

universe u

variable {H : Type u} [Group H]

@[expose] def oddGenerated (H : Type u) [Group H] : Subgroup H :=
  Subgroup.closure {x : H | Odd (orderOf x)}

theorem oddGenerated_eq_primeResidual_two : oddGenerated H = primeResidual 2 H := by
  unfold oddGenerated primeResidual
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, ← Nat.coprime_two_left,
    Nat.prime_two.coprime_iff_not_dvd]

instance oddGenerated_characteristic : (oddGenerated H).Characteristic := by
  rw [oddGenerated_eq_primeResidual_two]
  infer_instance

instance oddGenerated_normal : (oddGenerated H).Normal := inferInstance

@[expose] def originalRotation (n : ℕ) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : H := f (r n)

@[expose] def originalReflection (n : ℕ) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : H := f (s n)

@[expose] def originalQuaternion (n : ℕ) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : Subgroup H :=
  Subgroup.closure {originalRotation n S f ^ 2,
    originalRotation n S f * originalReflection n S f}

@[expose] def originalInvolution (n : ℕ) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : H :=
  originalRotation n S f ^ (2 ^ (n - 2))

theorem originalQuaternion_eq_map (n : ℕ) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) :
    originalQuaternion n S f =
      (Subgroup.closure {f (r n) ^ 2, f (r n) * f (s n)}).map
        (S : Subgroup H).subtype := by
  rw [MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, map_pow, map_mul]
  rfl

theorem originalQuaternion_le_sylow (n : ℕ) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : originalQuaternion n S f ≤ S := by
  rw [originalQuaternion_eq_map]
  exact Subgroup.map_subtype_le _

theorem originalQuaternion_subgroupOf_sylow (n : ℕ) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) :
    (originalQuaternion n S f).subgroupOf (S : Subgroup H) =
      Subgroup.closure {f (r n) ^ 2, f (r n) * f (s n)} := by
  change (originalQuaternion n S f).comap (S : Subgroup H).subtype = _
  rw [originalQuaternion_eq_map,
    Subgroup.comap_map_eq_self_of_injective (S : Subgroup H).subtype_injective]

theorem originalQuaternion_index (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) :
    ((originalQuaternion n S f).subgroupOf (S : Subgroup H)).index = 2 := by
  rw [originalQuaternion_subgroupOf_sylow]
  exact (supplied_index_two n hn f _).mpr (Or.inr (Or.inr rfl))

@[expose] noncomputable def originalQuaternionEquiv (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S) :
    QuaternionGroup (2 ^ (n - 3)) ≃* originalQuaternion n S f :=
  (suppliedQuaternionEquiv n hn f).trans
    ((Subgroup.equivMapOfInjective _ (S : Subgroup H).subtype
      (S : Subgroup H).subtype_injective).trans
        (MulEquiv.subgroupCongr (originalQuaternion_eq_map n S f).symm))

theorem originalQuaternionEquiv_coe (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (g : QuaternionGroup (2 ^ (n - 3))) :
    (originalQuaternionEquiv n hn S f g : H) = (f (quaternionHom n hn g) : H) :=
  rfl

theorem originalQuaternionEquiv_rotation (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S) :
    (originalQuaternionEquiv n hn S f (QuaternionGroup.a 1) : H) =
      originalRotation n S f ^ 2 := by
  rw [originalQuaternionEquiv_coe, quaternionHom_rotation, map_pow]
  rfl

theorem originalQuaternionEquiv_generator (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S) :
    (originalQuaternionEquiv n hn S f (QuaternionGroup.xa 0) : H) =
      originalRotation n S f * originalReflection n S f := by
  rw [originalQuaternionEquiv_coe, quaternionHom_generator, map_mul]
  rfl

theorem originalQuaternion_card (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) :
    Nat.card (originalQuaternion n S f) = 2 ^ (n - 1) := by
  rw [originalQuaternion_eq_map, Subgroup.card_map_of_injective
    (S : Subgroup H).subtype_injective]
  exact (supplied_subgroup_properties n hn f).2.2.2.2.2.2

theorem originalInvolution_eq_image (n : ℕ) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : originalInvolution n S f = (f (z n) : H) := by
  simp only [originalInvolution, originalRotation, z, half, map_pow, Subgroup.coe_pow]

theorem originalInvolution_mem_quaternion (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S) :
    originalInvolution n S f ∈ originalQuaternion n S f := by
  rw [originalInvolution_eq_image, originalQuaternion_eq_map]
  apply Subgroup.mem_map_of_mem
  rw [← map_quaternionSubgroup n f, mem_map_equiv_iff]
  exact z_mem_quaternionSubgroup n (by omega)

theorem originalInvolution_order (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : orderOf (originalInvolution n S f) = 2 := by
  rw [originalInvolution_eq_image, Subgroup.orderOf_coe, equiv_orderOf]
  exact orderOf_z n (by omega)

theorem originalQuaternion_unique_involution (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S) {x : H}
    (hxQ : x ∈ originalQuaternion n S f) (hx : orderOf x = 2) :
    x = originalInvolution n S f := by
  rw [originalQuaternion_eq_map] at hxQ
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hxQ
  have haord : orderOf a = 2 := by
    simpa only [orderOf_injective (S : Subgroup H).subtype
      (S : Subgroup H).subtype_injective] using hx
  have heq := supplied_quaternion_unique_involution n hn f a ha haord
  rw [modulus_div_two n (by omega)] at heq
  exact congrArg Subtype.val heq

theorem originalSylow_le_centralizer (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) :
    (S : Subgroup H) ≤ Subgroup.centralizer {originalInvolution n S f} := by
  have ht : f (z n) ∈ Subgroup.center S := by
    rw [(supplied_center n hn f).1, modulus_div_two n (by omega)]
    simpa only [z, map_pow] using (Subgroup.mem_zpowers (f (z n)))
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff, originalInvolution_eq_image]
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ht (⟨x, hx⟩ : S))

theorem focal_abelianization_index (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    ((commutator H).subgroupOf (S : Subgroup H)).index = 2 := by
  rw [← Subgroup.inf_subgroupOf_right (commutator H) (S : Subgroup H), inf_comm, hfocal]
  exact originalQuaternion_index n hn S f

theorem oddCore_eq_twoPrimeCore : oddCore H = pPrimeCore 2 H := by
  rw [oddCore_eq_piCore, pPrimeCore_eq_piCore]

theorem oddCore_le_oddGenerated [Finite H] : oddCore H ≤ oddGenerated H := by
  rw [oddCore_eq_twoPrimeCore, oddGenerated_eq_primeResidual_two]
  intro x hx
  apply pPrime_element_mem_primeResidual
  intro hdvd
  exact (Nat.prime_two.coprime_iff_not_dvd.mp (pPrimeCore_coprime_card (p := 2)))
    (hdvd.trans ((pPrimeCore 2 H).orderOf_dvd_natCard hx))

theorem oddGenerated_oddCore_map [Finite H] :
    (oddCore (oddGenerated H)).map (oddGenerated H).subtype = oddCore H := by
  have h := LocalCores.prime_set_core_normal_intersection
    (G := H) {q : Nat.Primes | q.val ≠ 2}
    (inferInstance : (oddGenerated H).Normal)
  rw [← oddCore_eq_piCore, ← oddCore_eq_piCore,
    inf_eq_right.mpr oddCore_le_oddGenerated] at h
  exact h

theorem oddGenerated_index [Finite H] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    (oddGenerated H).index = 2 := by
  rw [oddGenerated_eq_primeResidual_two]
  exact primeResidual_index S (focal_abelianization_index n hn S f hfocal)

theorem oddGenerated_inf_sylow [Finite H] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    oddGenerated H ⊓ (S : Subgroup H) = originalQuaternion n S f := by
  rw [inf_comm, oddGenerated_eq_primeResidual_two,
    sylow_inf_primeResidual_eq_commutator S
      (focal_abelianization_index n hn S f hfocal), hfocal]

theorem originalQuaternion_le_oddGenerated [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    originalQuaternion n S f ≤ oddGenerated H := by
  rw [← oddGenerated_inf_sylow n hn S f hfocal]
  exact inf_le_left

theorem oddGenerated_original_sylow [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    ∃ T : Sylow 2 (oddGenerated H),
      (T : Subgroup (oddGenerated H)) =
        (originalQuaternion n S f).subgroupOf (oddGenerated H) := by
  rw [oddGenerated_eq_primeResidual_two]
  obtain ⟨T, hT⟩ := sylow_inf_primeResidual S
    (focal_abelianization_index n hn S f hfocal)
  refine ⟨T, ?_⟩
  rw [sylow_inf_primeResidual_eq_commutator S
    (focal_abelianization_index n hn S f hfocal), hfocal] at hT
  exact hT

theorem original_quaternion_focal_odd_generated_subgroup_and_sylow_transport [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    (oddGenerated H).Characteristic ∧ (oddGenerated H).index = 2 ∧
      oddGenerated H ⊓ (S : Subgroup H) = originalQuaternion n S f ∧
      oddCore H ≤ oddGenerated H ∧
      (oddCore (oddGenerated H)).map (oddGenerated H).subtype = oddCore H ∧
      (∃ T : Sylow 2 (oddGenerated H),
        (T : Subgroup (oddGenerated H)) =
          (originalQuaternion n S f).subgroupOf (oddGenerated H)) ∧
      Nonempty (QuaternionGroup (2 ^ (n - 3)) ≃* originalQuaternion n S f) ∧
      Nat.card (originalQuaternion n S f) = 2 ^ (n - 1) ∧
      orderOf (originalInvolution n S f) = 2 ∧
      (S : Subgroup H) ≤ Subgroup.centralizer {originalInvolution n S f} := by
  exact ⟨inferInstance, oddGenerated_index n hn S f hfocal,
    oddGenerated_inf_sylow n hn S f hfocal, oddCore_le_oddGenerated,
    oddGenerated_oddCore_map, oddGenerated_original_sylow n hn S f hfocal,
    ⟨originalQuaternionEquiv n hn S f⟩, originalQuaternion_card n hn S f,
    originalInvolution_order n hn S f, originalSylow_le_centralizer n hn S f⟩


@[expose] noncomputable def oddGeneratedSylow [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    Sylow 2 (oddGenerated H) :=
  (oddGenerated_original_sylow n hn S f hfocal).choose

theorem oddGeneratedSylow_eq [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    (oddGeneratedSylow n hn S f hfocal : Subgroup (oddGenerated H)) =
      (originalQuaternion n S f).subgroupOf (oddGenerated H) :=
  (oddGenerated_original_sylow n hn S f hfocal).choose_spec

@[expose] noncomputable def oddGeneratedQuaternionEquiv [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    QuaternionGroup (2 ^ (n - 3)) ≃* oddGeneratedSylow n hn S f hfocal :=
  (originalQuaternionEquiv n hn S f).trans
    ((Subgroup.subgroupOfEquivOfLe
      (originalQuaternion_le_oddGenerated n hn S f hfocal)).symm.trans
        (MulEquiv.subgroupCongr (oddGeneratedSylow_eq n hn S f hfocal).symm))

theorem oddGeneratedQuaternionEquiv_coe [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f)
    (g : QuaternionGroup (2 ^ (n - 3))) :
    ((oddGeneratedQuaternionEquiv n hn S f hfocal g : oddGenerated H) : H) =
      (f (quaternionHom n hn g) : H) := rfl

@[expose] def oddGeneratedInvolution [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    oddGenerated H :=
  ⟨originalInvolution n S f, originalQuaternion_le_oddGenerated n hn S f hfocal
    (originalInvolution_mem_quaternion n hn S f)⟩

theorem oddGeneratedInvolution_mem_sylow [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    oddGeneratedInvolution n hn S f hfocal ∈ oddGeneratedSylow n hn S f hfocal := by
  change oddGeneratedInvolution n hn S f hfocal ∈
    (oddGeneratedSylow n hn S f hfocal : Subgroup (oddGenerated H))
  rw [oddGeneratedSylow_eq]
  exact originalInvolution_mem_quaternion n hn S f

theorem oddGeneratedInvolution_order [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    orderOf (oddGeneratedInvolution n hn S f hfocal) = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact originalInvolution_order n hn S f

theorem oddGeneratedInvolution_central_mod_core [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    QuotientGroup.mk' (oddCore (oddGenerated H))
      (oddGeneratedInvolution n hn S f hfocal) ∈
        Subgroup.center (oddGenerated H ⧸ oddCore (oddGenerated H)) := by
  have hquat : Nonempty ((oddGeneratedSylow n hn S f hfocal :
      Subgroup (oddGenerated H)) ≃* QuaternionGroup (2 ^ ((n - 1) - 2))) := by
    rw [show (n - 1) - 2 = n - 3 by omega]
    exact ⟨(oddGeneratedQuaternionEquiv n hn S f hfocal).symm⟩
  exact BrauerSuzuki.brauer_suzuki (n - 1) (by omega)
    (oddGeneratedSylow n hn S f hfocal) hquat (oddGeneratedInvolution n hn S f hfocal)
    (oddGeneratedInvolution_mem_sylow n hn S f hfocal)
    (oddGeneratedInvolution_order n hn S f hfocal)

theorem oddGenerated_core_comap [Finite H] :
    (oddCore H).comap (oddGenerated H).subtype = oddCore (oddGenerated H) := by
  rw [← oddGenerated_oddCore_map]
  exact Subgroup.comap_map_eq_self_of_injective (oddGenerated H).subtype_injective _

@[expose] def oddGeneratedCoreQuotientMap [Finite H] :
    oddGenerated H ⧸ oddCore (oddGenerated H) →* H ⧸ oddCore H :=
  QuotientGroup.map _ _ (oddGenerated H).subtype (le_of_eq oddGenerated_core_comap.symm)

theorem oddGeneratedCoreQuotientMap_mk [Finite H] (x : oddGenerated H) :
    oddGeneratedCoreQuotientMap (QuotientGroup.mk' (oddCore (oddGenerated H)) x) =
      QuotientGroup.mk' (oddCore H) (x : H) := rfl

theorem originalInvolution_commutes_with_oddGenerated_mod_core [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f)
    (x : H) (hx : x ∈ oddGenerated H) :
    QuotientGroup.mk' (oddCore H) x *
        QuotientGroup.mk' (oddCore H) (originalInvolution n S f) =
      QuotientGroup.mk' (oddCore H) (originalInvolution n S f) *
        QuotientGroup.mk' (oddCore H) x := by
  have h := Subgroup.mem_center_iff.mp
    (oddGeneratedInvolution_central_mod_core n hn S f hfocal)
    (QuotientGroup.mk' (oddCore (oddGenerated H)) (⟨x, hx⟩ : oddGenerated H))
  have hm := congrArg (oddGeneratedCoreQuotientMap (H := H)) h
  simpa only [map_mul, oddGeneratedCoreQuotientMap_mk, oddGeneratedInvolution] using hm

theorem oddGenerated_sup_originalSylow [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    oddGenerated H ⊔ (S : Subgroup H) = ⊤ := by
  have hindex := oddGenerated_index n hn S f hfocal
  have hnot : ¬ (S : Subgroup H) ≤ oddGenerated H := by
    intro hle
    have heq : originalQuaternion n S f = (S : Subgroup H) := by
      rw [← oddGenerated_inf_sylow n hn S f hfocal, inf_eq_right.mpr hle]
    have hqindex := originalQuaternion_index n hn S f
    rw [heq, Subgroup.subgroupOf_self, Subgroup.index_top] at hqindex
    norm_num at hqindex
  by_contra htop
  have hproper : oddGenerated H < oddGenerated H ⊔ (S : Subgroup H) := by
    apply lt_of_le_of_ne le_sup_left
    intro heq
    exact hnot (heq ▸ le_sup_right)
  have hlt := Subgroup.index_strictAnti hproper
  rw [hindex] at hlt
  have hpos := (oddGenerated H ⊔ (S : Subgroup H)).index_ne_zero_of_finite
  have hone : (oddGenerated H ⊔ (S : Subgroup H)).index = 1 := by omega
  exact htop (Subgroup.index_eq_one.mp hone)

theorem originalInvolution_central_mod_oddCore [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    QuotientGroup.mk' (oddCore H) (originalInvolution n S f) ∈
      Subgroup.center (H ⧸ oddCore H) := by
  let q := QuotientGroup.mk' (oddCore H)
  have hK : oddGenerated H ≤ (Subgroup.centralizer {q (originalInvolution n S f)}).comap q := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (originalInvolution_commutes_with_oddGenerated_mod_core n hn S f hfocal x hx)
  have hS : (S : Subgroup H) ≤ (Subgroup.centralizer {q (originalInvolution n S f)}).comap q := by
    intro x hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← map_mul, ← map_mul]
    exact congrArg q (Subgroup.mem_centralizer_singleton_iff.mp
      (originalSylow_le_centralizer n hn S f hx))
  have hall := sup_le hK hS
  rw [oddGenerated_sup_originalSylow n hn S f hfocal] at hall
  apply Subgroup.mem_center_iff.mpr
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (oddCore H) x
  exact Subgroup.mem_centralizer_singleton_iff.mp (hall (Subgroup.mem_top a))

theorem originalInvolution_mod_oddCore_ne_one [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S) :
    QuotientGroup.mk' (oddCore H) (originalInvolution n S f) ≠ 1 := by
  intro heq
  have hmem : originalInvolution n S f ∈ oddCore H := (QuotientGroup.eq_one_iff _).mp heq
  have hdvd := (oddCore H).orderOf_dvd_natCard hmem
  rw [originalInvolution_order n hn S f, oddCore_eq_twoPrimeCore] at hdvd
  exact (Nat.prime_two.coprime_iff_not_dvd.mp
    (pPrimeCore_coprime_card (p := 2))) hdvd

theorem original_quaternion_focal_involution_central_in_original_odd_core_quotient [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    QuotientGroup.mk' (oddCore H) (originalInvolution n S f) ≠ 1 ∧
      QuotientGroup.mk' (oddCore H) (originalInvolution n S f) ∈
        Subgroup.center (H ⧸ oddCore H) :=
  ⟨originalInvolution_mod_oddCore_ne_one n hn S f,
    originalInvolution_central_mod_oddCore n hn S f hfocal⟩


theorem centralizer_zpowers_eq_singleton (t : H) :
    Subgroup.centralizer ((Subgroup.zpowers t : Subgroup H) : Set H) =
      Subgroup.centralizer {t} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem oddCore_quotient_eq_bot [Finite H] : oddCore (H ⧸ oddCore H) = ⊥ := by
  rw [CFSG.oddCore_eq_piCore (H ⧸ oddCore H)]
  let e := QuotientGroup.quotientMulEquivOfEq (CFSG.oddCore_eq_piCore H)
  apply (Subgroup.map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [LocalCores.piCore_map_mulEquiv]
  exact LocalCores.prime_set_core_quotient {q : Nat.Primes | q.val ≠ 2}

theorem originalCentralizer_map_eq_top [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    (Subgroup.centralizer {originalInvolution n S f}).map (QuotientGroup.mk' (oddCore H)) =
      ⊤ := by
  let t := originalInvolution n S f
  have hA : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, originalInvolution_order n hn S f]
      norm_num)
  have hodd : ¬ 2 ∣ Nat.card (oddCore H) := by
    rw [oddCore_eq_twoPrimeCore]
    exact Nat.prime_two.coprime_iff_not_dvd.mp (pPrimeCore_coprime_card (p := 2))
  have h := Local.map_centralizer_eq_of_coprime 2 (oddCore H) hodd
    (Subgroup.zpowers t) hA
  rw [centralizer_zpowers_eq_singleton, MonoidHom.map_zpowers,
    centralizer_zpowers_eq_singleton] at h
  rw [h]
  exact Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr
    (originalInvolution_central_mod_oddCore n hn S f hfocal))

theorem original_element_oddCore_centralizer_factorization [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f)
    (x : H) :
    ∃ a ∈ oddCore H, ∃ c ∈ Subgroup.centralizer {originalInvolution n S f}, a * c = x := by
  let q := QuotientGroup.mk' (oddCore H)
  have hx : q x ∈ (Subgroup.centralizer {originalInvolution n S f}).map q := by
    rw [originalCentralizer_map_eq_top n hn S f hfocal]
    exact Subgroup.mem_top _
  obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
  refine ⟨x * c⁻¹, ?_, c, hc, by group⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change q (x * c⁻¹) = 1
  rw [map_mul, map_inv, hcx, mul_inv_cancel]

theorem original_oddCore_centralizer_set_product [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    (oddCore H : Set H) * (Subgroup.centralizer {originalInvolution n S f} : Set H) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨a, ha, c, hc, h⟩ := original_element_oddCore_centralizer_factorization n hn S f hfocal x
  exact Set.mem_mul.mpr ⟨a, ha, c, hc, h⟩

theorem original_oddCore_centralizer_sup [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    oddCore H ⊔ Subgroup.centralizer {originalInvolution n S f} = ⊤ := by
  apply top_unique
  intro x _
  exact Subgroup.mem_sup_of_normal_left.mpr
    (original_element_oddCore_centralizer_factorization n hn S f hfocal x)

theorem originalCentralizer_quotient_kernel
    (n : ℕ) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S) :
    ((QuotientGroup.mk' (oddCore H)).comp
      (Subgroup.centralizer {originalInvolution n S f}).subtype).ker =
        (oddCore H).subgroupOf (Subgroup.centralizer {originalInvolution n S f}) := by
  ext x
  change QuotientGroup.mk' (oddCore H) (x : H) = 1 ↔ (x : H) ∈ oddCore H
  exact QuotientGroup.eq_one_iff (x : H)

theorem originalCentralizer_oddCore [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    oddCore (Subgroup.centralizer {originalInvolution n S f}) =
      (oddCore H).subgroupOf (Subgroup.centralizer {originalInvolution n S f}) := by
  let C := Subgroup.centralizer {originalInvolution n S f}
  let q := QuotientGroup.mk' (oddCore H)
  let φ := q.comp C.subtype
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ C.map q := by
      rw [originalCentralizer_map_eq_top n hn S f hfocal]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨c, hc⟩, hcy⟩
  have hker : φ.ker = (oddCore H).subgroupOf C :=
    originalCentralizer_quotient_kernel n S f
  have hcop : Nat.Coprime 2 (Nat.card φ.ker) := by
    rw [hker]
    have hR : Nat.Coprime 2 (Nat.card (oddCore H)) := by
      rw [oddCore_eq_twoPrimeCore]
      exact pPrimeCore_coprime_card (p := 2)
    apply hR.coprime_dvd_right
    rw [← Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hcoremap := Local.pPrimeCore_map_eq_of_coprime_ker 2 φ hsurj hcop
  rw [← oddCore_eq_twoPrimeCore, ← oddCore_eq_twoPrimeCore, oddCore_quotient_eq_bot] at hcoremap
  have hle : oddCore C ≤ φ.ker := (Subgroup.map_eq_bot_iff _).mp hcoremap
  have hkerle : φ.ker ≤ oddCore C := by
    exact (le_sSup ⟨inferInstance, Nat.coprime_two_left.mp hcop⟩ : φ.ker ≤ oddCore C)
  exact (le_antisymm hle hkerle).trans hker

theorem originalCentralizer_oddCore_map [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H = originalQuaternion n S f) :
    (oddCore (Subgroup.centralizer {originalInvolution n S f})).map
      (Subgroup.centralizer {originalInvolution n S f}).subtype =
        oddCore H ⊓ Subgroup.centralizer {originalInvolution n S f} := by
  rw [originalCentralizer_oddCore n hn S f hfocal, Subgroup.subgroupOf_map_subtype]

theorem quaternion_focal_subgroup_forces_odd_core_centralizer_factorization [Finite H]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (f : SemidihedralGroup n ≃* S)
    (hfocal : (S : Subgroup H) ⊓ commutator H =
      Subgroup.closure {(f (r n) : H) ^ 2, (f (r n) : H) * (f (s n) : H)}) :
    let r := (f (CFSG.Semidihedral.r n) : H)
    let s := (f (CFSG.Semidihedral.s n) : H)
    let t := r ^ (2 ^ (n - 2))
    let Q := Subgroup.closure {r ^ 2, r * s}
    let R := oddCore H
    let K := Subgroup.closure {x : H | Odd (orderOf x)}
    let C := Subgroup.centralizer {t}
    K.Characteristic ∧ K.index = 2 ∧ K ⊓ (S : Subgroup H) = Q ∧
      (oddCore K).map K.subtype = R ∧
      QuotientGroup.mk' R t ≠ 1 ∧ QuotientGroup.mk' R t ∈ Subgroup.center (H ⧸ R) ∧
      (R : Set H) * (C : Set H) = Set.univ ∧
      (∀ x : H, ∃ a ∈ R, ∃ c ∈ C, a * c = x) ∧
      R ⊔ C = ⊤ ∧ oddCore C = R.subgroupOf C ∧
      (oddCore C).map C.subtype = R ⊓ C := by
  dsimp only
  exact ⟨oddGenerated_characteristic, oddGenerated_index n hn S f hfocal,
    oddGenerated_inf_sylow n hn S f hfocal, oddGenerated_oddCore_map,
    originalInvolution_mod_oddCore_ne_one n hn S f,
    originalInvolution_central_mod_oddCore n hn S f hfocal,
    original_oddCore_centralizer_set_product n hn S f hfocal,
    original_element_oddCore_centralizer_factorization n hn S f hfocal,
    original_oddCore_centralizer_sup n hn S f hfocal,
    originalCentralizer_oddCore n hn S f hfocal, originalCentralizer_oddCore_map n hn S f hfocal⟩

end CFSG.Semidihedral.QuaternionFocalFactorization
