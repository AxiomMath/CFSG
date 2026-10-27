module

public import CFSG.CharacterTheory.Semidihedral.InvolutionFusion
public import CFSG.CharacterTheory.Semidihedral.PrimeResidual

public section

namespace CFSG.Semidihedral.CentralizerResidual

open CFSG.Open CFSG.Semidihedral

variable {G : Type*} [Group G]

@[expose] def centeredInvolution (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : G := f (z n)

@[expose] def involutionCentralizer (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : Subgroup G :=
  Subgroup.centralizer {centeredInvolution n S f}

theorem sylow_le_involutionCentralizer (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : (S : Subgroup G) ≤ involutionCentralizer n S f := by
  have hz : f (z n) ∈ Subgroup.center S := by
    rw [← Subgroup.map_center_eq f]
    exact ⟨z n, z_mem_center n hn, rfl⟩
  intro g hg
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact congrArg (fun x : S => (x : G)) (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)

@[expose] def centralizerSylow (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : Sylow 2 (involutionCentralizer n S f) :=
  S.subtype (sylow_le_involutionCentralizer n hn S f)

@[expose] def centralizerCoordinates (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    SemidihedralGroup n ≃* centralizerSylow n hn S f :=
  f.trans (Subgroup.subgroupOfEquivOfLe (sylow_le_involutionCentralizer n hn S f)).symm

theorem centralizerCoordinates_coe (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (x : SemidihedralGroup n) :
    ((centralizerCoordinates n hn S f x : involutionCentralizer n S f) : G) =
      (f x : G) := rfl

theorem centeredInvolution_mem (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    centeredInvolution n S f ∈ involutionCentralizer n S f :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

@[expose] def centralInvolution (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : involutionCentralizer n S f :=
  ⟨centeredInvolution n S f, centeredInvolution_mem n S f⟩

theorem centralInvolution_mem_center (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    centralInvolution n S f ∈ Subgroup.center (involutionCentralizer n S f) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp g.property

theorem centralizerCoordinates_z (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    (centralizerCoordinates n hn S f (z n) : involutionCentralizer n S f) =
      centralInvolution n S f := by
  rfl

theorem conjugate_to_central_iff {H : Type*} [Group H] {x t : H}
    (ht : t ∈ Subgroup.center H) : IsConj x t ↔ x = t := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h.symm
    rw [Subgroup.mem_center_iff.mp ht c, mul_assoc, mul_inv_cancel, mul_one] at hc
    exact hc.symm
  · rintro rfl
    exact IsConj.refl _

theorem centralizer_s_not_fused (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    ¬ IsConj
      (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f)
      (centralizerCoordinates n hn S f (z n) : involutionCentralizer n S f) := by
  rw [centralizerCoordinates_z,
    conjugate_to_central_iff (centralInvolution_mem_center n S f)]
  intro h
  have hsz : s n = z n := (centralizerCoordinates n hn S f).injective
    (Subtype.ext (h.trans (centralizerCoordinates_z n hn S f).symm))
  rw [s_eq_element n (by omega), z_eq_element n (by omega), element_eq_iff] at hsz
  exact one_ne_zero hsz.2

theorem conjugate_in_centralizer_of_common_square {x y t : G}
    (hx : x ^ 2 = t) (hy : y ^ 2 = t) (hxy : IsConj x y)
    (hxC : x ∈ Subgroup.centralizer {t}) (hyC : y ∈ Subgroup.centralizer {t}) :
    IsConj (⟨x, hxC⟩ : Subgroup.centralizer {t}) ⟨y, hyC⟩ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have hs : c * t * c⁻¹ = t := by
    calc
      c * t * c⁻¹ = c * (x ^ 2) * c⁻¹ := by rw [hx]
      _ = (c * x * c⁻¹) ^ 2 := conj_pow.symm
      _ = t := by rw [hc, hy]
  have hcC : c ∈ Subgroup.centralizer {t} := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact mul_inv_eq_iff_eq_mul.mp hs
  apply isConj_iff.mpr
  exact ⟨⟨c, hcC⟩, Subtype.ext hc⟩

theorem quarter_square (n : ℕ) (hn : 4 ≤ n) :
    (r n ^ (2 ^ (n - 3))) ^ 2 = z n := by
  rw [← pow_mul, z, half_eq_two_mul_quarter (by omega), mul_comm]

theorem rs_square (n : ℕ) (hn : 3 ≤ n) : (r n * s n) ^ 2 = z n := by
  simpa only [pow_one] using reflection_square_nat n hn 1

theorem ambient_order_four_fusion [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    IsConj (f (r n * s n) : G) (f (r n ^ (2 ^ (n - 3))) : G) := by
  have h := (FocalFusion.semidihedral_focal_subgroup_four_cases n hn S f).2.2.2.2.mp hG
  have hq := h.2
  change IsConj ((f (r n) * f (s n) : S) : G)
    ((f (r n) ^ (modulus n / 4) : S) : G) at hq
  rw [modulus_div_four n hn, ← map_pow, ← map_mul] at hq
  exact hq

theorem centralizer_order_four_fusion [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    IsConj
      (centralizerCoordinates n hn S f (r n * s n) : involutionCentralizer n S f)
      (centralizerCoordinates n hn S f (r n ^ (2 ^ (n - 3))) : involutionCentralizer n S f) := by
  let ι := FocalFusion.ambientHom n (S : Subgroup G) f
  have hx : (f (r n * s n) : G) ^ 2 = centeredInvolution n S f := by
    change (ι (r n * s n)) ^ 2 = ι (z n)
    rw [← map_pow, rs_square n (by omega)]
  have hy : (f (r n ^ (2 ^ (n - 3))) : G) ^ 2 = centeredInvolution n S f := by
    change (ι (r n ^ (2 ^ (n - 3)))) ^ 2 = ι (z n)
    rw [← map_pow, quarter_square n hn]
  exact conjugate_in_centralizer_of_common_square hx hy (ambient_order_four_fusion n hn S f hG)
    (sylow_le_involutionCentralizer n hn S f (f (r n * s n)).property)
    (sylow_le_involutionCentralizer n hn S f (f (r n ^ (2 ^ (n - 3)))).property)

@[expose] def centralizerQuaternion (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : Subgroup (involutionCentralizer n S f) :=
  Subgroup.closure
    {(centralizerCoordinates n hn S f (r n) : involutionCentralizer n S f) ^ 2,
      (centralizerCoordinates n hn S f (r n) : involutionCentralizer n S f) *
        (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f)}

@[expose] def sylowQuaternion (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : Subgroup (centralizerSylow n hn S f) :=
  Subgroup.closure
    {centralizerCoordinates n hn S f (r n) ^ 2,
      centralizerCoordinates n hn S f (r n) * centralizerCoordinates n hn S f (s n)}

theorem sylowQuaternion_map (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    (sylowQuaternion n hn S f).map (centralizerSylow n hn S f :
      Subgroup (involutionCentralizer n S f)).subtype = centralizerQuaternion n hn S f := by
  rw [sylowQuaternion, centralizerQuaternion, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, map_pow, map_mul]
  rfl

theorem centralizerQuaternion_le_sylow (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    centralizerQuaternion n hn S f ≤ (centralizerSylow n hn S f :
      Subgroup (involutionCentralizer n S f)) := by
  rw [← sylowQuaternion_map n hn S f]
  exact Subgroup.map_subtype_le _

theorem centralizer_derived_eq_quaternion [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    (commutator (involutionCentralizer n S f)).subgroupOf (centralizerSylow n hn S f) =
      sylowQuaternion n hn S f := by
  let P := centralizerSylow n hn S f
  let e := centralizerCoordinates n hn S f
  let ι := FocalFusion.ambientHom n (P : Subgroup (involutionCentralizer n S f)) e
  have hι : Function.Injective ι := FocalFusion.ambientHom_injective n _ e
  have hs : ¬ IsConj (ι (s n)) (ι (z n)) := centralizer_s_not_fused n hn S f
  have hq : IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3)))) :=
    centralizer_order_four_fusion n hn S f hG
  rw [← FocalFusion.supplied_fusionClosure_eq_derived n P e,
    FocalFusion.fusionClosure_eq_quaternion n hn ι hι hs hq]
  exact map_quaternionSubgroup n e

theorem centralizer_derived_index [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    ((commutator (involutionCentralizer n S f)).subgroupOf
      (centralizerSylow n hn S f)).index = 2 := by
  rw [centralizer_derived_eq_quaternion n hn S f hG]
  exact (supplied_index_two n hn (centralizerCoordinates n hn S f)
    (sylowQuaternion n hn S f)).mpr (Or.inr (Or.inr rfl))

theorem centralizer_derived_inf [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    (centralizerSylow n hn S f : Subgroup (involutionCentralizer n S f)) ⊓
      commutator (involutionCentralizer n S f) = centralizerQuaternion n hn S f := by
  have h := congrArg
    (Subgroup.map (centralizerSylow n hn S f :
      Subgroup (involutionCentralizer n S f)).subtype)
    (centralizer_derived_eq_quaternion n hn S f hG)
  rw [Subgroup.subgroupOf_map_subtype, sylowQuaternion_map, inf_comm] at h
  exact h

@[expose] def oddResidual (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : Subgroup (involutionCentralizer n S f) :=
  primeResidual 2 (involutionCentralizer n S f)

instance oddResidual_characteristic (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : (oddResidual n S f).Characteristic :=
  primeResidual_characteristic 2 _

instance oddResidual_normal (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : (oddResidual n S f).Normal := inferInstance

theorem oddResidual_eq_odd_order_closure (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : oddResidual n S f =
    Subgroup.closure {x : involutionCentralizer n S f | Odd (orderOf x)} := by
  rw [oddResidual, primeResidual]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, ← even_iff_two_dvd, Nat.not_even_iff_odd]

theorem oddResidual_index [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) : (oddResidual n S f).index = 2 :=
  primeResidual_index (centralizerSylow n hn S f) (centralizer_derived_index n hn S f hG)

theorem oddResidual_inf_sylow [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    (centralizerSylow n hn S f : Subgroup (involutionCentralizer n S f)) ⊓
      oddResidual n S f = centralizerQuaternion n hn S f := by
  rw [oddResidual, sylow_inf_primeResidual_eq_commutator
    (centralizerSylow n hn S f) (centralizer_derived_index n hn S f hG)]
  exact centralizer_derived_inf n hn S f hG

theorem centralizerQuaternion_le_oddResidual [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    centralizerQuaternion n hn S f ≤ oddResidual n S f := by
  rw [← oddResidual_inf_sylow n hn S f hG]
  exact inf_le_right

theorem oddResidual_sylow [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    ∃ T : Sylow 2 (oddResidual n S f), (T : Subgroup (oddResidual n S f)) =
      (centralizerQuaternion n hn S f).subgroupOf (oddResidual n S f) := by
  obtain ⟨T, hT⟩ := sylow_inf_primeResidual (centralizerSylow n hn S f)
    (centralizer_derived_index n hn S f hG)
  refine ⟨T, ?_⟩
  have hi : (centralizerSylow n hn S f : Subgroup (involutionCentralizer n S f)) ⊓
      primeResidual 2 (involutionCentralizer n S f) = centralizerQuaternion n hn S f :=
    oddResidual_inf_sylow n hn S f hG
  rw [hi] at hT
  exact hT

theorem oddResidual_unique_index_two [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2)
    (H : Subgroup (involutionCentralizer n S f)) (hH : H.index = 2) : H = oddResidual n S f :=
  primeResidual_unique_normal_index (centralizerSylow n hn S f)
    (centralizer_derived_index n hn S f hG) H (H.normal_of_index_eq_two hH) hH

theorem oddResidual_hom_eq_one (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) {P : Type*} [Group P]
    (hP : IsPGroup 2 P) (φ : oddResidual n S f →* P) : φ = 1 :=
  primeResidual_hom_eq_one hP φ

@[expose] noncomputable def centralizerQuaternionEquiv (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    QuaternionGroup (2 ^ (n - 3)) ≃* centralizerQuaternion n hn S f :=
  (suppliedQuaternionEquiv n hn (centralizerCoordinates n hn S f)).trans
    (((sylowQuaternion n hn S f).equivMapOfInjective
      (centralizerSylow n hn S f : Subgroup (involutionCentralizer n S f)).subtype
      Subtype.val_injective).trans (MulEquiv.subgroupCongr (sylowQuaternion_map n hn S f)))

theorem centralizerQuaternionEquiv_coe (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) (g : QuaternionGroup (2 ^ (n - 3))) :
    (centralizerQuaternionEquiv n hn S f g : involutionCentralizer n S f) =
      ((suppliedQuaternionEquiv n hn (centralizerCoordinates n hn S f) g :
        centralizerSylow n hn S f) : involutionCentralizer n S f) := by
  rfl

theorem centralizerQuaternionEquiv_rotation (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    (centralizerQuaternionEquiv n hn S f (QuaternionGroup.a 1) : involutionCentralizer n S f) =
      (centralizerCoordinates n hn S f (r n) : involutionCentralizer n S f) ^ 2 := by
  rw [centralizerQuaternionEquiv_coe, suppliedQuaternionEquiv_rotation]
  rfl

theorem centralizerQuaternionEquiv_generator (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    (centralizerQuaternionEquiv n hn S f (QuaternionGroup.xa 0) : involutionCentralizer n S f) =
      (centralizerCoordinates n hn S f (r n) : involutionCentralizer n S f) *
        (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f) := by
  rw [centralizerQuaternionEquiv_coe, suppliedQuaternionEquiv_generator]
  rfl

theorem centralInvolution_mem_quaternion (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    centralInvolution n S f ∈ centralizerQuaternion n hn S f := by
  have hz : centralizerCoordinates n hn S f (z n) ∈ sylowQuaternion n hn S f := by
    change centralizerCoordinates n hn S f (z n) ∈ Subgroup.closure
      {centralizerCoordinates n hn S f (r n) ^ 2,
        centralizerCoordinates n hn S f (r n) * centralizerCoordinates n hn S f (s n)}
    rw [← map_quaternionSubgroup n (centralizerCoordinates n hn S f), mem_map_equiv_iff]
    exact z_mem_quaternionSubgroup n (by omega)
  rw [← sylowQuaternion_map n hn S f]
  exact ⟨centralizerCoordinates n hn S f (z n), hz, centralizerCoordinates_z n hn S f⟩

theorem centralInvolution_order (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : orderOf (centralInvolution n S f) = 2 := by
  rw [← centralizerCoordinates_z n hn S f]
  change orderOf ((centralizerSylow n hn S f :
    Subgroup (involutionCentralizer n S f)).subtype
      (centralizerCoordinates n hn S f (z n))) = 2
  rw [orderOf_injective _ Subtype.val_injective, equiv_orderOf]
  exact orderOf_z n (by omega)

theorem quaternion_unique_involution (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (x : involutionCentralizer n S f)
    (hxQ : x ∈ centralizerQuaternion n hn S f) (hx : orderOf x = 2) :
    x = centralInvolution n S f := by
  rw [← sylowQuaternion_map n hn S f] at hxQ
  obtain ⟨a, ha, rfl⟩ := hxQ
  have hoa : orderOf a = 2 := by
    rw [← orderOf_injective (centralizerSylow n hn S f :
      Subgroup (involutionCentralizer n S f)).subtype Subtype.val_injective]
    exact hx
  have hz := supplied_quaternion_unique_involution n hn
    (centralizerCoordinates n hn S f) a ha hoa
  rw [modulus_div_two n (by omega), ← map_pow] at hz
  change a = centralizerCoordinates n hn S f (z n) at hz
  rw [hz]
  exact centralizerCoordinates_z n hn S f

theorem centralInvolution_mem_oddResidual [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    centralInvolution n S f ∈ oddResidual n S f :=
  centralizerQuaternion_le_oddResidual n hn S f hG (centralInvolution_mem_quaternion n hn S f)

theorem s_not_mem_oddResidual [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f) ∉ oddResidual n S f := by
  intro hs
  have hP : (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f) ∈
      (centralizerSylow n hn S f : Subgroup (involutionCentralizer n S f)) ⊓ oddResidual n S f :=
    ⟨(centralizerCoordinates n hn S f (s n)).property, hs⟩
  rw [oddResidual_inf_sylow n hn S f hG, ← sylowQuaternion_map n hn S f] at hP
  obtain ⟨a, ha, he⟩ := hP
  have he' : a = centralizerCoordinates n hn S f (s n) := Subtype.ext he
  rw [he'] at ha
  change centralizerCoordinates n hn S f (s n) ∈ Subgroup.closure
    {centralizerCoordinates n hn S f (r n) ^ 2,
      centralizerCoordinates n hn S f (r n) * centralizerCoordinates n hn S f (s n)} at ha
  rw [← map_quaternionSubgroup n (centralizerCoordinates n hn S f), mem_map_equiv_iff] at ha
  exact s_not_mem_quaternionSubgroup n (by omega) ha

theorem s_order (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    orderOf (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f) = 2 := by
  change orderOf ((centralizerSylow n hn S f :
    Subgroup (involutionCentralizer n S f)).subtype
      (centralizerCoordinates n hn S f (s n))) = 2
  rw [orderOf_injective (centralizerSylow n hn S f :
    Subgroup (involutionCentralizer n S f)).subtype Subtype.val_injective, equiv_orderOf]
  exact orderOf_s n (by omega)

theorem sup_zpowers_of_index_two {H : Type*} [Group H] (K : Subgroup H)
    (hK : K.index = 2) (s : H) (hs : s ∉ K) : K ⊔ Subgroup.zpowers s = ⊤ := by
  apply top_unique
  intro x _
  by_cases hx : x ∈ K
  · exact (show K ≤ K ⊔ Subgroup.zpowers s from le_sup_left) hx
  · have hxs : x * s⁻¹ ∈ K := (Subgroup.mul_mem_iff_of_index_two hK).mpr
      (iff_of_false hx (by simpa only [Subgroup.inv_mem_iff] using hs))
    have h : (x * s⁻¹) * s ∈ K ⊔ Subgroup.zpowers s :=
      (K ⊔ Subgroup.zpowers s).mul_mem
        ((show K ≤ K ⊔ Subgroup.zpowers s from le_sup_left) hxs)
        ((show Subgroup.zpowers s ≤ K ⊔ Subgroup.zpowers s from le_sup_right)
          (Subgroup.mem_zpowers s))
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

theorem inf_zpowers_of_order_two {H : Type*} [Group H] (K : Subgroup H)
    (s : H) (hs : s ∉ K) (ho : orderOf s = 2) : K ⊓ Subgroup.zpowers s = ⊥ := by
  classical
  apply le_antisymm
  · intro x hx
    have hfin : IsOfFinOrder s := orderOf_pos_iff.mp (by omega)
    have hmem := hfin.mem_zpowers_iff_mem_range_orderOf.mp hx.2
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_range] at hi
    have hic : i = 0 ∨ i = 1 := by rw [ho] at hi; omega
    rcases hic with rfl | rfl
    · simpa only [pow_zero, Subgroup.mem_bot] using he.symm
    · simp only [pow_one] at he
      exact (hs (he.symm ▸ hx.1)).elim
  · exact bot_le

theorem oddResidual_split [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    oddResidual n S f ⊔ Subgroup.zpowers
      (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f) = ⊤ ∧
    oddResidual n S f ⊓ Subgroup.zpowers
      (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f) = ⊥ :=
  ⟨sup_zpowers_of_index_two _ (oddResidual_index n hn S f hG) _
      (s_not_mem_oddResidual n hn S f hG),
    inf_zpowers_of_order_two _ _ (s_not_mem_oddResidual n hn S f hG) (s_order n hn S f)⟩

theorem oddResidual_unique_involution [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) (x : oddResidual n S f)
    (hx : orderOf x = 2) : (x : involutionCentralizer n S f) = centralInvolution n S f := by
  obtain ⟨T, hT⟩ := oddResidual_sylow n hn S f hG
  have htwo : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨y, hxy⟩ := InvolutionFusion.exists_ambient_conjugate_mem_sylow T x htwo
  have hyQ : ((y : oddResidual n S f) : involutionCentralizer n S f) ∈
      centralizerQuaternion n hn S f := by
    have hym := y.property
    change (y : oddResidual n S f) ∈ (T : Subgroup (oddResidual n S f)) at hym
    rw [hT] at hym
    exact hym
  have hC := (oddResidual n S f).subtype.map_isConj hxy
  change IsConj (x : involutionCentralizer n S f)
    ((y : oddResidual n S f) : involutionCentralizer n S f) at hC
  have hoy : orderOf ((y : oddResidual n S f) : involutionCentralizer n S f) = 2 := by
    have ho := orderOf_injective (oddResidual n S f).subtype Subtype.val_injective x
    have he := conjugate_orderOf_eq hC
    exact he.symm.trans (ho.trans hx)
  have hy := quaternion_unique_involution n hn S f _ hyQ hoy
  rw [hy] at hC
  exact (conjugate_to_central_iff (centralInvolution_mem_center n S f)).mp hC

theorem oddResidual_involution_iff [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) (x : oddResidual n S f) :
    orderOf x = 2 ↔ (x : involutionCentralizer n S f) = centralInvolution n S f := by
  constructor
  · exact oddResidual_unique_involution n hn S f hG x
  · intro h
    have ho := orderOf_injective (oddResidual n S f).subtype Subtype.val_injective x
    change orderOf (x : involutionCentralizer n S f) = orderOf x at ho
    rw [h, centralInvolution_order n hn S f] at ho
    exact ho.symm

theorem oddResidual_factorization [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) (x : involutionCentralizer n S f) :
    ∃ k : oddResidual n S f,
      ∃ u : Subgroup.zpowers
        (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f),
        (k : involutionCentralizer n S f) * u = x := by
  have hx : x ∈ oddResidual n S f ⊔ Subgroup.zpowers
      (centralizerCoordinates n hn S f (s n) : involutionCentralizer n S f) := by
    rw [(oddResidual_split n hn S f hG).1]
    trivial
  obtain ⟨k, hk, u, hu, hku⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  exact ⟨⟨k, hk⟩, ⟨u, hu⟩, hku⟩

theorem centralizerQuaternion_ambient_map (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    (centralizerQuaternion n hn S f).map (involutionCentralizer n S f).subtype =
      Subgroup.closure {((f (r n) ^ 2 : S) : G), ((f (r n) * f (s n) : S) : G)} := by
  rw [centralizerQuaternion, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, map_pow, map_mul]
  rfl

theorem centered_quaternion_residual [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    let C := involutionCentralizer n S f
    let P := centralizerSylow n hn S f
    let e := centralizerCoordinates n hn S f
    let Q := centralizerQuaternion n hn S f
    let K := oddResidual n S f
    let t := centralInvolution n S f
    let s := (e (CFSG.Semidihedral.s n) : C)
    (S : Subgroup G) ≤ C ∧
    (P : Subgroup C) = (S : Subgroup G).subgroupOf C ∧
    (P : Subgroup C) ⊓ commutator C = Q ∧
    K = Subgroup.closure {x : C | Odd (orderOf x)} ∧ K.Characteristic ∧ K.index = 2 ∧
    (P : Subgroup C) ⊓ K = Q ∧
    (∃ T : Sylow 2 K, (T : Subgroup K) = Q.subgroupOf K) ∧
    (∃ q : QuaternionGroup (2 ^ (n - 3)) ≃* Q,
      (q (QuaternionGroup.a 1) : C) = (e (r n) : C) ^ 2 ∧
      (q (QuaternionGroup.xa 0) : C) = (e (r n) : C) * (e (CFSG.Semidihedral.s n) : C)) ∧
    t ∈ K ∧ orderOf t = 2 ∧ (∀ x : K, orderOf x = 2 ↔ (x : C) = t) ∧
    K ⊔ Subgroup.zpowers s = ⊤ ∧ K ⊓ Subgroup.zpowers s = ⊥ ∧
    (∀ x : C, ∃ k : K, ∃ u : Subgroup.zpowers s, (k : C) * u = x) ∧
    (∀ H : Subgroup C, H.index = 2 → H = K) ∧
    (∀ (A : Type*) [Group A] [Finite A], IsPGroup 2 A → ∀ φ : K →* A, φ = 1) := by
  dsimp only
  refine ⟨sylow_le_involutionCentralizer n hn S f, rfl,
    centralizer_derived_inf n hn S f hG, oddResidual_eq_odd_order_closure n S f,
    oddResidual_characteristic n S f, oddResidual_index n hn S f hG,
    oddResidual_inf_sylow n hn S f hG, oddResidual_sylow n hn S f hG,
    ⟨centralizerQuaternionEquiv n hn S f, centralizerQuaternionEquiv_rotation n hn S f,
      centralizerQuaternionEquiv_generator n hn S f⟩,
    centralInvolution_mem_oddResidual n hn S f hG, centralInvolution_order n hn S f,
    oddResidual_involution_iff n hn S f hG,
    (oddResidual_split n hn S f hG).1, (oddResidual_split n hn S f hG).2,
    oddResidual_factorization n hn S f hG,
    oddResidual_unique_index_two n hn S f hG, ?_⟩
  intro A _ _ hA φ
  exact oddResidual_hom_eq_one n S f hA φ

theorem involution_centralizer_quaternion_residual [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S₀ : Sylow 2 G) (f₀ : SemidihedralGroup n ≃* S₀)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    ∀ t : G, orderOf t = 2 →
      (∃ (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S),
        ((f (r n) ^ (2 ^ (n - 2)) : S) : G) = t) ∧
      (∀ (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S),
        ((f (r n) ^ (2 ^ (n - 2)) : S) : G) = t →
        let C := involutionCentralizer n S f
        let P := centralizerSylow n hn S f
        let e := centralizerCoordinates n hn S f
        let Q := centralizerQuaternion n hn S f
        let K := oddResidual n S f
        let tC := centralInvolution n S f
        let s := (e (CFSG.Semidihedral.s n) : C)
        C = Subgroup.centralizer {t} ∧ (tC : G) = t ∧
        (S : Subgroup G) ≤ C ∧ (P : Subgroup C) = (S : Subgroup G).subgroupOf C ∧
        (P : Subgroup C) ⊓ commutator C = Q ∧
        K = Subgroup.closure {x : C | Odd (orderOf x)} ∧ K.Characteristic ∧ K.index = 2 ∧
        (P : Subgroup C) ⊓ K = Q ∧
        (∃ T : Sylow 2 K, (T : Subgroup K) = Q.subgroupOf K) ∧
        (∃ q : QuaternionGroup (2 ^ (n - 3)) ≃* Q,
          (q (QuaternionGroup.a 1) : C) = (e (r n) : C) ^ 2 ∧
          (q (QuaternionGroup.xa 0) : C) =
            (e (r n) : C) * (e (CFSG.Semidihedral.s n) : C)) ∧
        tC ∈ K ∧ orderOf tC = 2 ∧ (∀ x : K, orderOf x = 2 ↔ (x : C) = tC) ∧
        K ⊔ Subgroup.zpowers s = ⊤ ∧ K ⊓ Subgroup.zpowers s = ⊥ ∧
        (∀ x : C, ∃ k : K, ∃ u : Subgroup.zpowers s, (k : C) * u = x) ∧
        (∀ H : Subgroup C, H.index = 2 → H = K) ∧
        (∀ (A : Type*) [Group A] [Finite A], IsPGroup 2 A → ∀ φ : K →* A, φ = 1)) := by
  intro t ht
  obtain ⟨S, f, hz, hr⟩ :=
    (InvolutionFusion.involution_centered_sylow_existence n hn S₀ f₀ hG t ht).2
  refine ⟨⟨S, f, hr⟩, ?_⟩
  intro S f hcenter
  have hz : centeredInvolution n S f = t := by
    change (f (z n) : G) = t
    simpa only [z, half, map_pow] using hcenter
  refine ⟨?_, hz, centered_quaternion_residual n hn S f hG⟩
  change Subgroup.centralizer {centeredInvolution n S f} = Subgroup.centralizer {t}
  rw [hz]

end CFSG.Semidihedral.CentralizerResidual
