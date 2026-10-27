module

public import CFSG.CharacterTheory.Wreathed.BaseNormalizer
public import CFSG.CharacterTheory.Wreathed.CentricClassification
public import CFSG.GroupTheory.NormalizerSylow

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u

variable {G : Type u} [Group G]

@[expose] def modelV {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) : Subgroup G :=
  (Original.V m).map (wreathModelHom S e)

@[expose] def modelVEquiv {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Original.V m ≃* modelV S e :=
  (Original.V m).equivMapOfInjective (wreathModelHom S e)
    (wreathModelHom_injective S e)

theorem modelV_le_sylow {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    modelV S e ≤ (S : Subgroup G) := by
  rw [← wreathModelHom_range S e]
  exact Subgroup.map_le_range (f := wreathModelHom S e) (H := Original.V m)

theorem model_local_normalizer_card {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (P : Subgroup G) (hPS : P ≤ (S : Subgroup G)) :
    Nat.card ((Subgroup.normalizer (P : Set G)).subgroupOf (S : Subgroup G)) =
      Nat.card (Subgroup.normalizer
        ((P.comap (wreathModelHom S e)) : Set (Wreath m))) := by
  have hPrange : P ≤ (wreathModelHom S e).range := by
    rw [wreathModelHom_range]
    exact hPS
  have hmap : (Subgroup.normalizer
      ((P.comap (wreathModelHom S e)) : Set (Wreath m))).map (wreathModelHom S e) =
      (S : Subgroup G) ⊓ Subgroup.normalizer (P : Set G) := by
    rw [← Subgroup.comap_normalizer_eq_of_le_range hPrange,
      Subgroup.map_comap_eq, wreathModelHom_range]
  rw [← Subgroup.card_map_of_injective (S : Subgroup G).subtype_injective,
    Subgroup.subgroupOf_map_subtype, inf_comm,
    ← hmap, Subgroup.card_map_of_injective (wreathModelHom_injective S e)]

theorem model_v_copy_local_normalizer_card (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (P : Subgroup G) (hPS : P ≤ (S : Subgroup G))
    (equiv : P ≃* modelV S e) :
    Nat.card ((Subgroup.normalizer (P : Set G)).subgroupOf (S : Subgroup G)) =
      8 * 2 ^ n := by
  have hPrange : P ≤ (wreathModelHom S e).range := by
    rw [wreathModelHom_range]
    exact hPS
  have hmap := Subgroup.map_comap_eq_self hPrange
  let ep : P.comap (wreathModelHom S e) ≃* P :=
    ((P.comap (wreathModelHom S e)).equivMapOfInjective (wreathModelHom S e)
      (wreathModelHom_injective S e)).trans (MulEquiv.subgroupCongr hmap)
  rw [model_local_normalizer_card S e P hPS]
  exact (wreath_centric_odd_automorphism_subgroups n hn).copies_normalizer
    (P.comap (wreathModelHom S e)) ⟨ep.trans (equiv.trans (modelVEquiv S e).symm)⟩

theorem exists_modelVNormalizerSylow [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ∃ T : Sylow 2 (Subgroup.normalizer (modelV S e : Set G)),
      (T : Subgroup (Subgroup.normalizer (modelV S e : Set G))) =
        (S : Subgroup G).subgroupOf (Subgroup.normalizer (modelV S e : Set G)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply CFSG.GorensteinWalter.exists_sylow_normalizer_of_card_max S (modelV S e)
    (modelV_le_sylow S e)
  intro P hPS ⟨equiv⟩
  rw [model_v_copy_local_normalizer_card n hn S e P hPS equiv,
    model_v_copy_local_normalizer_card n hn S e (modelV S e)
      (modelV_le_sylow S e) (MulEquiv.refl _)]

@[expose] def modelVNormalizerSylow [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Sylow 2 (Subgroup.normalizer (modelV S e : Set G)) :=
  (exists_modelVNormalizerSylow n hn S e).choose

theorem modelVNormalizerSylow_coe [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelVNormalizerSylow n hn S e :
      Subgroup (Subgroup.normalizer (modelV S e : Set G))) =
        (S : Subgroup G).subgroupOf (Subgroup.normalizer (modelV S e : Set G)) :=
  (exists_modelVNormalizerSylow n hn S e).choose_spec

@[expose] def modelVAction {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Subgroup.normalizer (modelV S e : Set G) →* MulAut (Original.V m) :=
  (MulAut.congr (modelVEquiv S e).symm).toMonoidHom.comp
    (modelV S e).normalizerMonoidHom

theorem modelVAction_coe {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (g : Subgroup.normalizer (modelV S e : Set G)) (v : Original.V m) :
    wreathModelHom S e (modelVAction S e g v).val =
      g.val * wreathModelHom S e v.val * g.val⁻¹ := by
  change (((modelVEquiv S e) (modelVAction S e g v) : modelV S e) : G) = _
  change (((modelVEquiv S e)
    ((modelVEquiv S e).symm ((modelV S e).normalizerMonoidHom g
      ((modelVEquiv S e) v))) : modelV S e) : G) = _
  rw [MulEquiv.apply_symm_apply]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

@[expose] def modelVCenterAction {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Subgroup.normalizer (modelV S e : Set G) →* MulAut (Subgroup.center (Original.V m)) :=
  (CFSG.FiveTransitive.CharacteristicAutomorphism.restrict
    (Subgroup.center (Original.V m))).comp (modelVAction S e)

theorem modelVAction_sylow_fixes_center (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) (hg : g.val ∈ (S : Subgroup G))
    (v : Original.V (2 ^ n)) (hv : v ∈ Subgroup.center (Original.V (2 ^ n))) :
    modelVAction S e g v = v := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  have hcentral : v.val ∈ Subgroup.center (Wreath (2 ^ n)) := by
    rw [hstructure.center, ← hstructure.central_product_center]
    exact ⟨v, hv, rfl⟩
  let s : S := ⟨g.val, hg⟩
  have hfs : wreathModelHom S e (e s) = g.val :=
    congrArg Subtype.val (e.symm_apply_apply s)
  have hcomm : g.val * wreathModelHom S e v.val =
      wreathModelHom S e v.val * g.val := by
    have h := congrArg (wreathModelHom S e) (Subgroup.mem_center_iff.mp hcentral (e s))
    rwa [map_mul, map_mul, hfs] at h
  apply Subtype.ext
  apply wreathModelHom_injective S e
  rw [modelVAction_coe, hcomm]
  group

theorem original_v_center_automorphism_isPGroup (n : ℕ) (hn : 2 ≤ n) :
    IsPGroup 2 (MulAut (Subgroup.center (Original.V (2 ^ n)))) := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  have hnonabelian := original_v_is_nonabelian n hn
  have hcenter : Subgroup.center (Wreath (2 ^ n)) ≤ Original.V (2 ^ n) := by
    rw [hstructure.center, hstructure.central_product]
    exact le_sup_left
  let : IsCyclic (Subgroup.center (Original.V (2 ^ n))) :=
    nonabelian_subgroup_center_isCyclic _
      (one_lt_pow₀ (by decide) (by omega)) (Original.V (2 ^ n)) hnonabelian hcenter
  exact CFSG.TwoRankLowerBound.Helpers.cyclic_two_group_automorphisms_isPGroup _
    (((wreath_isPGroup n).to_subgroup (Original.V (2 ^ n))).to_subgroup
      (Subgroup.center (Original.V (2 ^ n))))

theorem modelVCenterAction_eq_one [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G)) :
    modelVCenterAction S e g = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply CFSG.GorensteinWalter.hom_to_pGroup_eq_one_of_sylow
    (original_v_center_automorphism_isPGroup n hn) (modelVCenterAction S e)
    (modelVNormalizerSylow n hn S e) ?_ g
  intro s
  have hs : s.val.val ∈ (S : Subgroup G) := by
    have h := s.property
    change s.val ∈ (modelVNormalizerSylow n hn S e :
      Subgroup (Subgroup.normalizer (modelV S e : Set G))) at h
    rw [modelVNormalizerSylow_coe] at h
    exact h
  apply MulEquiv.ext
  intro c
  apply Subtype.ext
  exact modelVAction_sylow_fixes_center n hn S e s.val hs c.val c.property

theorem modelVAction_fixes_center [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G))
    (v : Original.V (2 ^ n)) (hv : v ∈ Subgroup.center (Original.V (2 ^ n))) :
    modelVAction S e g v = v := by
  have h := DFunLike.congr_fun (modelVCenterAction_eq_one n hn S e g) ⟨v, hv⟩
  exact congrArg Subtype.val h

theorem modelVNormalizer_centralizes_original_center [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : G) (hg : g ∈ Subgroup.normalizer (modelV S e : Set G))
    (v : Wreath (2 ^ n)) (hv : v ∈ Original.Z (2 ^ n)) :
    g * wreathModelHom S e v * g⁻¹ = wreathModelHom S e v := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  rw [← hstructure.central_product_center] at hv
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
  have h := congrArg (fun v : Original.V (2 ^ n) => wreathModelHom S e v.val)
    (modelVAction_fixes_center n hn S e ⟨g, hg⟩ w hw)
  rw [modelVAction_coe] at h
  exact h

theorem modelVNormalizer_le_center_centralizer [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelV S e : Set G) ≤
      Subgroup.centralizer (((Original.Z (2 ^ n)).map (wreathModelHom S e) : Subgroup G) :
        Set G) := by
  intro g hg
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨v, hv, rfl⟩
  exact (mul_inv_eq_iff_eq_mul.mp
    (modelVNormalizer_centralizes_original_center n hn S e g hg v hv)).symm

end CFSG.Wreathed
