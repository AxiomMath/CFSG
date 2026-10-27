module

public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionSupport
public import CFSG.CharacterTheory.Wreathed.BrauerWongBaseFusion
public import CFSG.CharacterTheory.Wreathed.BrauerWongMaximalOrder
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer

public noncomputable section

namespace CFSG.Wreathed.OrderThirtyTwo

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.AdaptedBaseFusion
open CFSG.Wreathed.WreathCentralSquare

universe u

variable {G : Type u} [Group G]

theorem orderOf_eq_of_isConj {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, show c * a * c⁻¹ = (MulAut.conj c) a by simp, MulEquiv.orderOf_eq]

variable (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ 2))

theorem root_eq : wreathModelHom S e (originalRoot (2 ^ 2)) =
    wreathModelHom S e (Original.s (2 ^ 2)) * wreathModelHom S e (Original.z (2 ^ 2)) := by
  rw [originalRoot, map_mul]

theorem root_eq_element : wreathModelHom S e (Original.s (2 ^ 2)) *
    wreathModelHom S e (Original.z (2 ^ 2)) = wreathModelHom S e (element (2 ^ 2) 1 0 1) := by
  rw [← root_eq, originalRoot_eq]

theorem root_cube_eq_element : (wreathModelHom S e (Original.s (2 ^ 2)) *
    wreathModelHom S e (Original.z (2 ^ 2))) ^ 3 = wreathModelHom S e (element (2 ^ 2) 2 1 1) := by
  rw [← root_eq, ← map_pow, show (3 : ℕ) = 2 * 1 + 1 from rfl, originalRoot_pow_odd]
  rfl

theorem pow_pow_swap_eq (j k : ℕ) :
    wreathModelHom S e (Original.s (2 ^ 2)) ^ j * wreathModelHom S e (Original.t (2 ^ 2)) ^ k *
      wreathModelHom S e (Original.z (2 ^ 2)) =
        wreathModelHom S e (element (2 ^ 2) (j : ZMod (2 ^ 2)) (k : ZMod (2 ^ 2)) 1) := by
  rw [← map_pow, ← map_pow, ← map_mul, ← map_mul]
  congr 1
  simp only [Original.s, Original.t, Original.z, element_base_pow, element_base_mul,
    nsmul_eq_mul, mul_one, mul_zero, add_zero, zero_add]

theorem orderOf_element_swap {c d : ZMod (2 ^ 2)} (hcd : Odd (c + d).val) :
    orderOf (wreathModelHom S e (element (2 ^ 2) c d 1)) = 2 * 2 ^ 2 := by
  rw [orderOf_injective _ (wreathModelHom_injective S e)]
  exact (element_maximal_order_iff 1 c d 1).mpr ⟨rfl, hcd⟩

theorem orderOf_root : orderOf (wreathModelHom S e (Original.s (2 ^ 2)) *
    wreathModelHom S e (Original.z (2 ^ 2))) = 2 * 2 ^ 2 := by
  rw [root_eq_element]
  exact orderOf_element_swap S e (by decide)

theorem orderOf_root_cube : orderOf ((wreathModelHom S e (Original.s (2 ^ 2)) *
    wreathModelHom S e (Original.z (2 ^ 2))) ^ 3) = 2 * 2 ^ 2 := by
  rw [root_cube_eq_element]
  exact orderOf_element_swap S e (by decide)

theorem isConj_element_swap {c d c' d' : ZMod (2 ^ 2)} (h : c + d = c' + d') :
    IsConj (wreathModelHom S e (element (2 ^ 2) c d 1))
      (wreathModelHom S e (element (2 ^ 2) c' d' 1)) :=
  (wreathModelHom S e).map_isConj ((swap_isConj_iff _ c d c' d').mpr h)

theorem exists_element_swap_of_orderOf {y : G} (hy : y ∈ (S : Subgroup G))
    (hord : orderOf y = 2 * 2 ^ 2) :
    ∃ c d : ZMod (2 ^ 2), Odd (c + d).val ∧ y = wreathModelHom S e (element (2 ^ 2) c d 1) := by
  obtain ⟨w', rfl⟩ := exists_wreathModelHom_eq S e hy
  rw [orderOf_injective _ (wreathModelHom_injective S e)] at hord
  obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv (2 ^ 2)).symm.surjective w'
  change orderOf (element (2 ^ 2) c d f) = _ at hord
  obtain ⟨rfl, hodd⟩ := (element_maximal_order_iff 1 c d f).mp hord
  exact ⟨c, d, hodd, rfl⟩

variable [Finite G]

theorem not_isConj_root_root_cube : ¬ IsConj (wreathModelHom S e (Original.s (2 ^ 2)) *
    wreathModelHom S e (Original.z (2 ^ 2))) ((wreathModelHom S e (Original.s (2 ^ 2)) *
      wreathModelHom S e (Original.z (2 ^ 2))) ^ 3) := by
  intro h
  rw [← root_eq] at h
  have h' := root_pow_isConj_iff S e (le_refl 2) 1 3 ⟨0, rfl⟩ ⟨1, rfl⟩ (by norm_num)
    (by norm_num) (by rwa [pow_one])
  omega

theorem val_odd_cases {c : ZMod (2 ^ 2)} (hc : Odd c.val) : c.val = 1 ∨ c.val = 3 := by
  have hlt : c.val < 4 := ZMod.val_lt c
  obtain ⟨k, hk⟩ := hc
  omega

theorem isConj_root_iff {y : G} (hy : y ∈ (S : Subgroup G)) :
    IsConj (wreathModelHom S e (Original.s (2 ^ 2)) * wreathModelHom S e (Original.z (2 ^ 2))) y ↔
      ∃ j k : ℕ, (j + k) % 4 = 1 ∧ y = wreathModelHom S e (Original.s (2 ^ 2)) ^ j *
        wreathModelHom S e (Original.t (2 ^ 2)) ^ k * wreathModelHom S e (Original.z (2 ^ 2)) := by
  constructor
  · intro hc
    have hord : orderOf y = 2 * 2 ^ 2 := (orderOf_eq_of_isConj hc).symm.trans (orderOf_root S e)
    obtain ⟨c, d, hodd, rfl⟩ := exists_element_swap_of_orderOf S e hy hord
    rcases val_odd_cases hodd with h1 | h3
    · refine ⟨c.val, d.val, ?_, ?_⟩
      · rw [← h1, ZMod.val_add]
        rfl
      · rw [pow_pow_swap_eq, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    · exfalso
      apply not_isConj_root_root_cube S e
      refine hc.trans ?_
      rw [root_cube_eq_element]
      apply isConj_element_swap
      apply ZMod.val_injective
      rw [h3]
      rfl
  · rintro ⟨j, k, hjk, rfl⟩
    rw [pow_pow_swap_eq, root_eq_element]
    apply isConj_element_swap
    rw [← Nat.cast_add, ← ZMod.natCast_mod, show (j + k) % 2 ^ 2 = 1 from hjk]
    rfl

theorem isConj_root_cube_iff {y : G} (hy : y ∈ (S : Subgroup G)) :
    IsConj ((wreathModelHom S e (Original.s (2 ^ 2)) *
      wreathModelHom S e (Original.z (2 ^ 2))) ^ 3) y ↔
      ∃ j k : ℕ, (j + k) % 4 = 3 ∧ y = wreathModelHom S e (Original.s (2 ^ 2)) ^ j *
        wreathModelHom S e (Original.t (2 ^ 2)) ^ k * wreathModelHom S e (Original.z (2 ^ 2)) := by
  constructor
  · intro hc
    have hord : orderOf y = 2 * 2 ^ 2 :=
      (orderOf_eq_of_isConj hc).symm.trans (orderOf_root_cube S e)
    obtain ⟨c, d, hodd, rfl⟩ := exists_element_swap_of_orderOf S e hy hord
    rcases val_odd_cases hodd with h1 | h3
    · exfalso
      apply not_isConj_root_root_cube S e
      refine IsConj.symm (hc.trans ?_)
      rw [root_eq_element]
      apply isConj_element_swap
      apply ZMod.val_injective
      rw [h1]
      rfl
    · refine ⟨c.val, d.val, ?_, ?_⟩
      · rw [← h3, ZMod.val_add]
        rfl
      · rw [pow_pow_swap_eq, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  · rintro ⟨j, k, hjk, rfl⟩
    rw [pow_pow_swap_eq, root_cube_eq_element]
    apply isConj_element_swap
    rw [← Nat.cast_add, ← ZMod.natCast_mod, show (j + k) % 2 ^ 2 = 3 from hjk]
    rfl

omit [Finite G] in
theorem not_isConj_root_base {u : G} (hu : u ∈ modelBase S e) :
    ¬ IsConj (wreathModelHom S e (Original.s (2 ^ 2)) *
        wreathModelHom S e (Original.z (2 ^ 2))) u ∧
      ¬ IsConj ((wreathModelHom S e (Original.s (2 ^ 2)) *
        wreathModelHom S e (Original.z (2 ^ 2))) ^ 3) u := by
  have hlt := orderOf_lt_of_mem_modelBase S e hu
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← orderOf_eq_of_isConj h, orderOf_root] at hlt
    omega
  · rw [← orderOf_eq_of_isConj h, orderOf_root_cube] at hlt
    omega

theorem two_element_cases [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x) (y : G)
    (hy : ∃ k : ℕ, orderOf y = 2 ^ k) :
    (∃ u ∈ modelBase S e, IsConj y u) ∨
      IsConj y (wreathModelHom S e (Original.s (2 ^ 2)) *
        wreathModelHom S e (Original.z (2 ^ 2))) ∨
      IsConj y ((wreathModelHom S e (Original.s (2 ^ 2)) *
        wreathModelHom S e (Original.z (2 ^ 2))) ^ 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hord : orderOf y = 2 * 2 ^ 2
  · right
    obtain ⟨k, hk⟩ := hy
    have hyp : IsPGroup 2 (Subgroup.zpowers y) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    obtain ⟨y', hyy'⟩ :=
      CFSG.Semidihedral.InvolutionFusion.exists_ambient_conjugate_mem_sylow S y hyp
    have hy'o : orderOf (y' : G) = 2 * 2 ^ 2 := (orderOf_eq_of_isConj hyy').symm.trans hord
    obtain ⟨h', hh'odd, -, hh'lt, s', -, hs'eq⟩ :=
      exists_isConj_root_pow S e (le_refl 2) (y' : G) y'.2 hy'o
    have hconj : IsConj (y' : G) (wreathModelHom S e (originalRoot (2 ^ 2)) ^ h') :=
      isConj_iff.mpr ⟨s'⁻¹, by rw [inv_inv]; exact hs'eq⟩
    have hh' : h' = 1 ∨ h' = 3 := by
      obtain ⟨j, rfl⟩ := hh'odd
      have : 2 * j + 1 < 4 := hh'lt
      omega
    rcases hh' with rfl | rfl
    · left
      rw [pow_one, root_eq] at hconj
      exact hyy'.trans hconj
    · right
      rw [root_eq] at hconj
      exact hyy'.trans hconj
  · left
    exact exists_isConj_mem_modelBase S e (le_refl 2)
      (modelVNormalizerQuotient_sym3_of_simple hnonab 2 (le_refl 2) S e) y hy hord

omit [Finite G] in
include e in
theorem card_sylow : Nat.card (S : Subgroup G) = 32 := by
  rw [Nat.card_congr e.toEquiv, (wreath_center_involution_and_quaternion_coordinates 2
    (le_refl 2)).card]
  rfl

omit [Finite G] in
theorem centralizer_inf_sylow_eq {b : G} (hbB : b ∈ modelBase S e)
    (hbZ : b ∉ modelCenter S e) :
    Subgroup.centralizer {b} ⊓ (S : Subgroup G) = modelBase S e := by
  apply le_antisymm
  · rintro g ⟨hgb, hgS⟩
    by_contra hgU
    apply hbZ
    apply mem_modelCenter_of_commute_outside S e (by norm_num) hbB hgS hgU
    exact (Subgroup.mem_centralizer_singleton_iff.mp hgb).symm
  · intro u hu
    refine ⟨?_, modelBase_le_sylow S e hu⟩
    change u ∈ Subgroup.centralizer {b}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact modelBase_commute S e u b hu hbB

theorem card_centralizer_inf_sylow_le {b : G} (hbS : b ∈ (S : Subgroup G))
    (hbZ : b ∉ modelCenter S e) :
    Nat.card (Subgroup.centralizer {b} ⊓ (S : Subgroup G) : Subgroup G) ≤ 16 := by
  have hle : Subgroup.centralizer {b} ⊓ (S : Subgroup G) ≤ (S : Subgroup G) := inf_le_right
  have hne : Subgroup.centralizer {b} ⊓ (S : Subgroup G) ≠ (S : Subgroup G) := by
    intro heq
    apply hbZ
    rw [← center_map_eq_modelCenter 2 (le_refl 2) S e]
    refine Subgroup.mem_map.mpr ⟨⟨b, hbS⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hg : (g : G) ∈ Subgroup.centralizer {b} ⊓ (S : Subgroup G) := by
      rw [heq]
      exact g.2
    exact Subgroup.mem_centralizer_singleton_iff.mp hg.1
  have hdvd := Subgroup.card_dvd_of_le hle
  have hlt := Subgroup.card_lt_of_lt (lt_of_le_of_ne hle hne)
  rw [card_sylow S e] at hdvd hlt
  have hpos : 0 < Nat.card (Subgroup.centralizer {b} ⊓ (S : Subgroup G) : Subgroup G) :=
    Nat.card_pos
  interval_cases (Nat.card (Subgroup.centralizer {b} ⊓ (S : Subgroup G) : Subgroup G)) <;>
    omega

end CFSG.Wreathed.OrderThirtyTwo
