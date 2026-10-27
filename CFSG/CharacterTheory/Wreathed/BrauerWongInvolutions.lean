module

public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

section BaseInvolutions


variable {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem modelHom_x_mul_x2 (hn : 1 ≤ n) :
    wreathModelHom S e (Original.x (2 ^ n)) * wreathModelHom S e (Original.x2 (2 ^ n)) =
      wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) := by
  rw [← map_mul, x_eq_element, x2_eq_element, t_half_eq_element, element_base_mul,
    half_add_half n hn, add_zero]

theorem modelHom_x2_mul_t_half :
    wreathModelHom S e (Original.x2 (2 ^ n)) *
        wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) =
      wreathModelHom S e (Original.x (2 ^ n)) := by
  rw [← map_mul, x_eq_element, x2_eq_element, t_half_eq_element, element_base_mul,
    add_zero, zero_add]

theorem modelHom_swap_conj_x2 :
    (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ * wreathModelHom S e (Original.x2 (2 ^ n)) *
        wreathModelHom S e (Original.z (2 ^ n)) =
      wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) := by
  rw [← map_inv, ← map_mul, ← map_mul, x2_eq_element, swap_conj_base, ← t_half_eq_element]

theorem modelHom_swap_conj_t_half :
    (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ *
        wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) *
        wreathModelHom S e (Original.z (2 ^ n)) =
      wreathModelHom S e (Original.x2 (2 ^ n)) := by
  rw [← map_inv, ← map_mul, ← map_mul, t_half_eq_element, swap_conj_base, ← x2_eq_element]

theorem modelHom_x_ne_x2 (hn : 1 ≤ n) :
    wreathModelHom S e (Original.x (2 ^ n)) ≠ wreathModelHom S e (Original.x2 (2 ^ n)) := by
  intro h
  have h' := wreathModelHom_injective S e h
  rw [x_eq_element, x2_eq_element, element_eq_iff] at h'
  exact half_ne_zero n hn h'.2.1

theorem modelHom_x_ne_t_half (hn : 1 ≤ n) :
    wreathModelHom S e (Original.x (2 ^ n)) ≠
      wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) := by
  intro h
  have h' := wreathModelHom_injective S e h
  rw [x_eq_element, t_half_eq_element, element_eq_iff] at h'
  exact half_ne_zero n hn h'.1

theorem modelHom_x2_ne_t_half (hn : 1 ≤ n) :
    wreathModelHom S e (Original.x2 (2 ^ n)) ≠
      wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) := by
  intro h
  have h' := wreathModelHom_injective S e h
  rw [x2_eq_element, t_half_eq_element, element_eq_iff] at h'
  exact half_ne_zero n hn h'.1

theorem modelHom_x_central {g : G} (hn : 2 ≤ n) (hg : g ∈ (S : Subgroup G)) :
    g⁻¹ * wreathModelHom S e (Original.x (2 ^ n)) * g = wreathModelHom S e (Original.x (2 ^ n)) :=
  modelCenter_conj S e hn ⟨_, (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _, rfl⟩ hg

theorem modelHom_x2_mem_modelBase :
    wreathModelHom S e (Original.x2 (2 ^ n)) ∈ modelBase S e :=
  (mem_modelBase_iff S e _).mpr (by rw [Original.x2_eq, element_mem_base])

theorem modelHom_x_mem_modelBase :
    wreathModelHom S e (Original.x (2 ^ n)) ∈ modelBase S e :=
  (mem_modelBase_iff S e _).mpr (by rw [Original.x_eq, element_mem_base])

end BaseInvolutions

variable [Finite G]

theorem exists_centralizer_conj_swap_eq_x2 {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    ∃ g ∈ Subgroup.centralizer (modelCenter S e : Set G),
      g⁻¹ * wreathModelHom S e (Original.z (2 ^ n)) * g =
        wreathModelHom S e (Original.x2 (2 ^ n)) := by
  obtain ⟨h, hh, hconj⟩ := exists_vNormalizer_swap_eq_x2 n hn S e hsix
  exact ⟨h, modelVNormalizer_le_center_centralizer n hn S e hh, hconj⟩

theorem exists_centralizer_singleton_conj_swap_eq_x2 {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) (c : G) (hc : c ∈ modelCenter S e) :
    ∃ g ∈ Subgroup.centralizer {c},
      g⁻¹ * wreathModelHom S e (Original.z (2 ^ n)) * g =
        wreathModelHom S e (Original.x2 (2 ^ n)) := by
  obtain ⟨g, hg, hconj⟩ := exists_centralizer_conj_swap_eq_x2 hn S e hsix
  refine ⟨g, ?_, hconj⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hg c hc).symm

theorem modelCenter_isolated_of_base_order_two {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    {c : G} (hc : c ∈ modelCenter S e) (g : G) (hg : g⁻¹ * c * g ∈ (S : Subgroup G)) :
    g⁻¹ * c * g = c := by
  obtain ⟨v, hv, rfl⟩ := hc
  let P := Subgroup.zpowers (wreathModelHom S e v)
  have hvP : wreathModelHom S e v ∈ P := Subgroup.mem_zpowers _
  have hPS : P ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr (wreathModelHom_mem S e v)
  have hgP : CFSG.BenderSuzuki.PFchapter1section1.rightConjugate P g ≤ (S : Subgroup G) := by
    rw [CFSG.BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy,
      MonoidHom.map_zpowers]
    apply Subgroup.zpowers_le.mpr
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hg
  obtain ⟨a, hchain, -, hag⟩ := wreathed_fusion_decomposition S n hn e P hPS g hgP
  exact (hag _ hvP).symm.trans
    (wreathedFusionDecomposition_fixes_original_center_of_base_order_two n hn S e hcard P v hv
      hvP hchain)

theorem involution_isConj_cases {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (x : G) (hx : orderOf x = 2) :
    IsConj x (wreathModelHom S e (Original.x (2 ^ n))) ∨
      IsConj x (wreathModelHom S e (Original.x2 (2 ^ n))) ∨
      IsConj x (wreathModelHom S e (Original.z (2 ^ n))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨y, hxy⟩ := CFSG.Semidihedral.InvolutionFusion.exists_ambient_conjugate_mem_sylow S x hxp
  have hyG : orderOf (y : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  have hyorder : orderOf (e y) = 2 :=
    (e.orderOf_eq y).trans ((Subgroup.orderOf_coe y).symm.trans hyG)
  have hyactual : wreathModelHom S e (e y) = (y : G) :=
    congrArg Subtype.val (e.symm_apply_apply y)
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  rcases hstr.involution_classes (e y) hyorder with h | h | h
  · left
    have := (wreathModelHom S e).map_isConj h.symm
    rw [hyactual] at this
    exact hxy.trans this
  · right; left
    have := (wreathModelHom S e).map_isConj h.symm
    rw [hyactual] at this
    exact hxy.trans this
  · right; right
    have := (wreathModelHom S e).map_isConj h.symm
    rw [hyactual] at this
    exact hxy.trans this

theorem isConj_swap_x2 {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    IsConj (wreathModelHom S e (Original.z (2 ^ n)))
      (wreathModelHom S e (Original.x2 (2 ^ n))) := by
  obtain ⟨g, -, hg⟩ := exists_centralizer_conj_swap_eq_x2 hn S e hsix
  exact isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]; exact hg⟩

theorem isConj_x_x2_of_base_sym3 {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3))) :
    IsConj (wreathModelHom S e (Original.x (2 ^ n)))
      (wreathModelHom S e (Original.x2 (2 ^ n))) := by
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  obtain ⟨g, -, hg⟩ := modelBaseNormalizer_involutions_transitive n (by omega) S e hbase
    (wreathModelHom S e (Original.x (2 ^ n))) (wreathModelHom S e (Original.x2 (2 ^ n)))
    ((mem_modelBase_iff S e _).mpr (by rw [Original.x_eq, element_mem_base]))
    ((mem_modelBase_iff S e _).mpr (by rw [Original.x2_eq, element_mem_base]))
    (by rw [orderOf_injective _ (wreathModelHom_injective S e)]; exact hstr.involution_orders.1)
    (by rw [orderOf_injective _ (wreathModelHom_injective S e)]; exact hstr.involution_orders.2.1)
  exact isConj_iff.mpr ⟨g, hg⟩

theorem all_involutions_conjugate_of_base_sym3 {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y := by
  have hJ (w : G) (hw : orderOf w = 2) : IsConj w (wreathModelHom S e (Original.x (2 ^ n))) := by
    have hxx2 := isConj_x_x2_of_base_sym3 hn S e hbase
    rcases involution_isConj_cases hn S e w hw with h | h | h
    · exact h
    · exact h.trans hxx2.symm
    · exact (h.trans (isConj_swap_x2 hn S e hsix)).trans hxx2.symm
  exact (hJ x hx).trans (hJ y hy).symm

theorem conj_class_x_inter_sylow_of_base_order_two {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2) :
    {g : G | IsConj (wreathModelHom S e (Original.x (2 ^ n))) g} ∩ ((S : Subgroup G) : Set G) =
      {wreathModelHom S e (Original.x (2 ^ n))} := by
  have hxZ : wreathModelHom S e (Original.x (2 ^ n)) ∈ modelCenter S e :=
    ⟨_, (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _, rfl⟩
  ext g
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hconj, hgS⟩
    obtain ⟨k, rfl⟩ := isConj_iff.mp hconj
    have h := modelCenter_isolated_of_base_order_two hn S e hcard hxZ k⁻¹ (by simpa using hgS)
    simpa using h
  · rintro rfl
    exact ⟨IsConj.refl _, wreathModelHom_mem S e _⟩

theorem involution_classes_of_base_order_two {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    {c : ConjClasses G | ∃ g : G, orderOf g = 2 ∧ ConjClasses.mk g = c} =
      {ConjClasses.mk (wreathModelHom S e (Original.x (2 ^ n))),
        ConjClasses.mk (wreathModelHom S e (Original.x2 (2 ^ n)))} ∧
    ConjClasses.mk (wreathModelHom S e (Original.x (2 ^ n))) ≠
      ConjClasses.mk (wreathModelHom S e (Original.x2 (2 ^ n))) := by
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  have hne : ConjClasses.mk (wreathModelHom S e (Original.x (2 ^ n))) ≠
      ConjClasses.mk (wreathModelHom S e (Original.x2 (2 ^ n))) := by
    rw [Ne, ConjClasses.mk_eq_mk_iff_isConj]
    intro h
    have hmem : wreathModelHom S e (Original.x2 (2 ^ n)) ∈
        {g : G | IsConj (wreathModelHom S e (Original.x (2 ^ n))) g} ∩
          ((S : Subgroup G) : Set G) := ⟨h, wreathModelHom_mem S e _⟩
    rw [conj_class_x_inter_sylow_of_base_order_two hn S e hcard] at hmem
    exact modelHom_x_ne_x2 S e (by omega) hmem.symm
  refine ⟨?_, hne⟩
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rcases involution_isConj_cases hn S e g hg with h | h | h
    · exact Or.inl (ConjClasses.mk_eq_mk_iff_isConj.mpr h)
    · exact Or.inr (ConjClasses.mk_eq_mk_iff_isConj.mpr h)
    · exact Or.inr (ConjClasses.mk_eq_mk_iff_isConj.mpr (h.trans (isConj_swap_x2 hn S e hsix)))
  · rintro (rfl | rfl)
    · refine ⟨_, ?_, rfl⟩
      rw [orderOf_injective _ (wreathModelHom_injective S e)]
      exact hstr.involution_orders.1
    · refine ⟨_, ?_, rfl⟩
      rw [orderOf_injective _ (wreathModelHom_injective S e)]
      exact hstr.involution_orders.2.1

theorem involution_classes_ncard_of_base_order_two {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    Set.ncard {c : ConjClasses G | ∃ g : G, orderOf g = 2 ∧ ConjClasses.mk g = c} = 2 := by
  obtain ⟨h, hne⟩ := involution_classes_of_base_order_two hn S e hcard hsix
  rw [h]
  exact Set.ncard_pair hne

end CFSG.Wreathed.BrauerWong
