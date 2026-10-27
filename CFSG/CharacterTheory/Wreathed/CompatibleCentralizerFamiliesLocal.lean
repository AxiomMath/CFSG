module

public import CFSG.CharacterTheory.Wreathed.BaseFourCentralizerStructure
public import CFSG.CharacterTheory.Wreathed.BrauerWongInvolutions

public noncomputable section

namespace CFSG.Wreathed.CompatibleFamilies

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.BaseFourCentralizerStructure

universe u

variable {G : Type u} [Group G] {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem modelT_eq_closure (hn : 1 ≤ n) :
    modelT n S e = Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
      wreathModelHom S e (Original.x2 (2 ^ n))} := by
  rw [modelT_eq_actual_generated, ← map_pow, ← map_pow]
  change Subgroup.closure {wreathModelHom S e (Original.x2 (2 ^ n)),
    wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2))} = _
  have h1 := modelHom_x_mul_x2 S e hn
  have h2 := modelHom_x2_mul_t_half S e
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz <;> rw [hz]
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · rw [← h1]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · rw [Subgroup.closure_le]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz <;> rw [hz]
    · rw [← h2]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem orderOf_x (hn : 2 ≤ n) : orderOf (wreathModelHom S e (Original.x (2 ^ n))) = 2 := by
  rw [orderOf_injective _ (wreathModelHom_injective S e)]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1

theorem orderOf_x2 (hn : 2 ≤ n) : orderOf (wreathModelHom S e (Original.x2 (2 ^ n))) = 2 := by
  rw [orderOf_injective _ (wreathModelHom_injective S e)]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.2.1

theorem sq_eq_one_of_orderOf {y : G} (hy : orderOf y = 2) : y * y = 1 := by
  rw [← pow_two, ← hy]
  exact pow_orderOf_eq_one y

theorem ne_one_of_orderOf {y : G} (hy : orderOf y = 2) : y ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hy
  omega

theorem x_mem_modelCenter :
    wreathModelHom S e (Original.x (2 ^ n)) ∈ modelCenter S e :=
  ⟨_, (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _, rfl⟩

theorem sylow_le_centralizer_x (hn : 2 ≤ n) :
    (S : Subgroup G) ≤ Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))} :=
  sylow_le_involutionCentralizer n hn S e

variable [Finite G]

theorem mem_closure_of_mem_centralizer (hn : 2 ≤ n) {y : G}
    (hy : y ∈ Subgroup.centralizer (Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
      wreathModelHom S e (Original.x2 (2 ^ n))} : Set G)) (hy2 : orderOf y = 2) :
    y ∈ Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
      wreathModelHom S e (Original.x2 (2 ^ n))} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← modelT_eq_closure S e (by omega)] at hy ⊢
  obtain ⟨P, hP⟩ := (sylow_and_base_four_group_centralizer_structure n hn S e).base_sylow
  have hyp : IsPGroup 2 (Subgroup.zpowers
      (⟨y, hy⟩ : Subgroup.centralizer (modelT n S e : Set G))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hy2, pow_one])
  obtain ⟨y', hyy'⟩ := CFSG.Semidihedral.InvolutionFusion.exists_ambient_conjugate_mem_sylow P _ hyp
  obtain ⟨c, hc⟩ := isConj_iff.mp hyy'
  have hval : (c : G) * y * (c : G)⁻¹ =
      ((y' : Subgroup.centralizer (modelT n S e : Set G)) : G) := congrArg Subtype.val hc
  have hy'P0 : (y' : Subgroup.centralizer (modelT n S e : Set G)) ∈
      (P : Subgroup (Subgroup.centralizer (modelT n S e : Set G))) := y'.2
  rw [hP] at hy'P0
  have hy'P : ((y' : Subgroup.centralizer (modelT n S e : Set G)) : G) ∈ modelBase S e := hy'P0
  generalize ((y' : Subgroup.centralizer (modelT n S e : Set G)) : G) = z at hval hy'P
  have hy'2 : orderOf z = 2 := by
    rw [← hval, show (c : G) * y * (c : G)⁻¹ = (MulAut.conj (c : G)) y by simp,
      MulEquiv.orderOf_eq, hy2]
  have hy'T : z ∈ modelT n S e := by
    rw [modelT_eq_closure S e (by omega)]
    have hJT : wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.closure
        {wreathModelHom S e (Original.x (2 ^ n)), wreathModelHom S e (Original.x2 (2 ^ n))} :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hJ₁T : wreathModelHom S e (Original.x2 (2 ^ n)) ∈ Subgroup.closure
        {wreathModelHom S e (Original.x (2 ^ n)), wreathModelHom S e (Original.x2 (2 ^ n))} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rcases modelBase_involution_cases S e (by omega) hy'P hy'2 with h | h | h <;> rw [h]
    · exact hJT
    · exact hJ₁T
    · rw [← modelHom_x_mul_x2 S e (by omega)]
      exact Subgroup.mul_mem _ hJT hJ₁T
  have hcomm := Subgroup.mem_centralizer_iff.mp c.2 _ hy'T
  have hyeq : y = z := by
    calc y = (c : G)⁻¹ * ((c : G) * y * (c : G)⁻¹) * c := by group
      _ = (c : G)⁻¹ * z * c := by rw [hval]
      _ = z := by rw [mul_assoc, hcomm, inv_mul_cancel_left]
  rw [hyeq]
  exact hy'T

omit [Finite G] in
theorem exists_sylow_conj_of_isConj {w w' : Wreath (2 ^ n)} (h : IsConj w w') :
    ∃ d ∈ (S : Subgroup G), d * wreathModelHom S e w * d⁻¹ = wreathModelHom S e w' := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine ⟨wreathModelHom S e c, wreathModelHom_mem S e c, ?_⟩
  rw [← hc, map_mul, map_mul, map_inv]

variable [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
include hnonab

theorem exists_centralizer_conj_eq_x2 (hn : 2 ≤ n) {y : G}
    (hyN : y ∈ Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))})
    (hy2 : orderOf y = 2) (hyJ : y ≠ wreathModelHom S e (Original.x (2 ^ n))) :
    ∃ c ∈ Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))},
      c⁻¹ * y * c = wreathModelHom S e (Original.x2 (2 ^ n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := wreathModelHom S e (Original.x (2 ^ n))
  set N := Subgroup.centralizer {J}
  have hSN : (S : Subgroup G) ≤ N := sylow_le_centralizer_x S e hn
  let P : Sylow 2 N := centralizerSylow n hn S e
  have hyp : IsPGroup 2 (Subgroup.zpowers (⟨y, hyN⟩ : N)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hy2, pow_one])
  obtain ⟨y', hyy'⟩ := CFSG.Semidihedral.InvolutionFusion.exists_ambient_conjugate_mem_sylow P _ hyp
  obtain ⟨c₁, hc₁⟩ := isConj_iff.mp hyy'
  have hval : (c₁ : G) * y * (c₁ : G)⁻¹ = ((y' : N) : G) := congrArg Subtype.val hc₁
  have hy'P0 : (y' : N) ∈ (P : Subgroup N) := y'.2
  rw [show (P : Subgroup N) = (S : Subgroup G).subgroupOf N from
    centralizerSylow_coe n hn S e] at hy'P0
  have hy'P : ((y' : N) : G) ∈ (S : Subgroup G) := hy'P0
  set y'' := ((y' : N) : G)
  have hy''2 : orderOf y'' = 2 := by
    rw [← hval, show (c₁ : G) * y * (c₁ : G)⁻¹ = (MulAut.conj (c₁ : G)) y by simp,
      MulEquiv.orderOf_eq, hy2]
  have hc₁J : (c₁ : G) * J = J * c₁ := Subgroup.mem_centralizer_singleton_iff.mp c₁.2
  have hy''J : y'' ≠ J := by
    intro h
    apply hyJ
    calc y = (c₁ : G)⁻¹ * ((c₁ : G) * y * (c₁ : G)⁻¹) * c₁ := by group
      _ = (c₁ : G)⁻¹ * J * c₁ := by rw [hval, h]
      _ = J := by rw [mul_assoc, ← hc₁J, inv_mul_cancel_left]
  obtain ⟨w', hw'⟩ := exists_wreathModelHom_eq S e hy'P
  have hw'2 : orderOf w' = 2 := by
    rw [← orderOf_injective _ (wreathModelHom_injective S e), hw']
    exact hy''2
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  obtain ⟨c₂, hc₂N, hc₂⟩ :
      ∃ c₂ ∈ N, c₂⁻¹ * y'' * c₂ = wreathModelHom S e (Original.x2 (2 ^ n)) := by
    rcases hstr.involution_classes w' hw'2 with h | h | h
    · exact absurd (by rw [← hw', (hstr.x_class w').mp h]) hy''J
    · obtain ⟨d, hdS, hd⟩ := exists_sylow_conj_of_isConj S e h
      refine ⟨d, hSN hdS, ?_⟩
      rw [← hw', ← hd]
      group
    · obtain ⟨d, hdS, hd⟩ := exists_sylow_conj_of_isConj S e h
      obtain ⟨g, hg, hgW⟩ := exists_centralizer_singleton_conj_swap_eq_x2 hn S e
        (modelVNormalizerQuotient_sym3_of_simple hnonab n hn S e) J (x_mem_modelCenter S e)
      refine ⟨d * g, N.mul_mem (hSN hdS) hg, ?_⟩
      rw [← hw', ← hd, ← hgW]
      group
  refine ⟨(c₁ : G)⁻¹ * c₂, N.mul_mem (N.inv_mem c₁.2) hc₂N, ?_⟩
  rw [← hc₂, ← hval]
  group

end CFSG.Wreathed.CompatibleFamilies
