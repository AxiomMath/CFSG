module

public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamiliesLocal
public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionGenerators
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerFamiliesConstruction

public noncomputable section

namespace CFSG.Wreathed.CompatibleFamilies

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.BaseFourCentralizerStructure

universe u

variable {G : Type u} [Group G]

theorem extend_conj_of_mem_closure {N T : Subgroup G} {lam : N →* ℂˣ} {X : Set G}
    (hX : X ⊆ Subgroup.normalizer (T : Set G))
    (hXinv : ∀ x ∈ X, ∀ c ∈ Subgroup.centralizer (T : Set G),
      extend N lam (x⁻¹ * c * x) = extend N lam c)
    {h : G} (hh : h ∈ Subgroup.closure X) :
    ∀ c ∈ Subgroup.centralizer (T : Set G), extend N lam (h⁻¹ * c * h) = extend N lam c := by
  have hle : Subgroup.closure X ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.closure_le _).mpr hX
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hXinv x hx
  | one =>
    intro c _
    rw [inv_one, one_mul, mul_one]
  | mul x y hx hy ihx ihy =>
    intro c hc
    have hxc := LocalConfig.conj_mem_centralizer (hle hx) hc
    rw [show (x * y)⁻¹ * c * (x * y) = y⁻¹ * (x⁻¹ * c * x) * y by group, ihy _ hxc, ihx c hc]
  | inv x hx ihx =>
    intro c hc
    have hxc : x * c * x⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
      have h := LocalConfig.conj_mem_centralizer (hle (Subgroup.inv_mem _ hx)) hc
      rwa [inv_inv] at h
    have h := ihx _ hxc
    rw [show x⁻¹ * (x * c * x⁻¹) * x = c by group] at h
    rw [inv_inv]
    exact h.symm

variable {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem originalBaseOnFourAction_coe (hn : 1 ≤ n)
    (g : Subgroup.normalizer (modelBase S e : Set G)) (t : modelT n S e) :
    (originalBaseOnFourAction n hn S e g t : G) = (g : G) * t * (g : G)⁻¹ := rfl

variable [Finite G]

theorem eta_properties (hn : 2 ≤ n) {η : G} (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    η ∈ Subgroup.normalizer (Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
      wreathModelHom S e (Original.x2 (2 ^ n))} : Set G) ∧
    ∀ t ∈ Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
        wreathModelHom S e (Original.x2 (2 ^ n))}, t ≠ 1 →
      ∃ j : ℕ, (η ^ j)⁻¹ * t * η ^ j = wreathModelHom S e (Original.x (2 ^ n)) := by
  rw [← modelT_eq_closure S e (by omega)]
  refine ⟨modelBase_normalizer_le_modelT_normalizer n (by omega) S e hη, ?_⟩
  intro t ht ht1
  have hJT : wreathModelHom S e (Original.x (2 ^ n)) ∈ modelT n S e := by
    rw [modelT_eq_closure S e (by omega)]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hJ1 : (⟨_, hJT⟩ : modelT n S e) ≠ 1 := by
    intro h
    exact ne_one_of_orderOf (orderOf_x S e hn) (congrArg Subtype.val h)
  have hcyc := ((sylow_and_base_four_group_centralizer_structure n hn S e).order_three_cycle
    ⟨η, hη⟩ hord ⟨_, hJT⟩ hJ1).2.2.2.2 ⟨t, ht⟩ (fun h => ht1 (congrArg Subtype.val h))
  rcases hcyc with h | h | h
  · exact ⟨0, by simpa using congrArg Subtype.val h⟩
  · refine ⟨1, ?_⟩
    have h' := congrArg Subtype.val h
    rw [originalBaseOnFourAction_coe] at h'
    change t = η * _ * η⁻¹ at h'
    rw [h', pow_one]
    group
  · refine ⟨2, ?_⟩
    have h' := congrArg Subtype.val h
    rw [originalBaseOnFourAction_coe, originalBaseOnFourAction_coe] at h'
    change t = η * (η * _ * η⁻¹) * η⁻¹ at h'
    rw [h']
    group

variable [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
include hnonab

theorem localConfig (hn : 2 ≤ n) {η : G} (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    LocalConfig (wreathModelHom S e (Original.x (2 ^ n)))
      (wreathModelHom S e (Original.x2 (2 ^ n))) η where
  sq := sq_eq_one_of_orderOf (orderOf_x S e hn)
  sq₁ := sq_eq_one_of_orderOf (orderOf_x2 S e hn)
  ne_one := ne_one_of_orderOf (orderOf_x S e hn)
  ne_one₁ := ne_one_of_orderOf (orderOf_x2 S e hn)
  ne := modelHom_x_ne_x2 S e (by omega)
  comm := modelBase_commute S e _ _ (modelHom_x_mem_modelBase S e)
    (modelHom_x2_mem_modelBase S e)
  conj_eq y hy := by
    obtain ⟨c, hc⟩ := isConj_iff.mp
      (all_involutions_conjugate_of_simple_wreathed hnonab n hn S e y _ hy (orderOf_x S e hn))
    exact ⟨c⁻¹, by rw [inv_inv]; exact hc⟩
  conj_eq₁ y hyN hy2 hyJ := exists_centralizer_conj_eq_x2 S e hnonab hn hyN hy2 hyJ
  involution_mem y hy hy2 := mem_closure_of_mem_centralizer S e hn hy hy2
  eta_mem := (eta_properties S e hn hη hord).1
  eta_cycle := (eta_properties S e hn hη hord).2

omit [Finite G] [IsSimpleGroup G] hnonab in
theorem isSpecial_sylow (hn : 2 ≤ n) :
    IsSpecial (wreathModelHom S e (Original.x (2 ^ n)))
      (Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
        wreathModelHom S e (Original.x2 (2 ^ n))}) (S : Subgroup G) := by
  refine Or.inl ⟨⟨modelBase_le_sylow S e (modelHom_x_mem_modelBase S e), ?_⟩, ?_⟩
  · change wreathModelHom S e (Original.x (2 ^ n)) ∈
      Subgroup.centralizer ((S : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h := modelHom_x_central S e hn hg
    calc g * wreathModelHom S e (Original.x (2 ^ n)) =
        g * (g⁻¹ * wreathModelHom S e (Original.x (2 ^ n)) * g) := by rw [h]
      _ = wreathModelHom S e (Original.x (2 ^ n)) * g := by group
  · intro y hy hy2
    have hy' := Subgroup.mem_inf.mp hy
    have hyZ : y ∈ modelCenter S e := by
      rw [← center_map_eq_modelCenter n hn S e]
      refine Subgroup.mem_map.mpr ⟨⟨y, hy'.1⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hy'.2 g g.2
    rw [modelCenter_eq_zpowers] at hyZ
    have hA : orderOf (wreathModelHom S e (Original.a (2 ^ n))) = 2 ^ n := by
      rw [orderOf_injective _ (wreathModelHom_injective S e)]
      exact (wreath_center_involution_and_quaternion_coordinates n hn).generator_orders.2.2.1
    rw [AdaptedBaseFusion.eq_pow_half_of_mem_zpowers (by omega) hA hyZ hy2, ← map_pow,
      ← WreathGenerators.half_eq (by omega)]
    rfl

omit [IsSimpleGroup G] hnonab in
theorem isInvariant_of_generation {J J₁ η W : G} {lam : Subgroup.centralizer {J} →* ℂˣ}
    (P : Sylow 2 (Subgroup.centralizer {J}))
    (hP : ∀ v : Subgroup.centralizer {J}, v ∈ (P : Subgroup (Subgroup.centralizer {J})) →
      (v : G) ∈ (S : Subgroup G))
    (hSN : (S : Subgroup G) ≤ Subgroup.centralizer {J})
    (hgen : Subgroup.normalizer (Subgroup.closure {J, J₁} : Set G) =
      Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) ⊔ Subgroup.closure {W, η})
    (hW : W ∈ (S : Subgroup G))
    (hWT : W ∈ Subgroup.normalizer (Subgroup.closure {J, J₁} : Set G))
    (hηT : η ∈ Subgroup.normalizer (Subgroup.closure {J, J₁} : Set G))
    (hS : ∀ v : Subgroup.centralizer {J}, (v : G) ∈ (S : Subgroup G) → lam v = 1)
    (hC : ∀ c c' : Subgroup.centralizer {J},
      (c : G) ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) →
      (c' : G) = η⁻¹ * c * η → lam c' = lam c) :
    IsInvariant J J₁ lam := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) ≤
      Subgroup.centralizer {J} := LocalConfig.centralizer_le
  refine ⟨?_, ?_⟩
  ·
    intro v hv hv2
    obtain ⟨k, hk⟩ := hv2.exists_card_eq
    have hyp : IsPGroup 2 (Subgroup.zpowers (⟨v, hv⟩ : Subgroup.centralizer {J})) := by
      apply IsPGroup.of_card (n := k)
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers, hk]
    obtain ⟨y', hyy'⟩ :=
      CFSG.Semidihedral.InvolutionFusion.exists_ambient_conjugate_mem_sylow P _ hyp
    obtain ⟨c, hc⟩ := isConj_iff.mp hyy'
    have h1 := hS _ (hP _ y'.2)
    rw [← hc, map_mul, map_mul, mul_comm, ← mul_assoc, map_inv, inv_mul_cancel, one_mul] at h1
    rw [extend_of_mem hv]
    exact h1
  ·
    intro h hh c hc
    rw [hgen, ← Subgroup.closure_eq (Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G)),
      ← Subgroup.closure_union] at hh
    refine extend_conj_of_mem_closure ?_ ?_ hh c hc
    · intro x hx
      rcases hx with hx | hx
      · exact Subgroup.centralizer_le_normalizer _ hx
      · rcases hx with rfl | hx
        · exact hWT
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact hηT
    · intro x hx c' hc'
      rcases hx with hx | hx
      · exact extend_conj (hCN hx) (hCN hc')
      · rcases hx with rfl | hx
        · exact extend_conj (hSN hW) (hCN hc')
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          have hc'' : η⁻¹ * c' * η ∈ Subgroup.centralizer (Subgroup.closure {J, J₁} : Set G) :=
            LocalConfig.conj_mem_centralizer hηT hc'
          rw [extend_of_mem (hCN hc''), extend_of_mem (hCN hc')]
          exact hC ⟨c', hCN hc'⟩ ⟨_, hCN hc''⟩ hc' rfl

omit [IsSimpleGroup G] hnonab in
theorem isInvariant (hn : 2 ≤ n) {η : G} (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3)
    {lam : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))} →* ℂˣ}
    (hS : ∀ v : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))},
      (v : G) ∈ (S : Subgroup G) → lam v = 1)
    (hC : ∀ c c' : Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))},
      (c : G) ∈ Subgroup.centralizer (Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
        wreathModelHom S e (Original.x2 (2 ^ n))} : Set G) →
      (c' : G) = η⁻¹ * c * η → lam c' = lam c) :
    IsInvariant (wreathModelHom S e (Original.x (2 ^ n)))
      (wreathModelHom S e (Original.x2 (2 ^ n))) lam := by
  have hgen := (sylow_and_base_four_group_centralizer_structure n hn S e).order_three_generation
    ⟨η, hη⟩ hord
  rw [modelT_eq_closure S e (by omega)] at hgen
  have hW : wreathModelHom S e (Original.z (2 ^ n)) ∈ (S : Subgroup G) :=
    wreathModelHom_mem S e _
  have hWT := modelBase_normalizer_le_modelT_normalizer n (by omega) S e
    (sylow_le_modelBase_normalizer S e hW)
  rw [modelT_eq_closure S e (by omega)] at hWT
  refine isInvariant_of_generation S (centralizerSylow n hn S e) ?_
    (sylow_le_centralizer_x S e hn) hgen hW hWT (eta_properties S e hn hη hord).1 hS hC
  intro v hv
  have hv' : v ∈ ((centralizerSylow n hn S e : Sylow 2 (involutionCentralizer n S e)) :
      Subgroup (involutionCentralizer n S e)) := hv
  rw [centralizerSylow_coe] at hv'
  exact hv'

end CFSG.Wreathed.CompatibleFamilies
