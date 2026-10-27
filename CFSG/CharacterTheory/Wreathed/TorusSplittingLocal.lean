module

public import CFSG.CharacterTheory.Wreathed.OddFieldFixedTorusDerivedCentralizer
public import CFSG.CharacterTheory.Wreathed.SimpleFusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear
public import CFSG.CharacterTheory.Wreathed.BaseFourCentralizerStructure
public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolutionSupport

public section

open scoped Classical

namespace CFSG.Wreathed.TorusSplitting

open CFSG.Wreathed.BaseFourCentralizerStructure CFSG.Wreathed.OddFieldTorus

variable {G : Type*} [Group G]

theorem conj_mem_centralizer_of_mem_normalizer {T : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) (hc : c ∈ Subgroup.centralizer (T : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro y hy
  have h := hc _ ((Subgroup.mem_normalizer_iff''.mp hg y).mp hy)
  calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * y := by group

theorem normalizer_le_normalizer_centralizer (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (T : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨conj_mem_centralizer_of_mem_normalizer hg, fun h => ?_⟩
  have h' := conj_mem_centralizer_of_mem_normalizer (Subgroup.inv_mem _ hg) h
  rwa [inv_inv, show g⁻¹ * (g * c * g⁻¹) * g = c by group] at h'

theorem map_conj_of_comm {H Q : Type*} [Group H] [Group Q] (ω : H →* Q)
    (hcomm : ∀ a b : Q, a * b = b * a) (c k : H) : ω (c * k * c⁻¹) = ω k := by
  rw [map_mul, map_mul, map_inv, hcomm (ω c) (ω k), mul_inv_cancel_right]

theorem map_commutatorElement_of_comm {H Q : Type*} [Group H] [Group Q] (ω : H →* Q)
    (hcomm : ∀ a b : Q, a * b = b * a) (a b : H) : ω (a * b * a⁻¹ * b⁻¹) = 1 := by
  rw [map_mul, map_conj_of_comm ω hcomm, map_inv, mul_inv_cancel]

theorem commutator_le_ker_of_comm {H Q : Type*} [Group H] [Group Q] (ω : H →* Q)
    (hcomm : ∀ a b : Q, a * b = b * a) : commutator H ≤ ω.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, commutatorElement_def]
  exact map_commutatorElement_of_comm ω hcomm a b

theorem wreath_zpowers_disjoint (m : ℕ) :
    Disjoint (Subgroup.zpowers (Original.s m)) (Subgroup.zpowers (Original.t m)) := by
  rw [Subgroup.disjoint_def]
  intro g hs ht
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hs' : Original.s m ^ k = element m (k • 1) 0 0 := by
    rw [Original.s, element_base_zpow, smul_zero]
  have ht' : Original.t m ^ j = element m 0 (j • 1) 0 := by
    rw [Original.t, element_base_zpow, smul_zero]
  rw [ht', hs', element_eq_iff] at hj
  rw [hs', ← hj.1, element_zero]

theorem wreath_s_t_commute (m : ℕ) : Commute (Original.s m) (Original.t m) := by
  change element m 1 0 0 * element m 0 1 0 = element m 0 1 0 * element m 1 0 0
  rw [element_base_mul, element_base_mul]
  simp only [add_zero, zero_add]

theorem wreath_z_mul_self (m : ℕ) : Original.z m * Original.z m = 1 := by
  have h := pow_orderOf_eq_one (Original.z m)
  rw [Original.orderOf_z, pow_two] at h
  exact h

theorem wreath_z_inv (m : ℕ) : (Original.z m)⁻¹ = Original.z m :=
  inv_eq_of_mul_eq_one_right (wreath_z_mul_self m)

theorem wreath_z_conjugates_t (m : ℕ) :
    Original.z m * Original.t m * (Original.z m)⁻¹ = Original.s m := by
  rw [← Original.z_conjugates_s m, wreath_z_inv]
  calc Original.z m * (Original.z m * Original.s m * Original.z m) * Original.z m =
      (Original.z m * Original.z m) * Original.s m * (Original.z m * Original.z m) := by group
    _ = Original.s m := by rw [wreath_z_mul_self, one_mul, mul_one]

variable {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem zpowers_disjoint :
    Disjoint (Subgroup.zpowers (wreathModelHom S e (Original.s (2 ^ n))))
      (Subgroup.zpowers (wreathModelHom S e (Original.t (2 ^ n)))) := by
  rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers]
  exact Subgroup.disjoint_map (wreathModelHom_injective S e) (wreath_zpowers_disjoint _)

theorem actual_s_t_commute :
    Commute (wreathModelHom S e (Original.s (2 ^ n))) (wreathModelHom S e (Original.t (2 ^ n))) :=
  (wreath_s_t_commute _).map _

theorem actual_swap_conj_s :
    (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ * wreathModelHom S e (Original.s (2 ^ n)) *
      wreathModelHom S e (Original.z (2 ^ n)) = wreathModelHom S e (Original.t (2 ^ n)) := by
  rw [← map_inv, ← map_mul, ← map_mul, wreath_z_inv]
  congr 1
  rw [← Original.z_conjugates_s, wreath_z_inv]

theorem actual_swap_conj_t :
    (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ * wreathModelHom S e (Original.t (2 ^ n)) *
      wreathModelHom S e (Original.z (2 ^ n)) = wreathModelHom S e (Original.s (2 ^ n)) := by
  rw [← map_inv, ← map_mul, ← map_mul, wreath_z_inv]
  congr 1
  rw [← wreath_z_conjugates_t, wreath_z_inv]

theorem swap_mem_normalizer_four :
    wreathModelHom S e (Original.z (2 ^ n)) ∈ Subgroup.normalizer
      ((Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Subgroup G) : Set G) := by
  set w := wreathModelHom S e (Original.z (2 ^ n))
  set s := wreathModelHom S e (Original.s (2 ^ n))
  set t := wreathModelHom S e (Original.t (2 ^ n))
  have hws : w * s * w⁻¹ = t := by
    rw [← map_inv, ← map_mul, ← map_mul, Original.z_conjugates_s]
  have hwt : w * t * w⁻¹ = s := by
    rw [← map_inv, ← map_mul, ← map_mul, wreath_z_conjugates_t]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_closure]
  congr 1
  rw [Set.image_insert_eq, Set.image_singleton]
  simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
  rw [← conj_pow, ← conj_pow, hws, hwt]
  exact Set.pair_comm _ _

theorem actual_orderOf_swap : orderOf (wreathModelHom S e (Original.z (2 ^ n))) = 2 := by
  rw [orderOf_injective _ (wreathModelHom_injective S e), Original.orderOf_z]

theorem actual_orderOf_s : orderOf (wreathModelHom S e (Original.s (2 ^ n))) = 2 ^ n := by
  rw [orderOf_injective _ (wreathModelHom_injective S e), Original.orderOf_s]

theorem actual_orderOf_t : orderOf (wreathModelHom S e (Original.t (2 ^ n))) = 2 ^ n := by
  rw [orderOf_injective _ (wreathModelHom_injective S e), Original.orderOf_t]

theorem closure_pair_eq_sup (a b : G) :
    Subgroup.closure {a, b} = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
    Subgroup.zpowers_eq_closure]

omit [Group G] in
theorem card_four_normalizer_quotient [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (Subgroup.normalizer ((Subgroup.closure
        {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
          wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Subgroup G) : Set G) ⧸
      (Subgroup.centralizer ((Subgroup.closure
        {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
          wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((Subgroup.closure
          {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
            wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Subgroup G) : Set G))) =
      6 := by
  have hstruct := sylow_and_base_four_group_centralizer_structure n hn S e
  rw [← hstruct.four_coordinates]
  obtain ⟨q, -⟩ := hstruct.normalizer_quotient
  obtain ⟨φ⟩ := modelBaseNormalizerQuotient_sym3_of_simple hnonab n hn S e
  rw [Nat.card_congr (q.trans φ).toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

theorem semidirect_derived_centralizer {F : Type*} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    (sigmaGroup : Subgroup (F ≃+* F)) (hodd : Odd (Nat.card sigmaGroup))
    (WF : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hWF : ∀ g, g ∈ WF ↔ g ∈ torus F ∧ Odd (orderOf g)) :
    Subgroup.centralizer (commutator (WF ⋊[(oddTorusAction WF hWF).comp sigmaGroup.subtype]
        sigmaGroup) : Set (WF ⋊[(oddTorusAction WF hWF).comp sigmaGroup.subtype] sigmaGroup)) =
      (SemidirectProduct.inl : WF →*
        WF ⋊[(oddTorusAction WF hWF).comp sigmaGroup.subtype] sigmaGroup).range := by
  obtain ⟨-, -, -, -, hall⟩ := odd_field_fixed_torus_derived_centralizer hp hpodd hf hcard
    (if p ^ f % 4 = 1 then 1 else -1) rfl _ rfl sigmaGroup hodd
  obtain ⟨-, -, -, -, hφ⟩ := hall WF hWF
  have : IsCyclic (F ≃+* F) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := sigmaGroup)
  have htop : Subgroup.zpowers σ₀ = ⊤ := eq_top_iff.mpr fun x _ => hσ₀ x
  exact (hφ _ (fun σ w => oddTorusAction_coe WF hWF σ w) σ₀ htop).2.2.2

theorem fieldAut_subgroup_comm {F : Type*} [Field F] [Finite F] (sigmaGroup : Subgroup (F ≃+* F))
    (a b : sigmaGroup) : a * b = b * a := by
  have : IsCyclic (F ≃+* F) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
  exact (inferInstance : IsMulCommutative sigmaGroup).is_comm.comm a b

@[expose] def centralizerSubgroupOfEquiv (K P : Subgroup G) (hPK : P ≤ K)
    (hCK : Subgroup.centralizer (P : Set G) ≤ K) :
    Subgroup.centralizer ((P.subgroupOf K : Subgroup K) : Set K) ≃*
      Subgroup.centralizer (P : Set G) where
  toFun c := ⟨((c : K) : G), by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp c.2 ⟨y, hPK hy⟩
      (Subgroup.mem_subgroupOf.mpr hy))⟩
  invFun g := ⟨⟨g, hCK g.2⟩, by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp g.2 y (Subgroup.mem_subgroupOf.mp hy))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem mem_ambientOddCore_of_mem_oddCore (K P : Subgroup G) (hPK : P ≤ K)
    (hCK : Subgroup.centralizer (P : Set G) ≤ K)
    (c : Subgroup.centralizer ((P.subgroupOf K : Subgroup K) : Set K))
    (hc : c ∈ CFSG.oddCore (Subgroup.centralizer ((P.subgroupOf K : Subgroup K) : Set K))) :
    ((c : K) : G) ∈ ambientOddCore (Subgroup.centralizer (P : Set G)) := by
  have hmap := ReducedInvolution.oddCore_map_mulEquiv (centralizerSubgroupOfEquiv K P hPK hCK)
  refine ⟨centralizerSubgroupOfEquiv K P hPK hCK c, ?_, rfl⟩
  rw [← hmap]
  exact Subgroup.mem_map_of_mem _ hc

end CFSG.Wreathed.TorusSplitting
