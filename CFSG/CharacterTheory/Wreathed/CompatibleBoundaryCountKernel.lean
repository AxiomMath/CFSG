module

public import CFSG.CharacterTheory.Wreathed.CompatibleBoundaryCountSupport
public import CFSG.CharacterTheory.Wreathed.BaseFourCentralizerStructure
public import CFSG.CharacterTheory.Wreathed.BrauerWongInvolutions

public noncomputable section

namespace CFSG.Wreathed.CompatibleFamilies

open CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.Wreathed.BaseFourCentralizerStructure
open scoped Classical Pointwise

universe u

variable {G : Type u} [Group G] {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

@[expose] def boundaryCommutator (η : G) : Subgroup G :=
  Subgroup.closure {y : G | ∃ c ∈ ambientOddCore (Subgroup.centralizer
    (Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
      wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G)),
    y = c⁻¹ * (η⁻¹ * c * η)}

@[expose] def boundaryProduct (η : G) : Subgroup G :=
  boundaryCommutator S e η ⊔ (commutator (Subgroup.centralizer
    {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
      (2 ^ n / 2)})).map (Subgroup.centralizer
    {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
      (2 ^ n / 2)}).subtype

@[expose] def boundaryKernel (η : G) :
    Subgroup (ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))) :=
  (ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) ⊓
    boundaryProduct S e η).subgroupOf
      (ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)))

theorem map_commutator_subtype (H : Subgroup G) :
    (commutator H).map H.subtype = ⁅H, H⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem x_eq_modelHom :
    (wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
      (2 ^ n / 2) = wreathModelHom S e (Original.x (2 ^ n)) := by
  rw [← map_mul, ← map_pow]
  rfl

theorem oddCore_sylow_le_centralizer :
    ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) ≤
      Subgroup.centralizer
        {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
          (2 ^ n / 2)} := by
  refine (ambientOddCore_le _).trans (Subgroup.centralizer_le ?_)
  rw [Set.singleton_subset_iff]
  exact (S : Subgroup G).pow_mem ((S : Subgroup G).mul_mem (wreathModelHom_mem S e _)
    (wreathModelHom_mem S e _)) _

theorem commutator_le_boundaryKernel (η : G) :
    commutator (ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))) ≤
      boundaryKernel S e η := by
  intro g hg
  have hgE : (g : G) ∈ ⁅ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)),
      ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G))⁆ := by
    rw [← map_commutator_subtype]
    exact Subgroup.mem_map_of_mem _ hg
  have hEN := oddCore_sylow_le_centralizer S e
  have hgN := Subgroup.commutator_mono hEN hEN hgE
  rw [← map_commutator_subtype] at hgN
  refine ⟨g.2, ?_⟩
  exact Subgroup.mem_sup_right hgN

instance boundaryKernel_normal (η : G) : (boundaryKernel S e η).Normal :=
  normal_of_commutator_le (commutator_le_boundaryKernel S e η)

instance boundaryKernel_quotient_isMulCommutative (η : G) :
    IsMulCommutative (ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) ⧸
      boundaryKernel S e η) :=
  (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr
    (commutator_le_boundaryKernel S e η)

theorem oddCore_four_le_centralizer :
    ambientOddCore (Subgroup.centralizer
      (Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G)) ≤
      Subgroup.centralizer
        {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
          (2 ^ n / 2)} := by
  refine (ambientOddCore_le _).trans (Subgroup.centralizer_le ?_)
  rw [Set.singleton_subset_iff, x_eq_modelHom, ← modelHom_x2_mul_t_half S e]
  refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) (Subgroup.subset_closure ?_)
  · left
    rw [← map_pow]
    rfl
  · right
    rw [← map_pow]
    rfl

theorem commutator_map_le_centralizer :
    (commutator (Subgroup.centralizer
      {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
        (2 ^ n / 2)})).map (Subgroup.centralizer
      {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
        (2 ^ n / 2)}).subtype ≤ Subgroup.centralizer
      {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
        (2 ^ n / 2)} :=
  Subgroup.map_subtype_le _

variable [Finite G]

theorem boundaryCommutator_le (hn : 2 ≤ n) {η : G}
    (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    boundaryCommutator S e η ≤ ambientOddCore (Subgroup.centralizer
      (Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G)) := by
  have hnorm :=
    (sylow_and_base_four_group_centralizer_structure n hn S e).order_three_normalizes_oddCore
      ⟨η, hη⟩ hord
  rw [modelT_eq_actual_generated] at hnorm
  rw [boundaryCommutator, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  have hc' : η⁻¹ * c * η ∈ ambientOddCore (Subgroup.centralizer
      (Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G)) :=
    (Subgroup.mem_normalizer_iff''.mp hnorm c).mp hc
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hc'

theorem boundaryProduct_le (hn : 2 ≤ n) {η : G}
    (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    boundaryProduct S e η ≤ Subgroup.centralizer
      {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
        (2 ^ n / 2)} :=
  sup_le ((boundaryCommutator_le S e hn hη hord).trans (oddCore_four_le_centralizer S e))
    (commutator_map_le_centralizer S e)

omit [Finite G] in
theorem boundaryProduct_normal (η : G) :
    ((boundaryProduct S e η).subgroupOf (Subgroup.centralizer
      {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
        (2 ^ n / 2)})).Normal := by
  apply normal_of_commutator_le
  intro g hg
  rw [Subgroup.mem_subgroupOf]
  exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ hg)

theorem coe_boundaryProduct (hn : 2 ≤ n) {η : G}
    (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    (boundaryProduct S e η : Set G) = (boundaryCommutator S e η : Set G) *
      ((commutator (Subgroup.centralizer
        {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
          (2 ^ n / 2)})).map (Subgroup.centralizer
        {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
          (2 ^ n / 2)}).subtype : Set G) := by
  apply Subgroup.coe_mul_of_left_le_normalizer_right
  refine ((boundaryCommutator_le S e hn hη hord).trans
    (oddCore_four_le_centralizer S e)).trans ?_
  have h := Subgroup.le_normalizer_map (H := commutator (Subgroup.centralizer
    {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
      (2 ^ n / 2)})) (Subgroup.centralizer
    {(wreathModelHom S e (Original.s (2 ^ n)) * wreathModelHom S e (Original.t (2 ^ n))) ^
      (2 ^ n / 2)}).subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

end CFSG.Wreathed.CompatibleFamilies
