module

public import CFSG.CharacterTheory.Wreathed.AbelianInertiaInduction
public import CFSG.CharacterTheory.Blocks.BrauerInduction

public section

open scoped BigOperators Classical

namespace CFSG.OddOrderBasics

open TwoRankLowerBound.Helpers Wreathed

theorem induced_class_function_identities {G : Type*} [Group G] [Fintype G] (H : Subgroup G) :
    (∀ (a b : ℂ) (α β : H → ℂ),
      inducedFunction H (a • α + b • β) = a • inducedFunction H α + b • inducedFunction H β) ∧
    (∀ α : H → ℂ, inducedFunction H (fun h => starRingEnd ℂ (α h)) =
      fun g => starRingEnd ℂ (inducedFunction H α g)) ∧
    (∀ α : H → ℂ, inducedFunction H α 1 = (H.index : ℂ) * α 1) ∧
    (H.Normal → ∀ α : H → ℂ, ∀ g : G, g ∉ H → inducedFunction H α g = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b α β
    funext g
    simp only [inducedFunction, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (∑ x : G, if h : x⁻¹ * g * x ∈ H then a * α ⟨x⁻¹ * g * x, h⟩ +
        b * β ⟨x⁻¹ * g * x, h⟩ else 0) =
        a * (∑ x : G, if h : x⁻¹ * g * x ∈ H then α ⟨x⁻¹ * g * x, h⟩ else 0) +
        b * (∑ x : G, if h : x⁻¹ * g * x ∈ H then β ⟨x⁻¹ * g * x, h⟩ else 0) from by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp]
    ring
  · intro α
    funext g
    simp only [inducedFunction, map_mul, map_sum, map_inv₀, map_natCast]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  · intro α
    have hcard : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hterm : ∀ x : G, (if hmember : x⁻¹ * (1 : G) * x ∈ H then
        α ⟨x⁻¹ * 1 * x, hmember⟩ else 0) = α 1 := by
      intro x
      have hmem : x⁻¹ * (1 : G) * x ∈ H := by simp
      rw [dite_eq_left hmem]
      congr 1
      exact Subtype.ext (by simp)
    simp only [inducedFunction]
    rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Nat.card_eq_fintype_card, ← H.card_mul_index, Nat.cast_mul]
    field_simp
  · intro hH α g hg
    simp only [inducedFunction]
    rw [Finset.sum_eq_zero, mul_zero]
    intro x _
    rw [dite_eq_right]
    intro hx
    exact absurd (by simpa [mul_assoc] using hH.conj_mem _ hx x) hg

theorem induction_preserves_characters {G : Type} [Group G] [Fintype G] (H : Subgroup G) :
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (ρ : Representation ℂ H V),
      ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
        (σ : Representation ℂ G W), σ.character = inducedFunction H ρ.character) ∧
    ∀ α ∈ BlocksVChar H, inducedFunction H α ∈ BlocksVChar G := by
  refine ⟨fun V _ _ _ ρ => ?_, fun α hα => inducedFunction_mem_blocksVChar H hα⟩
  let data : FiniteComplexRepresentation.{0, 0} H := { vector := V, representation := ρ }
  let induced := coinducedFiniteComplexRepresentation H data
  exact ⟨induced.vector, inferInstance, inferInstance, inferInstance, induced.representation,
    funext fun g => coinducedFiniteComplexRepresentation_character H data g⟩

theorem conjugateNormalCharacter_coset {L : Type*} [Group L] (H : Subgroup L) [H.Normal]
    {φ : H → ℂ} (hφ : BlocksIsClassFunction φ) {t t' : L}
    (htt' : (t : L ⧸ H) = (t' : L ⧸ H)) :
    conjugateNormalCharacter H φ t = conjugateNormalCharacter H φ t' := by
  have hk : t⁻¹ * t' ∈ H := QuotientGroup.eq.mp htt'
  have ht' : t' = t * (t⁻¹ * t') := by group
  rw [ht', conjugateNormalCharacter_mul_of_mem H φ t
    (le_characterInertiaSubgroup H hφ hk)]

theorem blocksInnerProduct_finset_sum_right {K : Type} [Group K] [Fintype K] {ι : Type*}
    (s : Finset ι) (f : K → ℂ) (g : ι → K → ℂ) :
    BlocksInnerProduct f (∑ i ∈ s, g i) = ∑ i ∈ s, BlocksInnerProduct f (g i) := by
  unfold BlocksInnerProduct
  simp only [Finset.sum_apply, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem normal_subgroup_induced_inner_products {L : Type} [Group L] [Fintype L]
    (H : Subgroup L) [H.Normal] (rep : L ⧸ H → L) (hrep : ∀ q, (rep q : L ⧸ H) = q)
    (θ φ : H → ℂ) (hθ : θ ∈ BlocksIrr H) (hφ : φ ∈ BlocksIrr H) :
    (fun h : H => inducedFunction H φ h) = ∑ q, conjugateNormalCharacter H φ (rep q) ∧
    BlocksInnerProduct (inducedFunction H θ) (inducedFunction H φ) =
      ((Finset.univ.filter fun q => θ = conjugateNormalCharacter H φ (rep q)).card : ℂ) ∧
    ∀ rep' : L ⧸ H → L, (∀ q, (rep' q : L ⧸ H) = q) →
      ∀ q, conjugateNormalCharacter H φ (rep' q) = conjugateNormalCharacter H φ (rep q) := by
  have hφclass : BlocksIsClassFunction φ := by
    obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hφ
    exact fun g h => Representation.char_conj ρ g h
  have hinj : Function.Injective rep := fun q q' h => by rw [← hrep q, ← hrep q', h]
  set C : Finset L := Finset.univ.image rep with hCdef
  have hC : ∀ q : L ⧸ H, ∃! h, h ∈ C ∧ (h : L ⧸ H) = q := by
    intro q
    refine ⟨rep q, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ q), hrep q⟩, ?_⟩
    rintro h ⟨hh, rfl⟩
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hh
    rw [hrep]
  have hres : (fun h : H => inducedFunction H φ h) = ∑ q, conjugateNormalCharacter H φ (rep q) := by
    have h := inducedFunction_restrict_eq_sum_conjugate H H le_rfl φ
      (fun i hi => (le_characterInertiaSubgroup H hφclass hi)) φ (fun x hx => rfl) C hC
    rw [h, hCdef, Finset.sum_image fun q _ q' _ hqq' => hinj hqq']
  refine ⟨hres, ?_, fun rep' hrep' q => conjugateNormalCharacter_coset H hφclass
    ((hrep' q).trans (hrep q).symm)⟩
  have hclass : BlocksIsClassFunction (inducedFunction H φ) := fun g h =>
    inducedFunction_conjugate H φ g h
  rw [blocksInnerProduct_inducedFunction_left H θ _ hclass, hres,
    blocksInnerProduct_finset_sum_right]
  have hconjIrr : ∀ q, conjugateNormalCharacter H φ (rep q) ∈ BlocksIrr H := fun q =>
    conjugateNormalCharacter_mem_blocksIrr H hφ (rep q)
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h := blocksInnerProduct_irreducible ⟨θ, hθ⟩ ⟨_, hconjIrr q⟩
  rw [h]
  by_cases hq : θ = conjugateNormalCharacter H φ (rep q)
  · rw [ite_eq_left (Subtype.ext hq), ite_eq_left hq, Nat.cast_one]
  · rw [ite_eq_right (fun h' => hq (congrArg Subtype.val h')), ite_eq_right hq, Nat.cast_zero]

end CFSG.OddOrderBasics
