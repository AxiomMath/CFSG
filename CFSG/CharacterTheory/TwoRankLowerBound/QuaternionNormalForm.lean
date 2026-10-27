module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionRelations

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def quaternionNormalFormHom {G : Type*} [Group G] (parameter : ℕ)
    (cyclicHom : Multiplicative (ZMod (2 * parameter)) →* G) (outside : G)
    (hsquare : outside ^ 2 = cyclicHom (Multiplicative.ofAdd (parameter : ZMod (2 * parameter))))
    (hcommute : ∀ residue : ZMod (2 * parameter),
      cyclicHom (Multiplicative.ofAdd residue) * outside =
        outside * (cyclicHom (Multiplicative.ofAdd residue))⁻¹) :
    QuaternionGroup parameter →* G := by
  let power : ZMod (2 * parameter) → G := fun residue => cyclicHom (Multiplicative.ofAdd residue)
  change outside ^ 2 = power (parameter : ZMod (2 * parameter)) at hsquare
  change ∀ residue : ZMod (2 * parameter), power residue * outside =
    outside * (power residue)⁻¹ at hcommute
  have hzero : power 0 = 1 := map_one cyclicHom
  have hadd : ∀ left right, power (left + right) = power left * power right := by
    intro left right
    exact map_mul cyclicHom (Multiplicative.ofAdd left) (Multiplicative.ofAdd right)
  have hsub : ∀ left right, power (left - right) = power left * (power right)⁻¹ := by
    intro left right
    have hneg : power (-right) = (power right)⁻¹ :=
      map_inv cyclicHom (Multiplicative.ofAdd right)
    rw [sub_eq_add_neg, hadd, hneg]
  have hpowercommute : ∀ left right, Commute (power left) (power right) := by
    intro left right
    change power left * power right = power right * power left
    rw [← hadd, ← hadd, add_comm]
  refine
    { toFun := fun quaternion => match quaternion with
        | QuaternionGroup.a residue => power residue
        | QuaternionGroup.xa residue => outside * power residue
      map_one' := ?_
      map_mul' := ?_ }
  · exact hzero
  · intro left right
    cases left with
    | a left =>
      cases right with
      | a right => exact hadd left right
      | xa right =>
        change outside * power (right - left) = power left * (outside * power right)
        calc
          outside * power (right - left) = outside * (power right * (power left)⁻¹) := by rw [hsub]
          _ = outside * ((power left)⁻¹ * power right) := by
            rw [(hpowercommute left right).inv_left.eq]
          _ = (outside * (power left)⁻¹) * power right := by group
          _ = (power left * outside) * power right := by rw [hcommute]
          _ = power left * (outside * power right) := by group
    | xa left =>
      cases right with
      | a right =>
        change outside * power (left + right) = outside * power left * power right
        rw [hadd, mul_assoc]
      | xa right =>
        change power ((parameter : ZMod (2 * parameter)) + right - left) =
          (outside * power left) * (outside * power right)
        calc
          power ((parameter : ZMod (2 * parameter)) + right - left) =
              outside ^ 2 * (power right * (power left)⁻¹) := by rw [hsub, hadd, ← hsquare, mul_assoc]
          _ = outside ^ 2 * ((power left)⁻¹ * power right) := by
            rw [(hpowercommute left right).inv_left.eq]
          _ = outside * (outside * (power left)⁻¹) * power right := by rw [pow_two]; group
          _ = outside * (power left * outside) * power right := by rw [hcommute]
          _ = (outside * power left) * (outside * power right) := by group

theorem quaternionNormalFormHom_a {G : Type*} [Group G] (parameter : ℕ)
    (cyclicHom : Multiplicative (ZMod (2 * parameter)) →* G) (outside : G)
    (hsquare : outside ^ 2 = cyclicHom (Multiplicative.ofAdd (parameter : ZMod (2 * parameter))))
    (hcommute : ∀ residue : ZMod (2 * parameter),
      cyclicHom (Multiplicative.ofAdd residue) * outside =
        outside * (cyclicHom (Multiplicative.ofAdd residue))⁻¹)
    (residue : ZMod (2 * parameter)) :
    quaternionNormalFormHom parameter cyclicHom outside hsquare hcommute
      (QuaternionGroup.a residue) = cyclicHom (Multiplicative.ofAdd residue) := rfl

theorem quaternionNormalFormHom_xa {G : Type*} [Group G] (parameter : ℕ)
    (cyclicHom : Multiplicative (ZMod (2 * parameter)) →* G) (outside : G)
    (hsquare : outside ^ 2 = cyclicHom (Multiplicative.ofAdd (parameter : ZMod (2 * parameter))))
    (hcommute : ∀ residue : ZMod (2 * parameter),
      cyclicHom (Multiplicative.ofAdd residue) * outside =
        outside * (cyclicHom (Multiplicative.ofAdd residue))⁻¹)
    (residue : ZMod (2 * parameter)) :
    quaternionNormalFormHom parameter cyclicHom outside hsquare hcommute
      (QuaternionGroup.xa residue) = outside * cyclicHom (Multiplicative.ofAdd residue) := rfl

theorem quaternion_normal_form_isomorphism_of_cyclic_index_two (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1)
    (cyclic : Subgroup G) [IsCyclic cyclic] (hindex : cyclic.index = 2)
    (hcenterle : Subgroup.center G ≤ cyclic) (hcentertwo : Nat.card (Subgroup.center G) = 2)
    (parameter : ℕ) (hparameter : 0 < parameter) (hcard : Nat.card cyclic = 2 * parameter)
    (outside : G) (houtside : outside ∉ cyclic) (houtsideorder : orderOf outside = 4) :
    Nonempty (QuaternionGroup parameter ≃* G) := by
  classical
  let residueEquiv : Multiplicative (ZMod (2 * parameter)) ≃* cyclic :=
    (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard.symm).toAddEquiv).trans
      (zmodCyclicMulEquiv (inferInstance : IsCyclic cyclic))
  let cyclicHom : Multiplicative (ZMod (2 * parameter)) →* G :=
    cyclic.subtype.comp residueEquiv.toMonoidHom
  have hcyclicinjective : Function.Injective cyclicHom :=
    cyclic.subtype_injective.comp residueEquiv.injective
  have hcyclicmem : ∀ residue, cyclicHom (Multiplicative.ofAdd residue) ∈ cyclic :=
    fun residue => (residueEquiv (Multiplicative.ofAdd residue)).property
  have hhalforder : orderOf (cyclicHom (Multiplicative.ofAdd
      (parameter : ZMod (2 * parameter)))) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      have hresidue : (Multiplicative.ofAdd (parameter : ZMod (2 * parameter))) ^ 2 = 1 := by
        rw [pow_two]
        change (parameter : ZMod (2 * parameter)) + parameter = 0
        rw [← Nat.cast_add]
        simpa only [two_mul] using ZMod.natCast_self (2 * parameter)
      rw [hresidue, map_one]
    · intro hone
      have hresidue := hcyclicinjective (hone.trans (map_one cyclicHom).symm)
      change (parameter : ZMod (2 * parameter)) = 0 at hresidue
      have hval := congrArg ZMod.val hresidue
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hval
      omega
  have houtsideinvolution : orderOf (outside ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by omega : 2 ≠ 0) (by rw [houtsideorder]; decide), houtsideorder]
  have hsquare : outside ^ 2 = cyclicHom (Multiplicative.ofAdd
      (parameter : ZMod (2 * parameter))) := by
    exact commuting_involutions_eq_of_twoRank_le_one G hrank _ _ houtsideinvolution hhalforder
      (Subgroup.mem_center_iff.mp
        (involution_mem_center_of_rank_one_two_group G htwogroup hrank _ hhalforder) _)
  have hcommute : ∀ residue : ZMod (2 * parameter),
      cyclicHom (Multiplicative.ofAdd residue) * outside =
        outside * (cyclicHom (Multiplicative.ofAdd residue))⁻¹ := by
    intro residue
    have hinverseinverse := outside_cyclic_index_two_conjugates_by_inversion G htwogroup hrank
      cyclic hindex hcenterle hcentertwo outside houtside _ (cyclic.inv_mem (hcyclicmem residue))
    have hequal := congrArg (fun element : G => element * outside) hinverseinverse
    simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hequal.symm
  let homomorphism := quaternionNormalFormHom parameter cyclicHom outside hsquare hcommute
  have hinjective : Function.Injective homomorphism := by
    intro left right hequal
    cases left with
    | a left =>
      cases right with
      | a right =>
        apply congrArg QuaternionGroup.a
        exact Multiplicative.ofAdd.injective (hcyclicinjective hequal)
      | xa right =>
        have hequal : cyclicHom (Multiplicative.ofAdd left) =
          outside * cyclicHom (Multiplicative.ofAdd right) := hequal
        have houtsideeq : outside = cyclicHom (Multiplicative.ofAdd left) *
            (cyclicHom (Multiplicative.ofAdd right))⁻¹ := by rw [hequal]; group
        exact False.elim (houtside (houtsideeq ▸
          cyclic.mul_mem (hcyclicmem left) (cyclic.inv_mem (hcyclicmem right))))
    | xa left =>
      cases right with
      | a right =>
        have hequal : outside * cyclicHom (Multiplicative.ofAdd left) =
          cyclicHom (Multiplicative.ofAdd right) := hequal
        have houtsideeq : outside = cyclicHom (Multiplicative.ofAdd right) *
            (cyclicHom (Multiplicative.ofAdd left))⁻¹ := by rw [← hequal]; group
        exact False.elim (houtside (houtsideeq ▸
          cyclic.mul_mem (hcyclicmem right) (cyclic.inv_mem (hcyclicmem left))))
      | xa right =>
        apply congrArg QuaternionGroup.xa
        exact Multiplicative.ofAdd.injective (hcyclicinjective (mul_left_cancel hequal))
  have hsurjective : Function.Surjective homomorphism := by
    intro element
    by_cases hmember : element ∈ cyclic
    · let residue := residueEquiv.symm (⟨element, hmember⟩ : cyclic)
      refine ⟨QuaternionGroup.a (Multiplicative.toAdd residue), ?_⟩
      change (residueEquiv residue : G) = element
      exact congrArg Subtype.val (residueEquiv.apply_symm_apply _)
    · have hinverseoutside : outside⁻¹ ∉ cyclic := by
        intro hinverse
        exact houtside (cyclic.inv_mem_iff.mp hinverse)
      have hdifference : outside⁻¹ * element ∈ cyclic :=
        (Subgroup.mul_mem_iff_of_index_two hindex).mpr
          ⟨fun h => False.elim (hinverseoutside h), fun h => False.elim (hmember h)⟩
      let residue := residueEquiv.symm (⟨outside⁻¹ * element, hdifference⟩ : cyclic)
      refine ⟨QuaternionGroup.xa (Multiplicative.toAdd residue), ?_⟩
      change outside * (residueEquiv residue : G) = element
      have hequal : (residueEquiv residue : G) = outside⁻¹ * element :=
        congrArg Subtype.val (residueEquiv.apply_symm_apply _)
      rw [hequal]
      group
  exact ⟨MulEquiv.ofBijective homomorphism ⟨hinjective, hsurjective⟩⟩

end CFSG.TwoRankLowerBound.Helpers
