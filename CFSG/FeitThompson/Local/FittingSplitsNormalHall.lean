module

public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Local.NilpotentHallCharacteristic
public import CFSG.FeitThompson.Local.CentralProductPlaneCentralizer
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.NormalHallIntersectionHall
import CFSG.FeitThompson.Local.FittingMonoNormal
import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] [Finite X] {π : Set ℕ} {N : Subgroup X}

omit [Finite X] in
theorem isHallSubgroup_iff_isHallPiSubgroup {H : Subgroup X} :
    IsHallSubgroup π H ↔ IsHallPiSubgroup π H := by
  rw [isHallSubgroup_iff, isHallPiSubgroup_iff]
  exact and_congr isPiNumber_iff isPiNumber_compl_iff

section Nilpotent

variable (π) (F : Type*) [Group F] [Finite F] [Group.IsNilpotent F]

theorem sylowPiPart_univ_eq_top : sylowPiPart (Set.univ : Set ℕ) F = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [natCard_sylowPiPart]
  have hset : piPrimeFactors (Set.univ : Set ℕ) F = (Nat.card F).primeFactors := by
    ext p; simp
  rw [hset, ← Nat.prod_factorization_eq_prod_primeFactors]
  exact Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'

theorem sylowPiPart_sup_compl : sylowPiPart π F ⊔ sylowPiPart πᶜ F = ⊤ := by
  refine top_le_iff.1 ?_
  rw [← sylowPiPart_univ_eq_top F]
  refine sylowPiPart_le fun p hp _ P => ?_
  by_cases h : p ∈ π
  · exact le_sup_of_le_left (sylow_le_sylowPiPart hp h P)
  · exact le_sup_of_le_right (sylow_le_sylowPiPart hp h P)

theorem coprime_natCard_sylowPiPart :
    (Nat.card (sylowPiPart π F)).Coprime (Nat.card (sylowPiPart πᶜ F)) :=
  IsPiNumber.coprime_of_compl (isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_sylowPiPart π F))
    (isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_sylowPiPart πᶜ F))
    Nat.card_pos.ne' Nat.card_pos.ne'

theorem sylowPiPart_inf_compl : sylowPiPart π F ⊓ sylowPiPart πᶜ F = ⊥ :=
  disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard (coprime_natCard_sylowPiPart π F))

theorem commutator_sylowPiPart_compl : ⁅sylowPiPart π F, sylowPiPart πᶜ F⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.commute_of_normal_of_disjoint _ _ inferInstance inferInstance
    (Subgroup.disjoint_of_coprime_natCard (coprime_natCard_sylowPiPart π F)) x y hx hy).symm

end Nilpotent

def fittingPiPart (π : Set ℕ) (X : Type*) [Group X] [Finite X] : Subgroup X :=
  (sylowPiPart π (fittingRaw X)).map (fittingRaw X).subtype

theorem fittingPiPart_eq_map (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    fittingPiPart π X = (sylowPiPart π (fittingRaw X)).map (fittingRaw X).subtype := (rfl)

theorem fittingPiPart_le_fittingRaw : fittingPiPart π X ≤ fittingRaw X := by
  rw [fittingPiPart_eq_map]
  exact Subgroup.map_subtype_le _

theorem subgroupOf_fittingPiPart :
    (fittingPiPart π X).subgroupOf (fittingRaw X) = sylowPiPart π (fittingRaw X) := by
  rw [fittingPiPart_eq_map]
  exact Subgroup.comap_map_eq_self_of_injective (fittingRaw X).subtype_injective _

theorem fittingPiPart_eq_map_iSup_piPrimeFactors (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    fittingPiPart π X =
      (⨆ p ∈ piPrimeFactors π (fittingRaw X), ⨆ P : Sylow p (fittingRaw X),
        (P : Subgroup (fittingRaw X))).map (fittingRaw X).subtype := by
  rw [fittingPiPart_eq_map, sylowPiPart_eq_iSup_piPrimeFactors]

theorem natCard_fittingPiPart (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    Nat.card (fittingPiPart π X) = Nat.card (sylowPiPart π (fittingRaw X)) := by
  rw [fittingPiPart_eq_map, Subgroup.card_map_of_injective (fittingRaw X).subtype_injective]

theorem isPiSubgroup_fittingPiPart (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    IsPiSubgroup π (fittingPiPart π X) := by
  rw [isPiSubgroup_iff, natCard_fittingPiPart]
  exact isPiSubgroup_iff.1 (isPiSubgroup_sylowPiPart π (fittingRaw X))

theorem fittingPiPart_eq_bot (π : Set ℕ) (X : Type*) [Group X] [Finite X]
    (h : piPrimeFactors π (fittingRaw X) = ∅) : fittingPiPart π X = ⊥ := by
  rw [fittingPiPart_eq_map, sylowPiPart_eq_bot _ _ h, Subgroup.map_bot]

theorem fittingPiPart_empty (X : Type*) [Group X] [Finite X] :
    fittingPiPart (∅ : Set ℕ) X = ⊥ := by
  rw [fittingPiPart_eq_map, sylowPiPart_empty, Subgroup.map_bot]

theorem characteristic_subgroupOf_fittingPiPart (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    ((fittingPiPart π X).subgroupOf (fittingRaw X)).Characteristic := by
  rw [subgroupOf_fittingPiPart]
  infer_instance

instance fittingPiPart_characteristic (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    (fittingPiPart π X).Characteristic := by
  rw [fittingPiPart_eq_map]
  exact Subgroup.characteristic_of_characteristic_of_characteristic

instance fittingPiPart_normal (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    (fittingPiPart π X).Normal := Subgroup.normal_of_characteristic _

theorem fittingPiPart_sup_compl (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    fittingPiPart π X ⊔ fittingPiPart πᶜ X = fittingRaw X := by
  rw [fittingPiPart_eq_map, fittingPiPart_eq_map, ← Subgroup.map_sup, sylowPiPart_sup_compl,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem fittingPiPart_inf_compl (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    fittingPiPart π X ⊓ fittingPiPart πᶜ X = ⊥ := by
  rw [fittingPiPart_eq_map, fittingPiPart_eq_map,
    ← Subgroup.map_inf _ _ _ (fittingRaw X).subtype_injective, sylowPiPart_inf_compl,
    Subgroup.map_bot]

theorem commutator_fittingPiPart_compl (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    ⁅fittingPiPart π X, fittingPiPart πᶜ X⁆ = ⊥ := by
  rw [fittingPiPart_eq_map, fittingPiPart_eq_map, ← Subgroup.map_commutator,
    commutator_sylowPiPart_compl, Subgroup.map_bot]

theorem fittingRaw_inf_eq_fittingPiPart (hN : N.Normal) (hHall : IsHallPiSubgroup π N) :
    fittingRaw X ⊓ N = fittingPiPart π X := by
  have h1 : IsHallPiSubgroup π ((N ⊓ fittingRaw X).subgroupOf (fittingRaw X)) :=
    hHall.inf_subgroupOf hN (fittingRaw X)
  have h2 : (N ⊓ fittingRaw X).subgroupOf (fittingRaw X) = sylowPiPart π (fittingRaw X) :=
    (isHallSubgroup_iff_isHallPiSubgroup.2 h1).eq_sylowPiPart
  have h3 := congrArg (Subgroup.map (fittingRaw X).subtype) h2
  rw [Subgroup.subgroupOf_map_subtype, ← fittingPiPart_eq_map, inf_right_idem] at h3
  rw [← h3, inf_comm]

theorem map_subtype_fittingRaw_eq_fittingPiPart (hN : N.Normal) (hHall : IsHallPiSubgroup π N) :
    (fittingRaw N).map N.subtype = fittingPiPart π X := by
  rw [map_subtype_fittingRaw_eq_inf hN, fittingRaw_inf_eq_fittingPiPart hN hHall]

theorem isInternalDirectProduct_map_fittingRaw (hN : N.Normal) (hHall : IsHallPiSubgroup π N) :
    IsInternalDirectProduct (fittingRaw X) ((fittingRaw N).map N.subtype)
      (fittingPiPart πᶜ X) := by
  rw [map_subtype_fittingRaw_eq_fittingPiPart hN hHall]
  exact isInternalDirectProduct_of_sup_eq (fittingPiPart_sup_compl π X)
    (fittingPiPart_inf_compl π X) (commutator_fittingPiPart_compl π X)

noncomputable def fittingRawProdMulEquivFittingRaw (hN : N.Normal)
    (hHall : IsHallPiSubgroup π N) :
    ((fittingRaw N).map N.subtype × fittingPiPart πᶜ X) ≃* fittingRaw X :=
  have h := isInternalDirectProduct_map_fittingRaw hN hHall
  mulEquivProdOfCoeEqMul h.coe_eq_mul h.inf_eq_bot fun _ hx _ hy => h.commute hx hy

theorem coe_fittingRawProdMulEquivFittingRaw_apply (hN : N.Normal)
    (hHall : IsHallPiSubgroup π N)
    (x : (fittingRaw N).map N.subtype × fittingPiPart πᶜ X) :
    ((fittingRawProdMulEquivFittingRaw hN hHall x : fittingRaw X) : X)
      = (x.1 : X) * (x.2 : X) :=
  have h := isInternalDirectProduct_map_fittingRaw hN hHall
  coe_mulEquivProdOfCoeEqMul_apply h.coe_eq_mul h.inf_eq_bot
    (fun _ hx _ hy => h.commute hx hy) x

theorem natCard_fittingRaw_eq_mul (hN : N.Normal) (hHall : IsHallPiSubgroup π N) :
    Nat.card (fittingRaw X) = Nat.card (fittingRaw N) * Nat.card (fittingPiPart πᶜ X) := by
  rw [(isInternalDirectProduct_map_fittingRaw hN hHall).card_eq_mul,
    Subgroup.card_map_of_injective N.subtype_injective]

end

end CFSG.FeitThompson
