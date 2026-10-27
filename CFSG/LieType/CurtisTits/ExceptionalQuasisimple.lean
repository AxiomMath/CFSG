module

public import CFSG.LieType.CurtisTits.Perfect
public import CFSG.LieType.TitsSimplicity
public import CFSG.LieType.Steinberg.Minuscule.ChevExtras
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116

public section

namespace CFSG.LieType.CurtisTits

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.TitsSimplicity CFSG.Blueprint.Chevalley
open scoped commutatorElement

variable (k : Type*) [Field k]

theorem isPerfect_e6 : Group.IsPerfect ↥(e6Data_valid.minGroup k) := by
  have hΦ := roots_eq isFiniteType_cartan_E6
  obtain ⟨O⟩ := e6_nonempty_commOrder k
  obtain ⟨C, -, hC⟩ := e6Datum_commutatorFormula k _ hΦ O
  have hext := e6_chevalleyExtras k O C hC
  refine isPerfect_of_rootGroup_single_le_commutator (e6Datum_isCTGroupDatum k)
    (e6Datum_steinbergExtras k).two_smul_le fun i => ?_
  obtain ⟨δ, hδ, γ, hγ, hne, j, hj, heq, hunit⟩ := hext.rankTwo i
  have hroots : (e6Datum k).roots = {γ | IsRoot .E6 γ} := hΦ
  have hδ' : IsRoot .E6 δ := by rw [hroots] at hδ; exact hδ
  have hγ' : IsRoot .E6 γ := by rw [hroots] at hγ; exact hγ
  have hsingle : IsRoot .E6 (Pi.single i 1) := IsRoot.basis (τ := .E6) i
  have hj1 : j = 1 := by
    have h := eq_one_of_isRoot_nsmul_add_nsmul posDef_cartan_E6 hδ' hγ' hne one_pos
      (show 0 < j by omega) (by rw [one_smul, ← heq]; exact hsingle)
    exact h.2
  subst hj1
  rw [one_smul] at heq
  have hroot : IsRoot .E6 (δ + γ) := heq ▸ hsingle
  have hlist := list_eq_singleton_of_isRoot posDef_cartan_E6 hΦ O hδ hγ hne hroot
  intro g hg
  have hsmem : Pi.single i 1 ∈ (RootSystem.ofCartan (e6Datum k).isFiniteType
      (e6Datum k).divisible).roots := by
    change Pi.single i 1 ∈ (e6Datum k).roots
    rw [hroots]; exact hsingle
  obtain ⟨u, rfl⟩ := ((hext.param _ hsmem).1 g).1 hg
  obtain ⟨c, hc⟩ := hunit
  have hform := hC δ hδ γ hγ hne ((c⁻¹ : kˣ) * u) 1
  rw [hlist, List.map_singleton, List.prod_singleton, one_smul, one_smul, ← heq, pow_one,
    pow_one, mul_one, ← hc, ← mul_assoc, Units.mul_inv, one_mul] at hform
  rw [← hform]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem isPerfect_e7 : Group.IsPerfect ↥(e7Data_valid.minGroup k) := by
  have hΦ := roots_eq isFiniteType_cartan_E7
  obtain ⟨O⟩ := e7_nonempty_commOrder k
  obtain ⟨C, -, hC⟩ := e7Datum_commutatorFormula k _ hΦ O
  have hext := e7_chevalleyExtras k O C hC
  refine isPerfect_of_rootGroup_single_le_commutator (e7Datum_isCTGroupDatum k)
    (e7Datum_steinbergExtras k).two_smul_le fun i => ?_
  obtain ⟨δ, hδ, γ, hγ, hne, j, hj, heq, hunit⟩ := hext.rankTwo i
  have hroots : (e7Datum k).roots = {γ | IsRoot .E7 γ} := hΦ
  have hδ' : IsRoot .E7 δ := by rw [hroots] at hδ; exact hδ
  have hγ' : IsRoot .E7 γ := by rw [hroots] at hγ; exact hγ
  have hsingle : IsRoot .E7 (Pi.single i 1) := IsRoot.basis (τ := .E7) i
  have hj1 : j = 1 := by
    have h := eq_one_of_isRoot_nsmul_add_nsmul posDef_cartan_E7 hδ' hγ' hne one_pos
      (show 0 < j by omega) (by rw [one_smul, ← heq]; exact hsingle)
    exact h.2
  subst hj1
  rw [one_smul] at heq
  have hroot : IsRoot .E7 (δ + γ) := heq ▸ hsingle
  have hlist := list_eq_singleton_of_isRoot posDef_cartan_E7 hΦ O hδ hγ hne hroot
  intro g hg
  have hsmem : Pi.single i 1 ∈ (RootSystem.ofCartan (e7Datum k).isFiniteType
      (e7Datum k).divisible).roots := by
    change Pi.single i 1 ∈ (e7Datum k).roots
    rw [hroots]; exact hsingle
  obtain ⟨u, rfl⟩ := ((hext.param _ hsmem).1 g).1 hg
  obtain ⟨c, hc⟩ := hunit
  have hform := hC δ hδ γ hγ hne ((c⁻¹ : kˣ) * u) 1
  rw [hlist, List.map_singleton, List.prod_singleton, one_smul, one_smul, ← heq, pow_one,
    pow_one, mul_one, ← hc, ← mul_assoc, Units.mul_inv, one_mul] at hform
  rw [← hform]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)


theorem rootGroupCommutators_e6 : RootGroupCommutators (e6Datum k) := by
  refine .of_divisible_eq_empty rfl fun γ hγ x hx y hy => ?_
  have hpar := e6Datum_isParametrization k
    (RootSystem.ofCartan (e6Datum k).isFiniteType (e6Datum k).divisible)
    (roots_eq isFiniteType_cartan_E6) γ hγ
  obtain ⟨a, rfl⟩ := (hpar.1 x).1 hx
  obtain ⟨b, rfl⟩ := (hpar.1 y).1 hy
  rw [Commute, SemiconjBy, ← hpar.2.1, ← hpar.2.1, add_comm]

theorem nontrivial_e6 : Nontrivial ↥(e6Data_valid.minGroup k) := by
  have hr : (e6Datum k).rank = 6 := rfl
  have hmem : Pi.single (⟨0, by rw [hr]; norm_num⟩ : Fin (e6Datum k).rank) 1 ∈ (e6Datum k).roots :=
    Or.inl ⟨1, ⟨0, by rw [hr]; norm_num⟩, by simp⟩
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    ((e6Datum_steinbergExtras k).ne_bot _ hmem)
  exact nontrivial_of_ne (x : ↥(e6Data_valid.minGroup k)) 1 fun h => hx (Subtype.ext h)

theorem isQuasisimple_e6 : IsQuasisimple ↥(e6Data_valid.minGroup k) := by
  have := nontrivial_e6 k
  exact TitsSimplicity.isQuasisimple (e6Datum_isCTGroupDatum k) (e6Datum_steinbergExtras k)
    (e6Datum_bruhatExtras k) (rootGroupCommutators_e6 k)
    (by change IsIndecomposable (Tag.cartan .E6); decide +kernel) (isPerfect_e6 k)

theorem rootGroupCommutators_e7 : RootGroupCommutators (e7Datum k) := by
  refine .of_divisible_eq_empty rfl fun γ hγ x hx y hy => ?_
  have hpar := e7Datum_isParametrization k
    (RootSystem.ofCartan (e7Datum k).isFiniteType (e7Datum k).divisible)
    (roots_eq isFiniteType_cartan_E7) γ hγ
  obtain ⟨a, rfl⟩ := (hpar.1 x).1 hx
  obtain ⟨b, rfl⟩ := (hpar.1 y).1 hy
  rw [Commute, SemiconjBy, ← hpar.2.1, ← hpar.2.1, add_comm]

theorem nontrivial_e7 : Nontrivial ↥(e7Data_valid.minGroup k) := by
  have hr : (e7Datum k).rank = 7 := rfl
  have hmem : Pi.single (⟨0, by rw [hr]; norm_num⟩ : Fin (e7Datum k).rank) 1 ∈ (e7Datum k).roots :=
    Or.inl ⟨1, ⟨0, by rw [hr]; norm_num⟩, by simp⟩
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    ((e7Datum_steinbergExtras k).ne_bot _ hmem)
  exact nontrivial_of_ne (x : ↥(e7Data_valid.minGroup k)) 1 fun h => hx (Subtype.ext h)

theorem isQuasisimple_e7 : IsQuasisimple ↥(e7Data_valid.minGroup k) := by
  have := nontrivial_e7 k
  exact TitsSimplicity.isQuasisimple (e7Datum_isCTGroupDatum k) (e7Datum_steinbergExtras k)
    (e7Datum_bruhatExtras k) (rootGroupCommutators_e7 k)
    (by change IsIndecomposable (Tag.cartan .E7); decide +kernel) (isPerfect_e7 k)
end CFSG.LieType.CurtisTits
