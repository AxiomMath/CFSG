module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.Goldschmidt.Steps.G3bPSL2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.L2AutAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GorensteinWalter
open scoped commutatorElement

universe u

theorem l2aut_comm
    {M : Type*} [Group M] {F : Type u} [Field F] [Finite F] (e : M ≃* PSL2 F)
    (h5 : 5 ≤ Nat.card F) (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) (S : Sylow 2 M)
    {α β : MulAut M} (hα : ∀ x ∈ (S : Subgroup M), α x = x)
    (hβ : ∀ x ∈ (S : Subgroup M), β x = x) : α * β = β * α := by
  refine l2aut_reduce e h5 h8 ?_
  intro p f _ hp hf h5' h8' e'
  haveI : Finite M := Finite.of_equiv _ e'.symm.toEquiv
  exact (CFSG.Goldschmidt.G3b.mulAut_fix_props_of_mulEquiv e' hp hf h5' h8' S).1 α β hα hβ

theorem l2aut_commutator_acts_trivially
    {M : Type*} [Group M] {F : Type u} [Field F] [Finite F] (e : M ≃* PSL2 F)
    (h5 : 5 ≤ Nat.card F) (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) (S : Sylow 2 M)
    {C : Type*} [Group C] (ρ : C →* MulAut M) {D : Subgroup C}
    (hD : ∀ d ∈ D, ∀ x ∈ (S : Subgroup M), ρ d x = x) : ⁅D, D⁆ ≤ ρ.ker := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact l2aut_comm e h5 h8 S (hD a ha) (hD b hb)

theorem l2aut_odd_eq_one
    {M : Type*} [Group M] {F : Type u} [Field F] [Finite F] (e : M ≃* PSL2 F)
    (h5 : 5 ≤ Nat.card F) (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    {α : MulAut M} (hα : Odd (orderOf α)) {u : M} (hu : orderOf u = 2)
    (hfix : ∀ x ∈ Subgroup.centralizer ({u} : Set M), α x = x) : α = 1 := by
  refine l2aut_reduce e h5 h8 ?_
  intro p f _ hp hf h5' h8' e'
  exact l2aut_gf_odd_eq_one_of_equiv hp hf h5' h8' e' hα hu hfix

theorem l2aut_action_odd_trivial
    {M : Type*} [Group M] {F : Type u} [Field F] [Finite F] (e : M ≃* PSL2 F)
    (h5 : 5 ≤ Nat.card F) (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    {C : Type*} [Group C] (ρ : C →* MulAut M) {c : C} (hc : Odd (orderOf c)) {u : M}
    (hu : orderOf u = 2) (hfix : ∀ x ∈ Subgroup.centralizer ({u} : Set M), ρ c x = x) :
    ρ c = 1 :=
  l2aut_odd_eq_one e h5 h8 (Odd.of_dvd_nat hc (orderOf_map_dvd ρ c)) hu hfix

end CFSG.OddStandard.SmallF3.Omega
