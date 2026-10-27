module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Prep06

universe u

variable {G : Type u} [Group G]

theorem inf_sup_eq_of_disjoint_of_le_normalizer {H U A : Subgroup G}
    (hHU : Disjoint H U) (hA : A ≤ U) (hn : A ≤ normalizer (H : Set G)) :
    U ⊓ (H ⊔ A) = A := by
  refine le_antisymm ?_ (le_inf hA le_sup_right)
  intro x hx
  obtain ⟨hxU, hxHA⟩ := hx
  have hmem : x ∈ ((H ⊔ A : Subgroup G) : Set G) := hxHA
  rw [Subgroup.coe_mul_of_right_le_normalizer_left H A hn] at hmem
  obtain ⟨h, hh, a, ha, rfl⟩ := hmem
  have hhU : h ∈ U := by
    have he : h = h * a * a⁻¹ := by group
    rw [he]
    exact U.mul_mem hxU (U.inv_mem (hA ha))
  have h1 : h = 1 := Subgroup.disjoint_def.1 hHU hh hhU
  simpa [h1] using ha

theorem commutator_le_sup_commutator_of_sup {K H U : Subgroup G}
    (hH : H ≤ K) (hU : U ≤ K) (hsup : H ⊔ U = K)
    (hn : K ≤ normalizer (H : Set G)) :
    ⁅K, K⁆ ≤ H ⊔ ⁅U, U⁆ := by
  have hnorm : (H.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH).2 hn
  have hsup' : H.subgroupOf K ⊔ U.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hH hU, hsup, Subgroup.subgroupOf_self]
  have h := CFSG.FeitThompson.commutator_le_sup_commutator hnorm hsup'
  have h2 := Subgroup.map_mono (f := K.subtype) h
  rwa [Subgroup.map_subtype_commutator, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hH, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hU] at h2

theorem FPF_type_iii_iv_core_centralizer_derived
    (h₁ : Statements.FPF_type_iii_iv_second_derived_fitting.{u}) :
    Statements.FPF_type_iii_iv_core_centralizer_derived.{u} := by
  intro G _ _ hG M U W₁ W₂ hM hMtype hc
  obtain ⟨hK', hHC, -, -⟩ := h₁ G hG M U W₁ W₂ hM hMtype hc
  rw [hallCoreIn_eq] at hHC ⊢
  set H : Subgroup G := (hallCore ↥M).map M.subtype with hHdef
  set C : Subgroup G := U ⊓ centralizer (H : Set G) with hCdef
  have hHCK : H ⊔ C = ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ := by
    rw [hHC, hK']
  have hUK : U ≤ (⁅M, M⁆ : Subgroup G) := hc.le_commutator_E
  have hHK : H ≤ (⁅M, M⁆ : Subgroup G) := hc.hallCore_le_commutator
  have hnK : (⁅M, M⁆ : Subgroup G) ≤ normalizer (H : Set G) :=
    commutator_le_normalizer_hallCore M
  have hdisj : Disjoint H U := hc.disjoint_hallCore_E
  refine le_antisymm ?_ ?_
  ·
    have hkey : ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ H ⊔ ⁅U, U⁆ :=
      commutator_le_sup_commutator_of_sup hHK hUK hc.sup_hallCore_E hnK
    have hC : C ≤ U ⊓ (H ⊔ ⁅U, U⁆) :=
      le_inf inf_le_left ((le_sup_right.trans hHCK.le).trans hkey)
    refine hC.trans (le_of_eq ?_)
    exact inf_sup_eq_of_disjoint_of_le_normalizer hdisj
      (Subgroup.commutator_le_self U) (((Subgroup.commutator_le_self U).trans hUK).trans hnK)
  ·
    have hC : ⁅U, U⁆ ≤ U ⊓ (H ⊔ C) :=
      le_inf (Subgroup.commutator_le_self U)
        (hHCK ▸ Subgroup.commutator_mono hUK hUK)
    refine hC.trans (le_of_eq ?_)
    exact inf_sup_eq_of_disjoint_of_le_normalizer hdisj inf_le_left
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))

end

end CFSG.FeitThompson.Proofs
