module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.AllTypeIKernelPartition
import CFSG.FeitThompson.Representations.TypeISupportingGroupConfiguration
import CFSG.FeitThompson.Representations.SolvableFrobeniusTIKernelsUncovered
import CFSG.FeitThompson.Representations.TISetDadeData

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

theorem FPF_not_all_type_I
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FPF_type_I_frobenius.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u}) :
    _root_.CFSG.FeitThompson.Statements.FPF_not_all_type_I.{u} := by
  intro G _ _ hG
  by_contra hcon
  have hallI : ∀ M : Subgroup G, IsCoatom M → IsTypeI M := by
    intro M hM
    by_contra hM'
    exact hcon ⟨M, hM, hM'⟩
  obtain ⟨k, hk, L, hLco, -, hHne, hfrob, hTI, hcop, -, -, hunion⟩ :=
    FPF_all_type_I_kernel_partition h₁ h₂ h₃ h₄ h₅ h₆ G hG hallI
  choose E _hEle hEne hsd hfree using hfrob
  set H : Fin k → Subgroup G := fun i => hallCoreOf (L i)
  have hsolv : ∀ i, Group.IsSolvable ↥(H i) := by
    intro i
    refine hG.isSolvable_of_ne_top (H i) fun hHtop => ?_
    exact (hLco i).1 (top_le_iff.1 (hHtop ▸ hallCoreOf_le (L i)))
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hstab : ∀ (i : Fin k) (g : G),
      (fun x => g⁻¹ * x * g) '' ((H i : Set G) \ {1}) = (H i : Set G) \ {1} ↔ g ∈ L i := by
    intro i g
    rw [← mem_normalizer_iff_conjInv_image_eq, (hTI i).normalizer_eq]
  have hTIor : ∀ (i : Fin k) (g : G),
      (fun x => g⁻¹ * x * g) '' ((H i : Set G) \ {1}) = (H i : Set G) \ {1} ∨
        (fun x => g⁻¹ * x * g) '' ((H i : Set G) \ {1}) ∩ ((H i : Set G) \ {1}) = ∅ := by
    intro i g
    by_cases hg : g ∈ L i
    · exact Or.inl ((hstab i g).2 hg)
    · refine Or.inr ?_
      have hd := (hTI i).disjoint_image_conj_inv hg
      rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm] at hd
      exact hd
  obtain ⟨x, hx1, hx⟩ :=
    FrobeniusMultipleKernel.exists_ne_one_notMem_conj_image (G := G) (I := Fin k)
      (L := L) (H := H) (E := E) hG.odd_natCard
      (fun i => (hsd i).le_normalizer)
      (fun i => ((hsd i).coe_eq_mul).symm)
      (fun i => (hsd i).inf_eq_bot)
      hHne hEne
      (fun i u hu hu1 =>
        inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn (hfree i) hu hu1)
      hstab hTIor (fun i j hij => hcop i j hij)
  have hxmem : x ∈ Set.univ \ ({1} : Set G) := ⟨Set.mem_univ x, by simpa using hx1⟩
  rw [← hunion] at hxmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hxmem
  simp only [conjClosure, Prep05.conjSet, Set.mem_iUnion] at hi
  obtain ⟨g, hg⟩ := hi
  exact hx i g hg

end

end CFSG.FeitThompson.Proofs
