module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubHypW

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise commutatorElement

namespace Hyp52W

variable {H : Type} [Group H] [Finite H] (h : Hyp52W H)

theorem le_coreActionKernel_of_ne {L : Subgroup H} (hL : L ≤ centralizer ({h.a} : Set H))
    (hLp : IsPComponent 2 (L.subgroupOf (centralizer ({h.a} : Set H)))) (hLJ : L ≠ h.J) :
    L ≤ coreActionKernel h.J := by
  set C := centralizer ({h.a} : Set H) with hC
  have hne : h.J.subgroupOf C ≠ L.subgroupOf C := by
    intro he
    rw [subgroupOf_inj, inf_of_le_left h.J_le, inf_of_le_left hL] at he
    exact hLJ he.symm
  obtain ⟨-, hdist⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
    Nat.prime_two _ _ h.isPComponent_J hLp
  obtain ⟨hLN, -, hcomm, -⟩ := hdist hne
  have hcore := CFSG.pPrimeCore_map_subgroupOf 2 h.J C h.J_le
  intro l hl
  have hlC : l ∈ C := hL hl
  refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
  · rw [mem_normalizer_iff]
    intro y
    have h1 := hLN (show (⟨l, hlC⟩ : C) ∈ L.subgroupOf C from hl)
    constructor
    · intro hy
      have hyC : y ∈ C := h.J_le hy
      have h2 := (mem_normalizer_iff.mp h1 ⟨y, hyC⟩).mp hy
      exact h2
    · intro hy
      have hyC : l * y * l⁻¹ ∈ C := h.J_le hy
      have hyC' : y ∈ C := by
        have := mul_mem (mul_mem (inv_mem hlC) hyC) hlC
        simpa [mul_assoc] using this
      have h2 := (mem_normalizer_iff.mp h1 ⟨y, hyC'⟩).mpr hy
      exact h2
  · have hjC : j ∈ C := h.J_le hj
    have h1 : ⁅(⟨j, hjC⟩ : C)⁻¹, (⟨l, hlC⟩ : C)⁻¹⁆ ∈ ⁅h.J.subgroupOf C, L.subgroupOf C⁆ :=
      Subgroup.commutator_mem_commutator (inv_mem (show (⟨j, hjC⟩ : C) ∈ h.J.subgroupOf C
        from hj)) (inv_mem (show (⟨l, hlC⟩ : C) ∈ L.subgroupOf C from hl))
    have h2 := (hcomm h1).1
    rw [← hcore]
    refine ⟨_, h2, ?_⟩
    simp only [subtype_apply, commutatorElement_def, coe_mul, coe_inv, inv_inv]

abbrev N0 : Subgroup H := centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)

end Hyp52W

end CFSG.ComponentClassification.GSThmB
