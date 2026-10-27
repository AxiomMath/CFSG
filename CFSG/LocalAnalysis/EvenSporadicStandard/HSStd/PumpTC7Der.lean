module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem commutator_mem_inner_alt6 (α β : MulAut (alternatingGroup (Fin 6))) :
    ⁅α, β⁆ ∈ inner (alternatingGroup (Fin 6)) := by
  have hcomm :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_commutative
  have h : (QuotientGroup.mk ⁅α, β⁆ : Outer (alternatingGroup (Fin 6))) = 1 := by
    change (QuotientGroup.mk' (inner (alternatingGroup (Fin 6)))) ⁅α, β⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm.is_comm.comm _ _)
  exact (QuotientGroup.eq_one_iff _).1 h

theorem card_centralizer_commutator_le {Γ : Type*} [Group Γ] [Finite Γ] {C : Subgroup Γ}
    (e : ↥C ≃* Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :
    Nat.card ↥C = 2880 ∧ Nat.card ↥⁅C, C⁆ ≤ 360 := by
  have hAut := CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6
  have hC : Nat.card ↥C = 2880 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hAut]
    have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    rw [this]
  refine ⟨hC, ?_⟩
  set I := inner (alternatingGroup (Fin 6)) with hI
  have hIcard : Nat.card I = 360 :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_card
  set B : Subgroup (Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) :=
    (⊥ : Subgroup (Multiplicative (ZMod 2))).prod I with hB
  have hBcard : Nat.card B = 360 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hIcard]
    simp
  have hmem : ∀ g h : Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)),
      ⁅g, h⁆ ∈ B := by
    intro g h
    refine ⟨?_, ?_⟩
    · show ⁅g, h⁆.1 ∈ (⊥ : Subgroup (Multiplicative (ZMod 2)))
      rw [Subgroup.mem_bot]
      simp only [commutatorElement_def, Prod.fst_mul, Prod.fst_inv]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
    · exact commutator_mem_inner_alt6 g.2 h.2
  have hKC : ⁅C, C⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    exact C.mul_mem (C.mul_mem (C.mul_mem hg hh) (C.inv_mem hg)) (C.inv_mem hh)
  have hle : ⁅C, C⁆ ≤ (B.comap (e : ↥C →* _)).map C.subtype := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    refine ⟨⁅(⟨g, hg⟩ : ↥C), (⟨h, hh⟩ : ↥C)⁆, ?_, ?_⟩
    · show (e : ↥C →* _) ⁅(⟨g, hg⟩ : ↥C), (⟨h, hh⟩ : ↥C)⁆ ∈ B
      rw [map_commutatorElement]
      exact hmem _ _
    · simp [commutatorElement_def]
  calc Nat.card ↥⁅C, C⁆ ≤ Nat.card ↥((B.comap (e : ↥C →* _)).map C.subtype) :=
        Subgroup.card_le_of_le hle
    _ = Nat.card ↥(B.comap (e : ↥C →* _)) := Subgroup.card_map_of_injective C.subtype_injective
    _ = Nat.card B := by
        rw [Subgroup.comap_equiv_eq_map_symm, Subgroup.card_map_of_injective e.symm.injective]
    _ = 360 := hBcard

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
