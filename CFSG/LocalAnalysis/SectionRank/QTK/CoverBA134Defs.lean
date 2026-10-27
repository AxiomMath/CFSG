module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup

@[expose] def RealLocalElement (S : Type) [Group S] (r : ℕ) : Prop :=
  ∃ R : Subgroup S, R ≠ ⊥ ∧ IsPGroup 2 R ∧
    ∃ x ∈ normalizer (R : Set S), orderOf x = r ∧ ∃ d : S, d * x * d⁻¹ = x⁻¹

variable {S T : Type} [Group S] [Group T]

theorem RealLocalElement.of_mulEquiv (e : S ≃* T) {r : ℕ} (h : RealLocalElement T r) :
    RealLocalElement S r := by
  obtain ⟨R, hR, hR2, x, hxN, hx, d, hd⟩ := h
  refine ⟨R.map e.symm.toMonoidHom, fun h0 => hR ?_, hR2.map _, e.symm x, ?_,
    by rw [MulEquiv.orderOf_eq, hx], e.symm d, by rw [← map_inv, ← map_mul, ← map_mul, hd,
      map_inv]⟩
  · exact (map_eq_bot_iff_of_injective _ e.symm.injective).mp h0
  · rw [← map_equiv_normalizer_eq]
    exact mem_map_of_mem _ hxN

end CFSG.SectionRank.QTK.CoverB
