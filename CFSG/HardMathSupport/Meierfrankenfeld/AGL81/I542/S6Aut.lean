module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsA6
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsA6Perm

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open Equiv

@[expose] def c3A6 : alternatingGroup (Fin 6) :=
  ⟨c[0, 1, 2], by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def c33A6 : alternatingGroup (Fin 6) :=
  ⟨c[0, 1, 2] * c[3, 4, 5], by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] noncomputable def s6Aut : Subgroup (MulAut (alternatingGroup (Fin 6))) := permAut

theorem relIndex_inner_s6Aut :
    ((MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range).relIndex
      s6Aut = 2 :=
  relIndex_inn_permAut

theorem nonempty_s6Aut_equiv : Nonempty (↥s6Aut ≃* Perm (Fin 6)) :=
  ⟨permAutEquiv.symm⟩

theorem mem_s6Aut_iff (σ : MulAut (alternatingGroup (Fin 6))) :
    σ ∈ s6Aut ↔ ∃ g : Perm (Fin 6), MulAut.conjNormal g = σ :=
  Iff.rfl

theorem conj_c3_of_not_mem_s6Aut {σ : MulAut (alternatingGroup (Fin 6))} (hσ : σ ∉ s6Aut) :
    ∃ k : alternatingGroup (Fin 6), σ c3A6 = k * c33A6 * k⁻¹ := by
  rcases mulAut_alt6_cases σ with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact absurd ⟨g, hg.symm⟩ hσ
  · refine ⟨g⁻¹, ?_⟩
    have h1 : g * σ c3A6 * g⁻¹ = c33A6 := Subtype.ext hg
    calc σ c3A6 = g⁻¹ * (g * σ c3A6 * g⁻¹) * g := by group
      _ = g⁻¹ * c33A6 * g⁻¹⁻¹ := by rw [h1, inv_inv]

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
