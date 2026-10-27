module

public import CFSG.Open.LocalVocabulary
import CFSG.Assembly.Defs
import CFSG.Holt.General.NoRelevantBasic

public section

namespace CFSG.Holt.General

open MulAction Subgroup

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {z : G} {α : Ω}

theorem faithfulSMul_of_ker_eq_bot (hK : (toPermHom G Ω).ker = ⊥) : FaithfulSMul G Ω := by
  refine ⟨fun {x y} h => ?_⟩
  have hmem : x⁻¹ * y ∈ (toPermHom G Ω).ker := by
    rw [MonoidHom.mem_ker]
    ext ω
    change (x⁻¹ * y) • ω = ω
    rw [mul_smul, ← h ω, inv_smul_smul]
  rw [hK, mem_bot, inv_mul_eq_one] at hmem
  exact hmem

end CFSG.Holt.General
