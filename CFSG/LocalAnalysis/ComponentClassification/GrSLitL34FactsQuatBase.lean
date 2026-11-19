
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Subgroup

def Q8 : Subgroup (Equiv.Perm (Fin 42)) := centralizer {r₄} ⊓ T0

theorem mem_Q8 {t : Equiv.Perm (Fin 42)} : t ∈ Q8 ↔ t * r₄ = r₄ * t ∧ t ∈ T0 := by
  rw [Q8, mem_inf, mem_centralizer_singleton_iff]

theorem Q8_le_T0 : Q8 ≤ T0 := inf_le_right

theorem lt_of_mem_q8Idx : ∀ k ∈ q8Idx, k < 64 := by decide

theorem tg_zero : tg 0 = [] := by decide

theorem wordPerm_tg_zero : wordPerm (tg 0) = 1 := by
  rw [tg_zero]
  rfl

private theorem q8_invol_idx :
    ∀ k ∈ q8Idx, (k == 0 || (sqData.map (·.1)).contains k) = true → k = 0 ∨ k = 4 := by
  decide

theorem not_isCyclic_of_ne {G : Type*} [Group G] {H : Subgroup G} {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) (hab : a * b ≠ b * a) : ¬ IsCyclic H := by
  intro hcyc
  have hcomm := (MonoidHom.id H).isMulCommutative_of_isCyclic_of_ker_le_center (by
    rw [MonoidHom.ker_id]
    exact bot_le)
  have h := congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
  exact hab h

end CFSG.ComponentClassification.GrSLit.L34Facts
