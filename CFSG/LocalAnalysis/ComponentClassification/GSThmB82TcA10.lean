module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10SideA6
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.A10Side

namespace A10Side

theorem isSymSixType_mul_of_not {Q : Type*} [Group Q] (e : Q ≃* alternatingGroup (Fin 6))
    {φ ψ : MulAut Q} (hφ : ¬ IsSymSixType e φ) (hψ : ¬ IsSymSixType e ψ) :
    IsSymSixType e (φ * ψ) := by
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6
    (by norm_num)
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (MulAut (alternatingGroup (Fin 6))),
      H = (MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
        Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := ⟨_, rfl⟩
  have hmem : ∀ χ : MulAut Q, IsSymSixType e χ ↔ MulAut.congr e χ ∈ H := by
    intro χ
    rw [hH, MonoidHom.mem_range]
    exact ⟨fun ⟨σ, hσ⟩ => ⟨σ, hσ.symm⟩, fun ⟨σ, hσ⟩ => ⟨σ, hσ.symm⟩⟩
  have hcard : Nat.card H = 720 := by
    rw [hH, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have : Finite (MulAut (alternatingGroup (Fin 6))) := MulEquiv.finite_left
  have hle := CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
  have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
  have hmul := H.card_mul_index
  rw [hcard] at hmul
  have h1 : H.index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    apply hφ
    rw [hmem, h1]
    exact mem_top _
  have hidx : H.index = 2 := by omega
  rw [hmem, map_mul]
  exact (Subgroup.mul_mem_iff_of_index_two hidx).mpr
    (iff_of_false ((hmem φ).not.mp hφ) ((hmem ψ).not.mp hψ))

end A10Side

end CFSG.ComponentClassification.GSThmB
