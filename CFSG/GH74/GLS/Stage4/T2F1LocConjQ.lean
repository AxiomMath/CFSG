module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open Subgroup CFSG

theorem conj_mem_centralizer_conj_iff {G : Type*} [Group G] (f c x : G) :
    c * x * c⁻¹ ∈ centralizer ({c * f * c⁻¹} : Set G) ↔ x ∈ centralizer ({f} : Set G) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  have h1 : c * x * c⁻¹ * (c * f * c⁻¹) = c * (x * f) * c⁻¹ := by group
  have h2 : c * f * c⁻¹ * (c * x * c⁻¹) = c * (f * x) * c⁻¹ := by group
  rw [h1, h2]
  exact ⟨fun h => mul_left_cancel (mul_right_cancel h), fun h => by rw [h]⟩

@[expose] def conjCentralizerEquiv {G : Type*} [Group G] (f c : G) :
    ↥(centralizer ({f} : Set G)) ≃* ↥(centralizer ({c * f * c⁻¹} : Set G)) where
  toFun x := ⟨c * x * c⁻¹, (conj_mem_centralizer_conj_iff f c x).2 x.2⟩
  invFun y := ⟨c⁻¹ * y * c, (conj_mem_centralizer_conj_iff f c (c⁻¹ * y * c)).1
    (by simpa [mul_assoc] using y.2)⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

theorem exists_quot_equiv_of_conj {G : Type} [Group G] [Finite G] (f c : G) :
    ∃ e : (↥(Subgroup.centralizer ({f} : Set G)) ⧸ pPrimeCore 2 ↥(Subgroup.centralizer ({f} : Set G))) ≃*
        (↥(Subgroup.centralizer ({c * f * c⁻¹} : Set G)) ⧸
          pPrimeCore 2 ↥(Subgroup.centralizer ({c * f * c⁻¹} : Set G))),
      ∀ (x : G) (hx : x ∈ Subgroup.centralizer ({f} : Set G))
        (hx' : c * x * c⁻¹ ∈ Subgroup.centralizer ({c * f * c⁻¹} : Set G)),
        e (QuotientGroup.mk (⟨x, hx⟩ : ↥(Subgroup.centralizer ({f} : Set G)))) =
          QuotientGroup.mk (⟨c * x * c⁻¹, hx'⟩ : ↥(Subgroup.centralizer ({c * f * c⁻¹} : Set G))) :=
  ⟨QuotientGroup.congr _ _ (conjCentralizerEquiv f c)
    (pPrimeCore_map_iso 2 (conjCentralizerEquiv f c)), fun _ _ _ => rfl⟩

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
