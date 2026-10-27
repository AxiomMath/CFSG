module

public import Certificates.Certificate22600
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert

namespace SCert.SE

theorem exists_conj_invRep (s : SE) (hs : s * s = 1)
    (hs1 : s ≠ 1) : ∃ i : Fin 9, ∃ g : SE, g⁻¹ * s * g = invRep i :=
  Certificates.certificate22600.1 s hs hs1

theorem mem_center_iff (s : SE) :
    (∀ g : SE, g * s = s * g) ↔ s = 1 ∨ s = gen 0 := by
  refine ⟨Certificates.certificate22600.2.2 s, ?_⟩
  rintro (rfl | rfl)
  · intro g
    simp
  · decide +kernel

theorem card_filter_comm_invRep : ∀ i : Fin 9,
    (Finset.univ.filter (fun g : SE => g * invRep i = invRep i * g)).card = invRepCent i := by
  decide +kernel

theorem card_centralizer_invRep (i : Fin 9) :
    Nat.card (centralizer ({invRep i} : Set SE)) = invRepCent i := by
  classical
  rw [← card_filter_comm_invRep i, Nat.card_eq_fintype_card, ← Fintype.card_coe]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [mem_centralizer_singleton_iff, Finset.mem_filter]
  exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩

end SCert.SE

end CFSG.ComponentClassification.GHarris
