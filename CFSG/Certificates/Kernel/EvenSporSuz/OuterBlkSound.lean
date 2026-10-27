module

public import CFSG.Certificates.Kernel.EvenSporSuz.Sound
public import Certificates.Data.Kernel.EvenSporSuz.OuterBlk

public section

namespace CFSG.KC.EvenSporSuz

open CFSG.EvenSporadicStandard.TwoSuz

theorem outerSub_canon (G : GenSys) (n : ℕ) (w : ℕ → List ℤ) : CanonGS (G.outerSub n w) := by
  refine ⟨canonB_getD fun x hx => ?_, canonB_getD fun x hx => ?_⟩
  · simp only [GenSys.outerSub, Array.mem_map] at hx
    obtain ⟨s, -, rfl⟩ := hx
    exact canonB_eval _ _
  · simp only [GenSys.outerSub, Array.mem_map] at hx
    obtain ⟨s, -, rfl⟩ := hx
    exact canonB_eval _ _

theorem outerSub_mats {G : GenSys} (hG : CanonGS G) (n : ℕ) (w : ℕ → List ℤ) :
    (G.outerSub n w).mats.toList.map rowsOf =
      subR (G.mats.toList.map rowsOf) (G.invs.toList.map rowsOf) n w := by
  unfold GenSys.outerSub subR
  simp only [Array.toList_map, Array.toList_range, List.map_map]
  refine List.map_congr_left fun s _ => ?_
  exact rowsOf_eval hG _

theorem outerSub_invs {G : GenSys} (hG : CanonGS G) (n : ℕ) (w : ℕ → List ℤ) :
    (G.outerSub n w).invs.toList.map rowsOf =
      subRI (G.mats.toList.map rowsOf) (G.invs.toList.map rowsOf) n w := by
  unfold GenSys.outerSub subRI
  simp only [Array.toList_map, Array.toList_range, List.map_map]
  refine List.map_congr_left fun s _ => ?_
  exact rowsOf_eval hG _

theorem parseBlock_eq (ws : List (List ℤ)) (p K M : ℕ) (h : ws.getD p [] = [(K : ℤ), (M : ℤ)]) :
    outerParseBlock ws.toArray p = (blockW ws p K M, p + 2 + 2 * K + 2 * M) := by
  have hg : ∀ i, ws.toArray.getD i [] = ws.getD i [] := fun i => by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  have hK : ((ws.getD p []).getD 0 0).toNat = K := by
    rw [h]
    simp
  have hM : ((ws.getD p []).getD 1 0).toNat = M := by
    rw [h]
    simp
  unfold outerParseBlock
  simp only [hg, hK, hM]
  rfl

end CFSG.KC.EvenSporSuz
