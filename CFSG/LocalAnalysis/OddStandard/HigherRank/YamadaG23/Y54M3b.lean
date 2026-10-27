module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Spl
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54M3a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y54_C3_eq_M {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) : C3 c.s = M ⊔ zpowers c.s.t := by
  rw [y54_C3_eq (c := c) hH]
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · exact (y54_YN_le (c := c) hH hM).trans le_sup_left
    · exact sup_le (hM.1.trans le_sup_left) le_sup_right
  · refine sup_le ?_ ?_
    · refine (y54_M_le_YN (c := c) hH hM).trans ?_
      exact sup_le_sup le_rfl le_sup_left
    · calc zpowers c.s.t ≤ f4P c.s := le_sup_right
        _ ≤ ⁅f4Y c.s, f4N c.s⁆ ⊔ f4P c.s := le_sup_right

theorem y54_M3_eq {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsM3Cand c.s M) : M3 c.s = M := by
  have htY : c.s.t ∈ f4Y c.s :=
    y54_X0_le_Y (s := c.s) (e := c.e) hH
      (y54_P_le_X0 (s := c.s) (e := c.e) hH
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)))
  have hC3le : C3 c.s ≤ f4Y c.s := by
    rw [y54_C3_eq_M (c := c) hH hM]
    exact sup_le hM.2.1 (Subgroup.zpowers_le.mpr htY)
  have hMle : M ≤ C3 c.s := by
    rw [y54_C3_eq_M (c := c) hH hM]
    exact le_sup_left
  rw [M3]
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ hM.1
    exact (Subgroup.commutator_mono hC3le (y54_NL_le_N (s := c.s) (e := c.e) hH)).trans
      (y54_YN_le (c := c) hH hM)
  · calc M = ⁅M, normIn L c.s.fr.F⁆ ⊔ c.s.fr.F := (y54_M_comm_eq (c := c) hH hM).symm
      _ ≤ ⁅C3 c.s, normIn L c.s.fr.F⁆ ⊔ c.s.fr.F :=
            sup_le ((Subgroup.commutator_mono_left hMle).trans le_sup_left) le_sup_right

theorem y54_M3_cand (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : IsM3Cand c.s (M3 c.s) := by
  obtain ⟨M, hM⟩ := y54_M_exists c hH
  rw [y54_M3_eq (c := c) hH hM]
  exact hM

theorem y54_C3_eq_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    C3 c.s = M3 c.s ⊔ zpowers c.s.t := by
  obtain ⟨M, hM⟩ := y54_M_exists c hH
  rw [y54_M3_eq (c := c) hH hM]
  exact y54_C3_eq_M (c := c) hH hM

end CFSG.OddStandard.HigherRank.YamadaG23
