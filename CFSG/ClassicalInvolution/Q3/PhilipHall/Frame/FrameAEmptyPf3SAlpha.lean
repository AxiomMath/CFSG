module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3SConf

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

structure AlphaCfgF (S : Sylow 2 G) (K K' J : Subgroup G) (z t a : G) : Prop where
  hA : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J
  ha1 : a ≠ 1
  ha2 : a * a = 1
  c4 : Concl20_4 S K K' J z
  hyp51 : Hyp51 (Subgroup.closure ({z, t, a} : Set G))

namespace AlphaCfgF

variable (d : Std20Frame K K' J S R R' W V z t) {a : G} (h : AlphaCfgF S K K' J z t a)
include d h

theorem isElemAbelian2_Z : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair d.viol.hzJ.sq d.viol.hzK.sq d.viol.hzJ.ne_one
    d.viol.hzK.ne_one d.late_ne_inv d.late_zt_comm.symm

theorem z_ne_a : z ≠ a := by
  intro e
  apply d.s_a_not_mem_closure h.c4 h.hA h.ha1
  rw [← e]
  exact Subgroup.subset_closure (by simp)

theorem isElemAbelian2_za : IsElemAbelian2 (Subgroup.closure ({z, a} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair d.viol.hzK.sq h.ha2 d.viol.hzK.ne_one h.ha1 (h.z_ne_a d)
    (d.s_comm_z h.hA.1.1).symm

theorem Z_le_B : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, t, a} : Set G) := by
  apply Subgroup.closure_mono
  intro x hx
  rcases hx with rfl | rfl <;> simp

theorem za_le_B : Subgroup.closure ({z, a} : Set G) ≤ Subgroup.closure ({z, t, a} : Set G) := by
  apply Subgroup.closure_mono
  intro x hx
  rcases hx with rfl | rfl <;> simp

theorem alpha_facts :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({t, z} : Set G)))) ∧
      ∀ A : Subgroup G, A ≤ Subgroup.closure ({z, t, a} : Set G) → IsElemAbelian2 A 2 →
        alphaOf A = alphaOf (Subgroup.closure ({t, z} : Set G)) :=
  lemma54_odd_and_eq h.hyp51 (h.Z_le_B d) (h.isElemAbelian2_Z d)

theorem cent_le {E : Subgroup G} (hE : IsElemAbelian2 E 2)
    (hEB : E ≤ Subgroup.closure ({z, t, a} : Set G)) :
    Subgroup.centralizer (E : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) :=
  T7A.centralizer_le_normalizer_alpha hE hEB (h.alpha_facts d).2

theorem B_le_Cz : Subgroup.closure ({z, t, a} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr d.late_zt_comm.symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (d.s_comm_z h.hA.1.1)

theorem oddCore_Cz_le :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) :=
  T7A.oddCore_le_normalizer_alpha (d.s_B_isElemAbelian h.hA h.ha2)
    (d.s_B_natCard h.c4 h.hA h.ha1 h.ha2) (h.B_le_Cz d) (h.alpha_facts d).2

end AlphaCfgF

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
