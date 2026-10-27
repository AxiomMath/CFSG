module

public import CFSG.ClassicalInvolution.Q3.Q3T6DSConf

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

structure AlphaCfg3 (S : Sylow 2 G) (K K' J : Subgroup G) (z t a : G) : Prop where
  hA : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J
  ha1 : a ≠ 1
  ha2 : a * a = 1
  c4 : Concl20_4 S K K' J z
  hyp51 : Hyp51 (Subgroup.closure ({z, t, a} : Set G))

namespace AlphaCfg3

variable (d : Std20Three K K' J S R R' W V z t) {a : G} (h : AlphaCfg3 S K K' J z t a)
include d h

theorem isElemAbelian2_Z : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair d.viol.hzJ.sq d.viol.hzK.sq d.viol.hzJ.ne_one
    d.viol.hzK.ne_one d.late_ne_inv d.late_zt_comm.symm

theorem z_ne_a : z ≠ a := by
  intro e
  apply d.s_a_not_mem_closure h.c4 h.hA h.ha1
  rw [← e]
  exact Subgroup.subset_closure (by simp)

theorem t_ne_a : t ≠ a := by
  intro e
  apply d.s_a_not_mem_closure h.c4 h.hA h.ha1
  rw [← e]
  exact Subgroup.subset_closure (by simp)

theorem isElemAbelian2_za : IsElemAbelian2 (Subgroup.closure ({z, a} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair d.viol.hzK.sq h.ha2 d.viol.hzK.ne_one h.ha1 (h.z_ne_a d)
    (d.s_comm_z h.hA.1.1).symm

theorem isElemAbelian2_ta : IsElemAbelian2 (Subgroup.closure ({t, a} : Set G)) 2 :=
  T7A.isElemAbelian2_closure_pair d.viol.hzJ.sq h.ha2 d.viol.hzJ.ne_one h.ha1 (h.t_ne_a d)
    (d.s_comm_t h.hA).symm

theorem Z_le_B : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, t, a} : Set G) := by
  apply Subgroup.closure_mono
  intro x hx
  rcases hx with rfl | rfl <;> simp

theorem za_le_B : Subgroup.closure ({z, a} : Set G) ≤ Subgroup.closure ({z, t, a} : Set G) := by
  apply Subgroup.closure_mono
  intro x hx
  rcases hx with rfl | rfl <;> simp

theorem ta_le_B : Subgroup.closure ({t, a} : Set G) ≤ Subgroup.closure ({z, t, a} : Set G) := by
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

theorem member_le {L : Subgroup G} (hL : L ∈ CoreAssembly.conjClass K)
    (hzL : IsUniqueInvolution L z) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ k ∈ L, ⁅a, k⁆ ∈ oddCoreOf L) :
    L ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  intro k hk
  obtain ⟨o, hoO, hfix⟩ := T7A.exists_fixed_mul_of_odd (oddCoreOf_odd_natCard L) h.ha2
    (mem_normalizer_oddCore_of_mem_normalizer haL)
    (mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hk)) (hcomm k hk)
  have hkoL : k * o ∈ L := L.mul_mem hk (oddCoreOf_le_self L hoO)
  have hfix' : a * (k * o) = (k * o) * a := mul_inv_eq_iff_eq_mul.mp hfix
  have hz : z * (k * o) = (k * o) * z := hzL.commute_of_mem hkoL
  have hc : k * o ∈
      Subgroup.centralizer ((Subgroup.closure ({z, a} : Set G) : Subgroup G) : Set G) :=
    mem_centralizer_closure_pair hz hfix'
  have h1 := h.cent_le d (h.isElemAbelian2_za d) (h.za_le_B d) hc
  have hKO : oddCoreOf L ≤ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
    Balance.oddCoreIn_le_of_isSubnormal
      (Q3CL.ClassicalClause.isSubnormal_of_uniqueInvolution d.late_cls hL hzL)
  have h2 := h.oddCore_Cz_le d (hKO hoO)
  have h3 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
  rwa [mul_inv_cancel_right] at h3

theorem K_le : K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) :=
  h.member_le d d.late_mem_K d.viol.hzK (d.cent_le_normalizer h.hA.1)
    (fun _ hk => d.s_comm_K h.hA hk)

theorem K'_le : K' ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) :=
  h.member_le d d.late_mem_K' d.late_hzK' (d.cent_le_normalizer' h.hA.1)
    (fun _ hk => d.s_comm_K' h.hA hk)

end AlphaCfg3

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
