module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecEdge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtU
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open scoped commutatorElement

section UVertex

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t₀ : G} {n : ℕ}
  {K K' J : Subgroup G} {z u t : G}

theorem u_cm (h : TwinCoreHyp n G R S t₀) (hRc : tightCore R = R)
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t)
    (hum : u ∈ centralizerModOdd ⊤ J) {c : G}
    (hc : c = u ∨ c = z * u ∨ c = u * t ∨ c = z * u * t) :
    c ∈ centralizerModOdd ⊤ J ∧ c * c = 1 ∧ c ≠ 1 := by
  obtain ⟨SJ, hJd⟩ := exists_datum_at h hRc hf.hJ.1 hf.ht
  have hRcJ : tightCore J = J := tightCore_eq_of_mem hRc hf.hJ.1
  have hΩ := h.hyp
  have hKe : K ∈ omegaNbr (CoreAssembly.conjClass (tightCore J)) (tightCore J) := by
    rw [hRcJ, conjClass_eq_of_mem hf.hJ.1]
    exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hf.mem hf.hJ.1
      (hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz))
  obtain ⟨hz2, -, hzm⟩ := edge_involution hJd.datum hRcJ hJd.hyp hKe hf.hz hf.t_ne_z.symm
  have htm : t ∈ centralizerModOdd ⊤ J :=
    mem_centralizerModOdd_of_commutator hf.ht.sq fun r hr => by
      have : r * t = t * r := Subgroup.mem_centralizer_singleton_iff.mp (hJd.datum.cent hr)
      have h1 : ⁅t, r⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact this.symm
      rw [h1]
      exact Subgroup.one_mem _
  obtain ⟨hcB, hc1, -, -, -, -⟩ := ucoset_facts hΩ hf hc
  have hcm : c ∈ centralizerModOdd ⊤ J := by
    rcases hc with rfl | rfl | rfl | rfl
    · exact hum
    · exact Subgroup.mul_mem _ hzm hum
    · exact Subgroup.mul_mem _ hum htm
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hzm hum) htm
  have hB := TwinFrame.isElemAbelian_of_frameData hΩ hf
  exact ⟨hcm, (sq c).symm.trans (hB.2 c hcB), hc1⟩

end UVertex

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf3
