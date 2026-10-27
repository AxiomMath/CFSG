module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf3Vtx
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtNbr

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open scoped commutatorElement

section Nbr

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t₀ : G} {n : ℕ}
  {K K' J : Subgroup G} {z u t : G}

theorem hyp51At_nbr_new3 (hSp : ModelFactSp62) (hD4m : ModelFactD42) (hM12 : ModelFactM12)
    (h4 : Thm4RTwinBelow 3 n)
    (h : TwinCoreHyp n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    (hD4 : TL4.D4OddAutInnerNC3)
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t) {c : G}
    (hc : c = t ∨ c = z * t) :
    Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
  have hΩ := h.hyp
  have hBelow : CIT3Below (Nat.card G) := h.card ▸ h.below
  have hB := TwinFrame.isElemAbelian_of_frameData hΩ hf
  have hzB := TwinFrame.z_mem z u t
  have htB := TwinFrame.t_mem z u t
  have hcB : c ∈ Subgroup.closure ({z, u, t} : Set G) := by
    rcases hc with rfl | rfl
    · exact htB
    · exact Subgroup.mul_mem _ hzB htB
  have hzc := Lemma52Proof.le_centralizer_of_mem hB hcB hzB
  have hc1 : c ≠ 1 := by
    rcases hc with rfl | rfl
    · exact hf.ht.ne_one
    · exact TwinFrame.zt_ne_one hf
  have hac : z ≠ c := by
    rcases hc with rfl | rfl
    · exact hf.t_ne_z.symm
    · intro e
      have : t = 1 := by
        have h1 : z * t = z * 1 := by rw [mul_one]; exact e.symm
        exact mul_left_cancel h1
      exact hf.ht.ne_one this
  have htK := edge_mem_centralizerModOdd h hRc hf.mem hf.hz
    (hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz)) hf.ht hf.t_ne_z
  have htK' := edge_mem_centralizerModOdd h hRc hf.hK'.1
    (isUniqueInvolution_of_mem_twinSet hf.hz hf.hK') (hf.hJ.2 K' hf.hK') hf.ht hf.t_ne_z
  have hquiet : Quiet c z hzc → Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := fun hq =>
    TwinFrame.hyp51At_of_classicalOrQuiet_model hBelow hZ hB hzB hcB hc1 hf.hz.ne_one hac hzc
      hq.classicalOrQuiet (fun L hL hm => (moved_false_of_quiet hB hzB hcB hc1 hf.hz.ne_one hac hzc
        hq hL hm).elim)
  have hlifted : (LiftedAt K c z ∧ LiftedAt K' c z) →
      Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := fun hl =>
    TwinFrame.hyp51At_nbr hBelow hZ hD4 hΩ hf hc (fun hzc' => hl.1.classicalOrQuiet hzc')
      (fun L hL hm huc => ubar_mem_of_lifted h hZ hf htK htK' hc hzc hl.1 hl.2 hL hm huc)
  have hexit : ∀ {M : Subgroup G}, ExitAt M c z hzc → MovedOddFreeAt c z hzc →
      Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := fun he hm =>
    hyp51At_of_autOddFree hB hzB hcB hc1 hf.hz.ne_one hac hzc hm.1 fun L hL hmv =>
      he.autOddFree hSp hD4m hM12 hL
        (hmv _ (oddQuotMk_mem_modOdd hzB hzc)
          (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hzB hf.hz.ne_one hac hzc))
  rcases TwinExitPf3.nbr_out3 hSp hD4m h4 h hRc hZ hf hc hzc with hq | hl | ⟨he, hm⟩ | ⟨he, hm⟩
  · exact hquiet hq
  · exact hlifted hl
  · exact hexit he hm
  · exact hexit he hm

end Nbr

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf4
