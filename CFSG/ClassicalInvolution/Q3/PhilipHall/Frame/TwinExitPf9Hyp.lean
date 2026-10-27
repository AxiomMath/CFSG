module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf4Hyp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Out
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Pull
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameConn

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9

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

theorem hyp51At_u_new5 (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (h4 : Thm4RTwinBelow 3 n)
    (h : TwinCoreHyp n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    (hAct : TwinFrameUActs (CoreAssembly.conjClass (tightCore R)))
    (hLP : TwinExitPf9.TwinFrameULiftPairSec (CoreAssembly.conjClass (tightCore R)))
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t) {c : G}
    (hc : c = u ∨ c = z * u ∨ c = u * t ∨ c = z * u * t) :
    Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
  have hΩ := h.hyp
  have hBelow : CIT3Below (Nat.card G) := h.card ▸ h.below
  have hB := TwinFrame.isElemAbelian_of_frameData hΩ hf
  have hzB := TwinFrame.z_mem z u t
  have huB := TwinFrame.u_mem z u t
  have htB := TwinFrame.t_mem z u t
  obtain ⟨hcB, hc1, hzc, htc, hztc, hBeq⟩ := ucoset_facts hΩ hf hc
  have htC : t ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB htB
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hf.hz hf.hK'
  obtain ⟨J', hJ', hJne⟩ := TwinFrame.exists_twin_of_trans hΩ
    (TwinFrame.trans_conjClass _) hf.mem hf.hK' hf.hne hf.hJ.1
  have hf' := frameData_twin_J hΩ hf hJ'
  have outJ := TwinExitPf9.u_out_sec hSp hD4 h4 h hRc hZ hAct hf hJ' hJne hc htC
  have hquiet : Quiet c t htC → Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := fun hq =>
    ⟨fun L₁ L₂ h₁ _ m₁ _ => (moved_false_of_quiet hB htB hcB hc1 hf.ht.ne_one htc htC hq h₁
        m₁).elim,
      fun L hL hm => (moved_false_of_quiet hB htB hcB hc1 hf.ht.ne_one htc htC hq hL hm).elim⟩
  obtain ⟨SJ, hJd⟩ := exists_datum_at h hRc hf.hJ.1 hf.ht
  have hlifted : ¬ Quiet c t htC → TwinExitPf9.LiftedAtSec J c t htC → TwinExitPf9.LiftedAtSec J' c t htC →
      Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
    intro hq lJ lJ'
    refine TwinFrame.hyp51At_of_classicalOrQuiet_model hBelow hZ hB htB hcB hc1 hf.ht.ne_one htc
      htC ((lJ.liftedAt hJd.datum).classicalOrQuiet htC) ?_
    intro L hL hmov
    have htK := edge_mem_centralizerModOdd h hRc hf.mem hf.hz
      (hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz)) hf.ht hf.t_ne_z
    have htK' := edge_mem_centralizerModOdd h hRc hf.hK'.1 hzK'
      (hf.hJ.2 K' hf.hK') hf.ht hf.t_ne_z
    obtain ⟨R₁, R₂, hR₁, hR₂, hcomm, hR₁t, -, x, hx, y, hy, hx2, hy2, hxy⟩ :=
      exists_sylow_frame_gen hΩ hf htK htK'
    have hxK : x ∈ K := hR₁.1 hx
    have hyK' : y ∈ K' := hR₂.1 hy
    have hxt : x * t = t * x := hR₁t x hx
    have hxy' : x * y = y * x := hcomm x hx y hy
    have hxz : z * x = x * z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hf.hz hxK)
      exact this.symm
    have hux : u * x = x * u := by
      rw [← hxy]
      calc x * y * x = x * (y * x) := by group
        _ = x * (x * y) := by rw [← hxy']
    have hBx : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      intro b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hb with rfl | rfl | rfl
      · exact hxz
      · exact hux
      · exact hxt.symm
    have hxc : x ∈ Subgroup.centralizer ({c} : Set G) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hBx hcB)
      exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
    obtain ⟨M, M', hM, hM', hne, hcm, hcM, hcM'⟩ := hLP K K' J z u t hf J' hJ' hJne c hc htC hq lJ lJ'
      x y hxK hyK' hx2 hy2 hxy hxt hxc
    exact alpha_of_lifted_u hBelow hZ hB hcB hc1 hzB htB hf.hz.ne_one hf.ht.ne_one hzc htc hztc
      (TwinFrame.zt_ne_one hf) hBeq hM hM' hne hcm hxc hx2 hxt hcM hcM' hL hmov
  have hexit : ∀ {M : Subgroup G}, ExitAt M c t htC → MovedOddFreeAt c t htC →
      Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := fun he hm =>
    hyp51At_of_autOddFree hB htB hcB hc1 hf.ht.ne_one htc htC hm.1 fun L hL hmv =>
      he.autOddFree hSp hD4 hM12 hL
        (hmv _ (oddQuotMk_mem_modOdd htB htC)
          (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 htB hf.ht.ne_one htc htC))
  by_cases hq : Quiet c t htC
  · exact hquiet hq
  rcases outJ with hq' | hl | ⟨he, hm⟩ | ⟨he, hm⟩
  · exact absurd hq' hq
  · exact hlifted hq hl.1 hl.2
  · exact hexit he hm
  · exact hexit he hm

theorem hyp51_of_frameData_new5 (hSp : ModelFactSp62) (hD4m : ModelFactD42) (hM12 : ModelFactM12)
    (h4 : Thm4RTwinBelow 3 n)
    (h : TwinCoreHyp n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    (hD4 : TL4.D4OddAutInnerNC3)
    (hsolv : ∀ M ∈ CoreAssembly.conjClass (tightCore R), Group.IsSolvable ↥M)
    (hLP : TwinExitPf9.TwinFrameULiftPairSec (CoreAssembly.conjClass (tightCore R)))
    (hAct : TwinFrameUActs (CoreAssembly.conjClass (tightCore R)))
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t) :
    Hyp51 (Subgroup.closure ({z, u, t} : Set G)) := by
  have hΩ := h.hyp
  obtain ⟨hB, hB8⟩ := TwinFrame.shape_of_frameData hΩ hf
  refine ⟨hB, hB8, fun c hc hc1 => ?_⟩
  rcases TwinFrame.mem_closure_cases hΩ hf hc with e | e | e | e | e | e | e | e
  · exact absurd e hc1
  · subst e
    exact TwinFrame.hyp51At_z hΩ hsolv hf
  · exact TwinExitPf4.hyp51At_nbr_new3 hSp hD4m hM12 h4 h hRc hZ hD4 hf (Or.inl e)
  · exact TwinExitPf4.hyp51At_nbr_new3 hSp hD4m hM12 h4 h hRc hZ hD4 hf (Or.inr e)
  · exact hyp51At_u_new5 hSp hD4m hM12 h4 h hRc hZ hAct hLP hf (Or.inl e)
  · exact hyp51At_u_new5 hSp hD4m hM12 h4 h hRc hZ hAct hLP hf (Or.inr (Or.inl e))
  · exact hyp51At_u_new5 hSp hD4m hM12 h4 h hRc hZ hAct hLP hf (Or.inr (Or.inr (Or.inl e)))
  · exact hyp51At_u_new5 hSp hD4m hM12 h4 h hRc hZ hAct hLP hf (Or.inr (Or.inr (Or.inr e)))

theorem hyp51_of_mem_frameSet_new5 (hSp : ModelFactSp62) (hD4m : ModelFactD42)
    (hM12 : ModelFactM12) (h4 : Thm4RTwinBelow 3 n)
    (h : TwinCoreHyp n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    (hD4 : TL4.D4OddAutInnerNC3)
    (hsolv : ∀ M ∈ CoreAssembly.conjClass (tightCore R), Group.IsSolvable ↥M)
    (hLP : TwinExitPf9.TwinFrameULiftPairSec (CoreAssembly.conjClass (tightCore R)))
    (hAct : TwinFrameUActs (CoreAssembly.conjClass (tightCore R))) {B : Subgroup G}
    (hB : B ∈ TwinFrame.frameSet (CoreAssembly.conjClass (tightCore R))) : Hyp51 B := by
  obtain ⟨K, K', J, z, u, t, hf, rfl⟩ := hB
  exact hyp51_of_frameData_new5 hSp hD4m hM12 h4 h hRc hZ hD4 hsolv hLP hAct hf

end UVertex

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9
