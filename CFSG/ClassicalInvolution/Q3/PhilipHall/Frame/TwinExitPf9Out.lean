module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf3U

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

section UVertex

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t₀ : G} {n : ℕ}
  {K K' J : Subgroup G} {z u t : G}


theorem u_out_gen_sec (hSp : ModelFactSp62) (hD4 : ModelFactD42) (h4 : Thm4RTwinBelow 3 n)
    (h : TwinCoreHyp n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t)
    (hum : u ∈ centralizerModOdd ⊤ J) {J' : Subgroup G}
    (hf' : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J' t)
    (hJ' : J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) J) (hJne : J' ≠ J)
    (hum' : u ∈ centralizerModOdd ⊤ J') {c : G}
    (hc : c = u ∨ c = z * u ∨ c = u * t ∨ c = z * u * t)
    (htc : t ∈ Subgroup.centralizer ({c} : Set G)) :
    Quiet c t htc ∨ LiftedAtSec J c t htc ∨ (ExitAt J c t htc ∧ MovedOddFreeAt c t htc) := by
  obtain ⟨SJ, hJd⟩ := exists_datum_at h hRc hf.hJ.1 hf.ht
  have hRcJ : tightCore J = J := tightCore_eq_of_mem hRc hf.hJ.1
  obtain ⟨hcm, hc2, hc1⟩ := TwinExitPf3.u_cm h hRc hf hum hc
  obtain ⟨hcm', -, -⟩ := TwinExitPf3.u_cm h hRc hf' hum' hc
  have hcK' : c ∈ Balance.Bootstrap.trivialOnQuot J' := ⟨hcm'.2.1, fun x hx => hcm'.2.2.2 x hx⟩
  have hJ'tw : J' ∈ twinSet (CoreAssembly.conjClass (tightCore J)) (tightCore J) := by
    rw [hRcJ, conjClass_eq_of_mem hf.hJ.1]
    exact hJ'
  have hne' : J' ≠ tightCore J := by rw [hRcJ]; exact hJne
  exact quietLiftedSecExit_of_twin hSp hD4 h4 hJd hRcJ hZ hc2 hc1 hcm htc hJ'tw hne' hcK'

theorem u_out_sec (hSp : ModelFactSp62) (hD4 : ModelFactD42) (h4 : Thm4RTwinBelow 3 n)
    (h : TwinCoreHyp n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    (hAct : TwinFrameUActs (CoreAssembly.conjClass (tightCore R)))
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t) {J' : Subgroup G}
    (hJ' : J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) J) (hJne : J' ≠ J) {c : G}
    (hc : c = u ∨ c = z * u ∨ c = u * t ∨ c = z * u * t)
    (htc : t ∈ Subgroup.centralizer ({c} : Set G)) :
    Quiet c t htc ∨ (LiftedAtSec J c t htc ∧ LiftedAtSec J' c t htc) ∨ (ExitAt J c t htc ∧ MovedOddFreeAt c t htc) ∨
      (ExitAt J' c t htc ∧ MovedOddFreeAt c t htc) := by
  have hΩ := h.hyp
  have hf' := frameData_twin_J hΩ hf hJ'
  have htJ' : IsUniqueInvolution J' t := isUniqueInvolution_of_mem_twinSet hf.ht hJ'
  have hJtw : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) J' := ⟨hf.hJ.1, t, htJ', hf.ht⟩
  have outJ := u_out_gen_sec hSp hD4 h4 h hRc hZ hf (hAct K K' J z u t hf) hf' hJ' hJne
    (hAct K K' J' z u t hf') hc htc
  have outJ' := u_out_gen_sec hSp hD4 h4 h hRc hZ hf' (hAct K K' J' z u t hf') hf hJtw (Ne.symm hJne)
    (hAct K K' J z u t hf) hc htc
  rcases outJ with q | l | e
  · exact Or.inl q
  · rcases outJ' with q | l' | e'
    · exact Or.inl q
    · exact Or.inr (Or.inl ⟨l, l'⟩)
    · exact Or.inr (Or.inr (Or.inr e'))
  · exact Or.inr (Or.inr (Or.inl e))

end UVertex

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9
