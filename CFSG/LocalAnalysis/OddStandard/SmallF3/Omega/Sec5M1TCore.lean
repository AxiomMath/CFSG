module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5M1TFrameCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem sec5m1t_aux_simAct_conj (g : OGroup Q) (y : simGroup Q) (t : OGroup Q) :
    simAct Q ((orthToSim Q g)⁻¹ * y * orthToSim Q g) t =
      g⁻¹ * simAct Q y (g * t * g⁻¹) * g := by
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, simAct_orthToSim]
  rw [← map_inv, simAct_orthToSim]
  simp

theorem sec5m1t_core (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {z : OGroup Q} (hzz : z * z = 1) (hzt : invType z = (4, 1))
    {x : simGroup Q}
    (hcomm : ∀ h ∈ omegaGroup hQ, h * z = z * h → Odd (orderOf h) →
      x * orthToSim Q h = orthToSim Q h * x)
    (hsq : ∀ t ∈ omegaGroup hQ, simAct Q (x * x) t = simAct Q (orthToSim Q z) t) :
    ∃ x₀ : OGroup Q, x = orthToSim Q x₀ ∧ x₀ * x₀ = piOrth Q * z := by
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  have ht0 : fr.signChange {0, 1, 2, 3} * fr.signChange {0, 1, 2, 3} = 1 :=
    fr.signChange_mul_self _
  have ht0type : invType (fr.signChange {0, 1, 2, 3}) = (4, 1) := by
    have h := fr.invType_signChange hQ {0, 1, 2, 3}
      (by decide : Even ({0, 1, 2, 3} : Finset (Fin 6)).card)
    have hc : ({0, 1, 2, 3} : Finset (Fin 6)).card = 4 := by decide
    rw [hc] at h
    norm_num at h
    exact h
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_invType_eq hQ ht0 hzz (ht0type.trans hzt.symm))
  let x' : simGroup Q := (orthToSim Q g)⁻¹ * x * orthToSim Q g
  have hcomm' : ∀ h ∈ omegaGroup hQ,
      h * fr.signChange {0, 1, 2, 3} = fr.signChange {0, 1, 2, 3} * h → Odd (orderOf h) →
        x' * orthToSim Q h = orthToSim Q h * x' := by
    intro h hh hht hodd
    have hh'mem : g * h * g⁻¹ ∈ omegaGroup hQ := (omegaGroup_normal hQ).conj_mem h hh g
    have hh'z : (g * h * g⁻¹) * z = z * (g * h * g⁻¹) := by
      rw [← hg]
      calc (g * h * g⁻¹) * (g * fr.signChange {0, 1, 2, 3} * g⁻¹)
          = g * (h * fr.signChange {0, 1, 2, 3}) * g⁻¹ := by group
        _ = g * (fr.signChange {0, 1, 2, 3} * h) * g⁻¹ := by rw [hht]
        _ = (g * fr.signChange {0, 1, 2, 3} * g⁻¹) * (g * h * g⁻¹) := by group
    have hh'odd : Odd (orderOf (g * h * g⁻¹)) := by
      have ho := MulEquiv.orderOf_eq (MulAut.conj g) h
      rw [MulAut.conj_apply] at ho
      rw [ho]
      exact hodd
    have hx := hcomm (g * h * g⁻¹) hh'mem hh'z hh'odd
    have h'orth : orthToSim Q (g * h * g⁻¹) =
        (orthToSim Q g) * orthToSim Q h * (orthToSim Q g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have hconj := (Commute.conj_iff (h := orthToSim Q g)
      (a := (orthToSim Q g)⁻¹ * x * orthToSim Q g) (b := orthToSim Q h)).mp ?_
    · exact hconj
    · rwa [← h'orth, show (orthToSim Q g) * ((orthToSim Q g)⁻¹ * x * orthToSim Q g) *
        (orthToSim Q g)⁻¹ = x from by group]
  have hsq' : ∀ t ∈ omegaGroup hQ,
      simAct Q (x' * x') t =
        simAct Q (orthToSim Q (fr.signChange {0, 1, 2, 3})) t := by
    intro t ht
    have ht' : g * t * g⁻¹ ∈ omegaGroup hQ := (omegaGroup_normal hQ).conj_mem t ht g
    have h1 : simAct Q (x' * x') t =
        g⁻¹ * simAct Q (x * x) (g * t * g⁻¹) * g := by
      rw [show x' * x' = (orthToSim Q g)⁻¹ * (x * x) * orthToSim Q g from by
        simp only [x']; group]
      exact sec5m1t_aux_simAct_conj g (x * x) t
    rw [h1, hsq (g * t * g⁻¹) ht', simAct_orthToSim, simAct_orthToSim]
    rw [← hg]
    group
  obtain ⟨x₀', hx', hx'sq⟩ := sec5m1t_core_frame hQ hdim fr (x := x') hcomm' hsq'
  refine ⟨g * x₀' * g⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, ← hx']
    show x = (orthToSim Q g) * ((orthToSim Q g)⁻¹ * x * orthToSim Q g) * (orthToSim Q g)⁻¹
    group
  · show (g * x₀' * g⁻¹) * (g * x₀' * g⁻¹) = piOrth Q * z
    calc (g * x₀' * g⁻¹) * (g * x₀' * g⁻¹) = g * (x₀' * x₀') * g⁻¹ := by group
      _ = g * (piOrth Q * fr.signChange {0, 1, 2, 3}) * g⁻¹ := by rw [hx'sq]
      _ = piOrth Q * (g * fr.signChange {0, 1, 2, 3} * g⁻¹) := by
        rw [← mul_assoc, mul_piOrth_comm]
        group
      _ = piOrth Q * z := by rw [hg]

end CFSG.OddStandard.SmallF3.Omega
