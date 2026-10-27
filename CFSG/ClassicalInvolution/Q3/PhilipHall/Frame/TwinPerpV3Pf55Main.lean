module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Frame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf9Layer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Main

theorem twinSet_four {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K K' K₃ K₄ : Subgroup Y} {u₁ u₂ u₃ : Y} (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hF : FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄) :
    ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, J = K ∨ J = K' ∨ J = K₃ ∨ J = K₄ := by
  classical
  intro J hJ
  by_contra hcon
  push Not at hcon
  obtain ⟨hJK, hJK', hJK₃, hJK₄⟩ := hcon
  have hd := hStd.datum
  have hC := CoreData.of_S hStd.perp.core
  have hP := hC.partIHypG
  have hperp := kPerp_datum hStd.perp hd.mem hd.hz
  have hnc : ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
      (∃ ρ : Rep (CoreAssembly.conjClass (tightCore R)) W, ρ.K = K) →
        ¬ DbarConnected (CoreAssembly.conjClass (tightCore R)) W :=
    fun W hW ⟨ρ₀, hρ₀⟩ => not_dbarConnected_of_wyl' hP hd hperp hW ρ₀ hρ₀ (hStd.wyl W hW)
  have hKt : K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := mem_twinSet_self hd.mem hd.hz
  obtain ⟨hK₄, h41, h42, h43, -⟩ := hF
  have hcard := twins_card_le_four' hP hd hperp hnc ({K, K', K₃, K₄, J} : Finset (Subgroup Y))
    (by simp) (by
      intro M hM
      simp only [Finset.mem_insert, Finset.mem_singleton] at hM
      rcases hM with rfl | rfl | rfl | rfl | rfl
      · exact hKt
      · exact hd.hK'
      · exact hd.hK₃
      · exact hK₄
      · exact hJ)
  have hne : K ≠ K' := hd.hne.symm
  rw [Finset.card_insert_of_notMem (by simp [hne, hd.hK₃K.symm, h41.symm, hJK.symm]),
    Finset.card_insert_of_notMem (by simp [hd.hK₃K'.symm, h42.symm, hJK'.symm]),
    Finset.card_insert_of_notMem (by simp [h43.symm, hJK₃.symm]),
    Finset.card_pair_eq_two_iff.2 (Ne.symm hJK₄)] at hcard
  omega

variable {n : ℕ}

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
