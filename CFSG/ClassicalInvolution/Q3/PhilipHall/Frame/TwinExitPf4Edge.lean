module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent2Disch
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecEdge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes

section Edge

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)}

theorem omegaNbr_of_twin (hΩ : HypOmegaGen Ω) {K L J : Subgroup Y} (hL : L ∈ Ω) {z : Y}
    (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) (hJ : J ∈ omegaNbr Ω K)
    (hJL : J ≠ L) : J ∈ omegaNbr Ω L := by
  obtain ⟨hJΩ, -, R, hR, hRJ, hRN⟩ := hJ
  refine ⟨hJΩ, hJL, R, hR, hRJ, ?_⟩
  obtain ⟨J', -, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
  exact Sec6Gen.le_normalizer_of_le_centralizer hΩ hL hJΩ (Ne.symm hJL) hzL hRJ hRJ'.2.1
    (by have := Sec6Gen.eight_le_of_mem_RSet hΩ hR; omega)
    (Sec6Gen.le_centralizer_of_le_normalizer' hzK hRN)

end Edge

section Main


theorem twinEdgeExitOddFree_proved (hSp : ModelFactSp62) (hD4 : ModelFactD42) (n : ℕ)
    (h4 : Thm4RTwinBelow 3 n) : TwinEdgeExitOddFree n := by
  intro Y _ _ R S t h hRc J hJ u hu hut htu ht Sb hex
  obtain ⟨hu2, -, hBR⟩ := edge_involution h.datum hRc h.hyp hJ hu hut
  obtain ⟨K', hK'tw, hne'⟩ := h.twin
  have hΩ := h.hyp
  have hK'Ω : K' ∈ CoreAssembly.conjClass (tightCore R) := hK'tw.1
  have htR : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core h.datum
  have htK' : IsUniqueInvolution K' t := by
    obtain ⟨-, z, hzK, hzK'⟩ := hK'tw
    rwa [htR.eq hzK]
  have hJK' : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) K' := by
    refine omegaNbr_of_twin hΩ hK'Ω htR htK' hJ ?_
    intro e
    rw [e] at hu
    exact hut (htK'.eq hu).symm
  obtain ⟨SK', hK'd⟩ := exists_datum_at h hRc hK'Ω htK'
  have hRcK' : tightCore K' = K' := tightCore_eq_of_mem hRc hK'Ω
  have hJe : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore K')) (tightCore K') := by
    rw [hRcK', conjClass_eq_of_mem hK'Ω]
    exact hJK'
  obtain ⟨-, -, hBR'⟩ := edge_involution hK'd.datum hRcK' hK'd.hyp hJe hu hut
  have hcK' : u ∈ Balance.Bootstrap.trivialOnQuot K' :=
    ⟨hBR'.2.1, fun x hx => hBR'.2.2.2 x hx⟩
  rcases TwinExitPf2.hasTwin_or_inO2 h4 h hRc hu2 hu.ne_one hBR htu ht hK'tw hne' hcK' with htw | i
  · exact TwinExitPf.exitOddFree_of_hasTwin hSp hD4 R u
      (twinSecHyp_cent h.datum hRc h.hyp hu2 hu.ne_one hBR) htw _ Sb hex
  · exact Or.inl i

theorem twinSecAOddFree_proved (n : ℕ) : TwinSecAOddFree n :=
  twinSecAOddFree_of_secA (TwinADescent2.twinSecA_proved n)

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf4
