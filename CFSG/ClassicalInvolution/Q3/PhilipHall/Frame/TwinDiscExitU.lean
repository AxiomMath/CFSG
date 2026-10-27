module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10Frame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc

variable {Y : Type} [Group Y] [Finite Y]

section Edge

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
    {K K' : Subgroup Y} {z u : Y} {J : Subgroup Y} {t : Y} {W : Subgroup Y}

theorem section_edge (s : Setting n R S t₀ K K' z u J t W) :
    ∃ M ∈ secFam (CoreAssembly.conjClass (tightCore R)) u,
      ∃ N : Subgroup (↥(coreHull (CoreAssembly.conjClass (tightCore R)) u) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) u)),
        N ∈ omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) u) M := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : Y, conjSub g M = N := TwinFrame.trans_conjClass _
  obtain ⟨J', R₁, R₁', T, T', x, y, hJ'tw, hJ'ne, hJ't, hF⟩ := exists_frame hΩ htr h2 s.data
  have hJΩ : J ∈ Ω := hf.hJ.1
  have hJ'Ω : J' ∈ Ω := hJ'tw.1
  have hJtq : J ∈ tqMembers3 Ω u :=
    ⟨hJΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJΩ ⟨T, hF.hT, hF.le_centralizer_u.1⟩⟩
  have hJ'tq : J' ∈ tqMembers3 Ω u :=
    ⟨hJ'Ω, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ'Ω ⟨T', hF.hT', hF.le_centralizer_u.2⟩⟩
  have h8 : 8 ≤ Nat.card T' :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ'Ω hF.hT')
  have hT't : T' ≤ Subgroup.centralizer ({t} : Set Y) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hJ't.commute_of_mem (hF.hT'.1 hs)).symm
  have hT'J : T' ≤ Subgroup.normalizer (J : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJΩ hJ'Ω hJ'ne.symm hf.ht hF.hT'.1 hF.hT'.2.1
      (by omega) hT't
  exact ⟨_, secImg_mem_secFam hJtq, _, omegaNbr_secImg hΩ hc2 hJtq hJ'tq hF.hT hF.hT'
    hF.le_centralizer_u.1 hF.le_centralizer_u.2 hF.cTT' hT'J⟩

end Edge

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
