module

public import CFSG.ClassicalInvolution.AschTight.S1916Omega
public import CFSG.ClassicalInvolution.Asc77.AscT7AApp
public import CFSG.ClassicalInvolution.Q3.Q3CLSeven1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu

namespace Pf3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Asc77.Star3T

section Layer


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem conjSub_rLayer (hΩ : HypOmegaGen Ω) {x g : G} (hg : g ∈ Subgroup.centralizer ({x} : Set G)) :
    conjSub g (rLayer Ω x) = rLayer Ω x := by
  have h : ∀ g : G, g ∈ Subgroup.centralizer ({x} : Set G) → conjSub g (rLayer Ω x) ≤ rLayer Ω x := by
    intro g hg
    unfold rLayer
    show Subgroup.map (MulAut.conj g).toMonoidHom _ ≤ _
    rw [Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hR => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hRx => ?_
    have hR' : conjSub g R ∈ RSet Ω := Q3CL.Thompson.conjSub_mem_RSet hΩ hR g
    have hC : conjSub g R ≤ Subgroup.centralizer ({x} : Set G) := by
      have h1 := conjSub_mono (n := g) hRx
      rwa [conjSub_eq_self_of_mem hg] at h1
    exact le_iSup₂_of_le (conjSub g R) hR' (le_iSup_of_le hC le_rfl)
  refine le_antisymm (h g hg) ?_
  have hg' : g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.inv_mem _ hg
  have h2 := conjSub_mono (n := g) (h g⁻¹ hg')
  rwa [conjSub_conjSub_inv] at h2

theorem exists_conj_mem_D (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) {x : G} (hxW : x ∈ W)
    {R : Subgroup G} (hR : R ∈ RSet Ω) (hRx : R ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ y ∈ rLayer Ω x, conjSub y R ∈ DSet Ω W ∧ conjSub y R ≤ Subgroup.centralizer ({x} : Set G) := by
  set Y : Subgroup G := rLayer Ω x with hY
  have hcomm := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  have hWC : W ≤ Subgroup.centralizer ({x} : Set G) := fun w hw => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm x hxW w hw).symm
  have hWY : W ≤ Subgroup.normalizer (Y : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_rLayer hΩ (hWC hw))
  obtain ⟨P, hP, hWP⟩ := AscQuot.exists_sylow_normalized' hW2 hWY
  have hWPn : W ≤ Subgroup.normalizer (P : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hWP w hw)
  have hWPsup : IsPGroup 2 ↥(W ⊔ P) := hW2.to_sup_of_normal_right' hP.2.1 hWPn
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hWPsup
  have hPS : P ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hWS : W ≤ (S : Subgroup G) := le_sup_left.trans hS
  have hRY : R ≤ Y := le_iSup₂_of_le R hR (le_iSup (fun _ : R ≤ Subgroup.centralizer ({x} : Set G) => R) hRx)
  obtain ⟨K, -, hRK⟩ := exists_isSylow2In_of_mem_RSet hR
  have hR2 : IsPGroup 2 R := hRK.2.1
  obtain ⟨R', hR'Y, hRR'⟩ := IsSylow2In.exists_ge hR2 hRY
  obtain ⟨c, hcY, hc⟩ := S1916.IsSylow2In.exists_conj hP hR'Y
  have hy : c⁻¹ ∈ Y := Y.inv_mem hcY
  have hle : conjSub c⁻¹ R ≤ P := by
    have h1 := conjSub_mono (n := c⁻¹) (hRR'.trans hc.symm.le)
    rwa [conjSub_inv_conjSub] at h1
  refine ⟨c⁻¹, hy, ?_, ?_⟩
  · exact Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (Q3CL.Thompson.conjSub_mem_RSet hΩ hR c⁻¹)
      (hle.trans hPS)
  · have hyC : c⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := Asc77.rLayer_le_centralizer Ω x hy
    have h1 := conjSub_mono (n := c⁻¹) hRx
    rwa [conjSub_eq_self_of_mem hyC] at h1

end Layer

end Pf3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu
