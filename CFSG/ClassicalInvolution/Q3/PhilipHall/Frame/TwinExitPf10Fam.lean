module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Bridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt

section Fam

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem tightCore_conjSub (A : Subgroup G) (g : G) :
    tightCore (conjSub g A) = conjSub g (tightCore A) := by
  apply le_antisymm
  · have h1 := map_tightCore_le (MulAut.conj g⁻¹).toMonoidHom (conjSub g A)
    have h2 : (tightCore (conjSub g A)).map (MulAut.conj g⁻¹).toMonoidHom ≤ tightCore A := by
      have : (conjSub g A).map (MulAut.conj g⁻¹).toMonoidHom = A := conjSub_inv_conjSub g A
      rw [this] at h1
      exact h1
    have h3 : conjSub g⁻¹ (tightCore (conjSub g A)) ≤ tightCore A := h2
    rw [conjSub_le_iff, inv_inv] at h3
    exact h3
  · exact map_tightCore_le (MulAut.conj g).toMonoidHom A

omit [Finite G] in
theorem coreAt_conjSub {c g : G} (hg : g ∈ Subgroup.centralizer ({c} : Set G)) (J : Subgroup G) :
    TwinADescent.coreAt c (conjSub g J) = conjSub g (TwinADescent.coreAt c J) := by
  unfold TwinADescent.coreAt
  rw [← tightCore_conjSub]
  congr 1
  ext x
  simp only [Subgroup.mem_inf, mem_conjSub_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) h2) hg⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hg h2) (Subgroup.inv_mem _ hg)
    simpa [mul_assoc] using this



theorem secImg_conj {Ω : Set (Subgroup G)} {c : G} (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (g : ↥(Subgroup.centralizer ({c} : Set G)))
    (J : Subgroup G) :
    (secImg Ω c J).map (TwinExitPf6.secAut Ω c hΩ hc2 g).toMonoidHom =
      secImg Ω c (conjSub (g : G) J) := by
  haveI hHn := TwinExitPf6.normal_coreHull hΩ hc2
  have hgC : (g : G) ∈ Subgroup.centralizer ({c} : Set G) := g.2
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hy
    have hh' : (((h : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈
        TwinADescent.coreAt c J := hh
    let h' : ↥(coreHull Ω c) := ⟨g * ((h : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) * g⁻¹,
      hHn.conj_mem _ h.2 g⟩
    refine ⟨h', ?_, (TwinExitPf6.secAut_mk hΩ hc2 g h h' rfl).symm⟩
    show (((h' : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈
      TwinADescent.coreAt c (conjSub (g : G) J)
    rw [coreAt_conjSub hgC, mem_conjSub_iff]
    have : (g : G)⁻¹ * (((h' : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) : G) * g =
        (((h : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) : G) := by
      simp [h', mul_assoc]
    rw [this]
    exact hh'
  · rintro ⟨h, hh, rfl⟩
    have hh' : (((h : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈
        TwinADescent.coreAt c (conjSub (g : G) J) := hh
    rw [coreAt_conjSub hgC, mem_conjSub_iff] at hh'
    let h₀ : ↥(coreHull Ω c) := ⟨g⁻¹ * ((h : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) * g⁻¹⁻¹,
      hHn.conj_mem _ h.2 g⁻¹⟩
    refine ⟨QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) h₀, ⟨h₀, ?_, rfl⟩, ?_⟩
    · show (((h₀ : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈
        TwinADescent.coreAt c J
      have : (((h₀ : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) : G) =
          (g : G)⁻¹ * (((h : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) : G) * g := by
        simp [h₀]
      rw [this]
      exact hh'
    · exact (TwinExitPf6.secAut_mk hΩ hc2 g h₀ h (by simp [h₀, mul_assoc]) :)

theorem secAut_map_secFam {Ω : Set (Subgroup G)} {c : G} (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (g : ↥(Subgroup.centralizer ({c} : Set G)))
    {K : Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))}
    (hK : K ∈ TwinDisc.secFam Ω c) :
    K.map (TwinExitPf6.secAut Ω c hΩ hc2 g).toMonoidHom ∈ TwinDisc.secFam Ω c := by
  obtain ⟨J, hJ, rfl⟩ := exists_of_mem_secFam hK
  rw [secImg_conj hΩ hc2 g J]
  refine secImg_mem_secFam ⟨hΩ.conjInvariant (g : G) J hJ.1, ?_⟩
  have := trivialOnQuot_conjSub hJ.2 (g : G)
  have hcomm : (g : G) * c * (g : G)⁻¹ = c := by
    have := Subgroup.mem_centralizer_singleton_iff.mp g.2
    calc (g : G) * c * (g : G)⁻¹ = c * (g : G) * (g : G)⁻¹ := by rw [this]
      _ = c := by group
  rwa [hcomm] at this

end Fam

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10
