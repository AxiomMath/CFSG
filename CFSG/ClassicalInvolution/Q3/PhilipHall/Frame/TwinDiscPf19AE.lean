module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Act

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

section Perm

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem secAct_map_secImg (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (g : ↥(Subgroup.centralizer ({c} : Set G))) {J₁ : Subgroup G} :
    (secImg Ω c J₁).map (secAct hΩ hc2 g).toMonoidHom = secImg Ω c (conjSub (g : G) J₁) := by
  have hcore : ∀ (h : ↥(Subgroup.centralizer ({c} : Set G))) {L : Subgroup G}
      (k : ↥(coreHull Ω c)), ((k : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈
        TwinADescent.coreAt c L → (h : G) * ((k : ↥(Subgroup.centralizer ({c} : Set G))) : G) *
          (h : G)⁻¹ ∈ TwinADescent.coreAt c (conjSub (h : G) L) := by
    intro h L k hk
    have h1 : (h : G) * ((k : ↥(Subgroup.centralizer ({c} : Set G))) : G) * (h : G)⁻¹ ∈
        conjSub (h : G) (TwinADescent.coreAt c L) := conj_mem_conjSub hk
    rwa [TwinADescent.conjSub_coreAt h.2 L] at h1
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hs
    have hk'G : ((k' : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈ TwinADescent.coreAt c J₁ :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hk')
    refine Subgroup.mem_map.mpr ⟨C25Y.conjOnSub (coreHull Ω c) (conjSub_coreHull hΩ hc2 g) k', ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (hcore g k' hk'G))
    · exact (secAct_mk hΩ hc2 g k').symm
  · rintro hy
    obtain ⟨k'', hk'', rfl⟩ := Subgroup.mem_map.mp hy
    have hk''G : ((k'' : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈
        TwinADescent.coreAt c (conjSub (g : G) J₁) :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hk'')
    set k' : ↥(coreHull Ω c) :=
      C25Y.conjOnSub (coreHull Ω c) (conjSub_coreHull hΩ hc2 g⁻¹) k'' with hk'def
    have hk'G : ((k' : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈ TwinADescent.coreAt c J₁ := by
      have h0 := hcore g⁻¹ k'' hk''G
      have e : conjSub (((g⁻¹ : ↥(Subgroup.centralizer ({c} : Set G))) : G))
          (conjSub (g : G) J₁) = J₁ := conjSub_inv_conjSub (g : G) J₁
      rw [e] at h0
      exact h0
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk k', Subgroup.mem_map.mpr ⟨k',
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hk'G), rfl⟩, ?_⟩
    show secAct hΩ hc2 g (QuotientGroup.mk k') = QuotientGroup.mk k''
    rw [secAct_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    show (g : G) * ((g : G)⁻¹ * ((k'' : ↥(Subgroup.centralizer ({c} : Set G))) : G) *
      ((g : G)⁻¹)⁻¹) * (g : G)⁻¹ = ((k'' : ↥(Subgroup.centralizer ({c} : Set G))) : G)
    group

end Perm

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
