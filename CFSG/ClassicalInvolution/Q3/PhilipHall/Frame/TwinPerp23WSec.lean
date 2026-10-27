module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

namespace W

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.AE5

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

@[expose] noncomputable def topIncl {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hgen : TC.Thin.pSpan Φ = ⊤) : X →* ↥(TC.Thin.pSpan Φ) where
  toFun x := ⟨x, TwinDisc.mem_pSpan_of_top hgen x⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def chiX {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hgen : TC.Thin.pSpan Φ = ⊤) (I : TC.Thin.AEIdent Φ 5) : X →* Equiv.Perm (Fin 5) :=
  ((TC.Thin.permQ 5).comp I.φ).comp (topIncl hgen)

@[expose] noncomputable def chiLayer (Ω : Set (Subgroup G)) (c : G)
    (hgen : TC.Thin.pSpan (TwinDisc.secFam Ω c) = ⊤) (I : TC.Thin.AEIdent (TwinDisc.secFam Ω c) 5) :
    ↥(coreLayer Ω c) →* Equiv.Perm (Fin 5) :=
  ((chiX hgen I).comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)))).comp
    (Subgroup.equivMapOfInjective (coreHull Ω c) (Subgroup.centralizer ({c} : Set G)).subtype
      (Subgroup.centralizer ({c} : Set G)).subtype_injective).symm.toMonoidHom

theorem chiLayer_apply (hgen : TC.Thin.pSpan (TwinDisc.secFam Ω c) = ⊤)
    (I : TC.Thin.AEIdent (TwinDisc.secFam Ω c) 5) {τ : G} (hC : τ ∈ Subgroup.centralizer ({c} : Set G))
    (hH : (⟨τ, hC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c)
    (hL : τ ∈ coreLayer Ω c) :
    chiLayer Ω c hgen I ⟨τ, hL⟩ =
      TC.Thin.permQ 5 (I.φ ⟨(QuotientGroup.mk (⟨⟨τ, hC⟩, hH⟩ : ↥(coreHull Ω c)) :
        ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)),
          TwinDisc.mem_pSpan_of_top hgen _⟩) := by
  have h : (Subgroup.equivMapOfInjective (coreHull Ω c) (Subgroup.centralizer ({c} : Set G)).subtype
      (Subgroup.centralizer ({c} : Set G)).subtype_injective).symm ⟨τ, hL⟩ =
        (⟨⟨τ, hC⟩, hH⟩ : ↥(coreHull Ω c)) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  show chiX hgen I (QuotientGroup.mk' _ ((Subgroup.equivMapOfInjective _ _ _).symm ⟨τ, hL⟩)) = _
  rw [h]
  rfl

theorem mem_coreLayer_of {τ : G} (hC : τ ∈ Subgroup.centralizer ({c} : Set G))
    (hH : (⟨τ, hC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c) : τ ∈ coreLayer Ω c :=
  ⟨⟨τ, hC⟩, hH, rfl⟩

theorem exists_mem_sylow_of_mem_secImg (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J T : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) (hT : IsSylow2In T J)
    (hTc : T ≤ Subgroup.centralizer ({c} : Set G))
    (hA : IsPGroup 2 ↥(TwinDisc.secImg Ω c J)) {y0 : ↥(coreHull Ω c) ⧸
      classicalInvolutionOddCore ↥(coreHull Ω c)} (hy0 : y0 ∈ TwinDisc.secImg Ω c J) :
    ∃ τ ∈ T, ∃ (hC : τ ∈ Subgroup.centralizer ({c} : Set G))
      (hH : (⟨τ, hC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c),
      (QuotientGroup.mk (⟨⟨τ, hC⟩, hH⟩ : ↥(coreHull Ω c)) :
        ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) = y0 := by
  classical
  have hTs : IsSylow2In T (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hT, hTc⟩
  have hTt := (hTs.subgroupOf (TwinADescent.coreAt_le_centralizer c J)).subgroupOf (le_coreHull hJ)
  let g : ↥(((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
      (coreHull Ω c)) →* ↥(TwinDisc.secImg Ω c J) :=
    ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))).comp
      (((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
        (coreHull Ω c)).subtype).codRestrict (TwinDisc.secImg Ω c J)
      (fun x => ⟨x, x.2, rfl⟩)
  have hgs : Function.Surjective g := by
    rintro ⟨y', x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hmap := map_sylow_eq_of_isPGroup g hgs hA (Uniform.sylowOfIsSylow2In hTt)
  have hy' : (⟨y0, hy0⟩ : ↥(TwinDisc.secImg Ω c J)) ∈
      ((Uniform.sylowOfIsSylow2In hTt : Subgroup _)).map g := by
    rw [hmap]; trivial
  obtain ⟨s, hs0, hsg⟩ := hy'
  have hs := hs0
  rw [Uniform.coe_sylowOfIsSylow2In hTt] at hs
  exact ⟨s.1.1.1, hs, s.1.1.2, s.1.2, congrArg Subtype.val hsg⟩

end Layer

end W

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
