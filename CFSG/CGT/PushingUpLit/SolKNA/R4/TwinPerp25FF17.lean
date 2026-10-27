module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF16
public import CFSG.ClassicalInvolution.Q3.TL4D1Out
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SubnormalE2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25F0
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF11
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF15

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2 (imgX)
open scoped commutatorElement

section Four


section Sec

variable {Y : Type} [Group Y] [Finite Y]

@[expose] noncomputable def fSection (b : Y) (K : Subgroup Y) : Subgroup ↥(Subgroup.centralizer ({b} : Set Y)) :=
  subnormalClosure ((coreAt b K).subgroupOf (Subgroup.centralizer ({b} : Set Y)))

end Sec

@[expose] def TwinCentral4 (n : ℕ) : Prop :=
  TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (S₁ : Sylow 2 Y) (R₁ R₂ : Subgroup Y) (t₁ u₁ u₂ b : Y)
    (F : FSet 4 n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b)
    (htH : (⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) ∈ fSection b (tightCore R)),
    (∃ K'' ∈ twinSet (CoreAssembly.conjClass (imgX b (fSection b (tightCore R)) (tightCore R)))
      (imgX b (fSection b (tightCore R)) (tightCore R)),
      K'' ≠ imgX b (fSection b (tightCore R)) (tightCore R)) →
    ∀ g : ↥(fSection b (tightCore R)) ⧸ classicalInvolutionOddCore ↥(fSection b (tightCore R)),
      g * QuotientGroup.mk' (classicalInvolutionOddCore ↥(fSection b (tightCore R)))
        (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ :
          ↥(fSection b (tightCore R))) * g⁻¹ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(fSection b (tightCore R)))
        (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ :
          ↥(fSection b (tightCore R)))

section Thm

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ b : Y}

theorem mem_zStarOf_ff_of_center (F : FSet 4 n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b)
    (htH : (⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) ∈ fSection b (tightCore R))
    (hcent : ∀ g : ↥(fSection b (tightCore R)) ⧸
        classicalInvolutionOddCore ↥(fSection b (tightCore R)),
      g * QuotientGroup.mk' (classicalInvolutionOddCore ↥(fSection b (tightCore R)))
        (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ :
          ↥(fSection b (tightCore R))) * g⁻¹ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(fSection b (tightCore R)))
        (⟨(⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))), htH⟩ :
          ↥(fSection b (tightCore R)))) :
    t ∈ zStarOf (Subgroup.centralizer ({b} : Set Y)) := by
  classical
  have hP2 := isPGroup_quot_of_center F htH hcent
  have hin : ∀ τ ∈ fSection b (tightCore R),
      TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer ({b} : Set Y))) τ) := by
    intro τ hτ
    refine tightInO2_oddQuot_of_subnormal (isSubnormal_subnormalClosure _) hτ ?_
    refine ⟨⊤, Subgroup.normal_top, ?_, Subgroup.mem_top _⟩
    exact hP2.of_equiv Subgroup.topEquiv.symm
  have hQ : imgX b ⊤ (tightCore R) ≤ pCore 2 (CentBar b) := by
    rintro _ ⟨m, hm, rfl⟩
    have hmH : ((m : ↥(⊤ : Subgroup ↥(Subgroup.centralizer ({b} : Set Y)))) :
        ↥(Subgroup.centralizer ({b} : Set Y))) ∈ fSection b (tightCore R) :=
      le_subnormalClosure _ (Subgroup.mem_subgroupOf.mp hm)
    exact TL4.mem_pCore_of_tightInO2 (tightInO2_top (hin _ hmH))
  exact mem_zStarOf_ff_of_le_pCore F hQ

theorem zStarFFR_four (hTw : TwinCentral4 n) (hP3 : TL4.TightBelowRPlus 3 n) :
    ZStarFFR 4 n := by
  intro Y _ _ R S t hP K' W S₁ R₁ R₂ t₁ u₁ u₂ hyp h11 b hbS hb2 hF₁ hF₂
  have F : FSet 4 n R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b := ⟨le_rfl, hP, hyp, h11, hbS, hb2, hF₁⟩
  have hKH : (coreAt b (tightCore R)).subgroupOf (Subgroup.centralizer ({b} : Set Y)) ≤
      fSection b (tightCore R) := le_subnormalClosure _
  have htH : (⟨t, F.htC⟩ : ↥(Subgroup.centralizer ({b} : Set Y))) ∈ fSection b (tightCore R) :=
    hKH (Subgroup.mem_subgroupOf.mpr F.base.t_mem_core)
  by_cases htw : ∃ K'' ∈ twinSet (CoreAssembly.conjClass (imgX b (fSection b (tightCore R)) (tightCore R)))
      (imgX b (fSection b (tightCore R)) (tightCore R)),
      K'' ≠ imgX b (fSection b (tightCore R)) (tightCore R)
  · exact mem_zStarOf_ff_of_center F htH (hTw hP3 Y R S t K' W S₁ R₁ R₂ t₁ u₁ u₂ b F htH htw)
  · exact mem_zStarOf_ff_of_center F htH (center_of_noTwin F hKH htH htw).2

end Thm

end Four

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
