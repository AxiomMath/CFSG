module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf11Tight
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Wire

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf11

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

section Rest

variable {X : Type} [Group X] [Finite X]

@[expose] def NoExitRest (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) : Prop :=
  ∀ K ∈ Φ, ∀ (z : X) (hz : IsUniqueInvolution K z), ¬ TightInO2 z ∧
    ∀ (W : Subgroup X) (hKW : K ≤ W), IsSubnormal W ⊤ → (⨆ x : W, conjSub (x : X) K) = W →
      ¬ Thm4Twin.F2.ExitSec W K hKW z hz

theorem hasLifts_of_noExitRest {Φ : Set (Subgroup X)} {n : ℕ} (hP : TL4.TightBelowRPlus 3 n)
    (hlt : Nat.card X < n) (hS : Q8Section X Φ) (htight : ∀ K ∈ Φ, tightCore K = K)
    (hno : NoExitRest X Φ) : HasLifts Φ := by
  intro K hK
  obtain ⟨z, hz⟩ := (hS.hyp.omega1 K hK).1
  rcases exists_lift_or_exit_tight (Thm1RTwinLiftSetEBelow.toSet (hP.twin rfl))
      (tightBelowR_three_iff.mp hP.tbelow) hlt hS.oddFree hS.hyp htight hS.two hS.q8 hS.aEmpty
      (fun K hK z hz => (hno K hK z hz).1) hK hz with ⟨L, hL⟩ | ⟨W, hKW, hWs, hWg, hexit⟩
  · exact ⟨L, z, hL⟩
  · exact absurd hexit ((hno K hK z hz).2 W hKW hWs hWg)

theorem noExit_of_noExitRest {Φ : Set (Subgroup X)} {n : ℕ} (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hlt : Nat.card X < n) (hS : Q8Section X Φ)
    (htight : ∀ K ∈ Φ, tightCore K = K) (hno : NoExitRest X Φ) : NoExit X Φ := by
  intro K hK z hz
  have hl := hasLifts_of_noExitRest hP hlt hS htight hno
  refine ⟨?_, (hno K hK z hz).1, (hno K hK z hz).2⟩
  exact TwinExitPf10.oddCent_bot_of_hasLifts hcit hS.hyp hlt hS.oddFree hS.gen hl ⟨K, hK⟩ z hz.sq

end Rest

section Tight

theorem map_tightCore_le_tightCore_map {X Z : Type} [Group X] [Group Z] (f : X →* Z) (A : Subgroup X) :
    (tightCore A).map f ≤ tightCore ((tightCore A).map f) := by
  have h1 : (tightCore A).map f =
      Subgroup.closure (f '' {x | x ∈ A ∧ IsPGroup 2 (Subgroup.zpowers x)}) :=
    MonoidHom.map_closure f _
  refine h1.le.trans ((Subgroup.closure_le _).mpr ?_)
  rintro _ ⟨x, ⟨hxA, hx2⟩, rfl⟩
  refine Subgroup.subset_closure ⟨⟨x, Subgroup.subset_closure ⟨hxA, hx2⟩, rfl⟩, ?_⟩
  rw [← MonoidHom.map_zpowers]
  exact hx2.map _

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem tightCore_of_mem_secFam {K : Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))}
    (hK : K ∈ TwinDisc.secFam Ω c) : tightCore K = K := by
  obtain ⟨J, hJ, rfl⟩ := exists_of_mem_secFam hK
  refine le_antisymm (tightCore_le _) ?_
  have h1 := TwinExitPf2.tightCore_subgroupOf_cent J c
  have hle : tightCore (J.subgroupOf (Subgroup.centralizer ({c} : Set G))) ≤ coreHull Ω c := by
    rw [h1]; exact le_coreHull hJ
  have h2 : tightCore ((J.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf (coreHull Ω c)) =
      (tightCore (J.subgroupOf (Subgroup.centralizer ({c} : Set G)))).subgroupOf (coreHull Ω c) :=
    CFSG.ClassicalInvolution.Q3.tightCore_subgroupOf hle
  have h3 : secImg Ω c J = (tightCore ((J.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
      (coreHull Ω c))).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))) := by
    rw [h2, h1]; rfl
  rw [h3]
  exact map_tightCore_le_tightCore_map _ _

end Tight

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf11
