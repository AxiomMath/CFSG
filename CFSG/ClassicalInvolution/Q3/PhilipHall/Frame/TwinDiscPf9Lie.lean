module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectF
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF2Lift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Hyp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinOddCent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetCore
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc


structure Q8Section (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) : Prop where
  hyp : HypOmegaGen Φ
  two : ∀ J ∈ Φ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)
  q8 : ∀ J ∈ Φ, ∀ P : Subgroup X, IsSylow2In P J → Nonempty (↥P ≃* QuaternionGroup 2)
  oddFree : classicalInvolutionOddCore X = ⊥
  aEmpty : ∀ J ∈ Φ, AEmpty Φ J
  gen : omegaGen Φ = ⊤

@[expose] def NoExit (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) : Prop :=
  ∀ K ∈ Φ, ∀ (z : X) (hz : IsUniqueInvolution K z),
    oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥ ∧ ¬ TightInO2 z ∧
      ∀ (W : Subgroup X) (hKW : K ≤ W), IsSubnormal W ⊤ → (⨆ x : W, conjSub (x : X) K) = W →
        ¬ Thm4Twin.F2.ExitSec W K hKW z hz

section Lie

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem lifts_of_noExit {n : ℕ} (hP : TL4.TightBelowRPlus 3 n) (hlt : Nat.card X < n)
    (hS : Q8Section X Φ) (hno : NoExit X Φ) :
    (∀ J ∈ Φ, IsPGroup 2 J) ∧ HasLifts Φ ∧ ExactSylow Φ := by
  have hodd : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z →
      oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥ := fun K hK z hz => (hno K hK z hz).1
  have hno2 : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z → ¬ TightInO2 z :=
    fun K hK z hz => (hno K hK z hz).2.1
  have h2 : ∀ K ∈ Φ, IsPGroup 2 K := fun K hK => by
    obtain ⟨z, hz⟩ := (hS.hyp.omega1 K hK).1
    exact isPGroup_of_oddCent hS.hyp hK hz (hodd K hK z hz) (hS.two K hK)
  have hq8 : ∀ K ∈ Φ, Nonempty (↥K ≃* QuaternionGroup 2) := fun K hK => by
    have hKS : IsSylow2In K K := ⟨le_rfl, h2 K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    exact hS.q8 K hK K hKS
  have hl : HasLifts Φ := by
    intro K hK
    obtain ⟨z, hz⟩ := (hS.hyp.omega1 K hK).1
    rcases Thm4Twin.F2.exists_lift_or_exit (Thm1RTwinLiftSetEBelow.toSet (hP.twin rfl))
      (tightBelowR_three_iff.mp hP.tbelow) hlt hS.oddFree hS.hyp h2 hq8 hS.aEmpty hno2 hK hz
      with ⟨L', hL'⟩ | ⟨W, hKW, hWs, hWg, hexit⟩
    · exact ⟨L', z, hL'⟩
    · exact absurd hexit ((hno K hK z hz).2.2 W hKW hWs hWg)
  exact ⟨h2, hl, ExactSylow.of_oddCoreIn_eq_bot fun J hJ L u h => hodd J hJ u h.inv⟩

theorem lieDecomp_of_noExit {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hlt : Nat.card X < n) (hS : Q8Section X Φ) (hne : Φ.Nonempty) (hno : NoExit X Φ) :
    (∀ J ∈ Φ, IsPGroup 2 J) ∧ HasLifts Φ ∧ ExactSylow Φ ∧
      Nonempty (OmegaLieU 3 1 (liftFam Φ)) := by
  obtain ⟨h2, hl, hex⟩ := lifts_of_noExit hP hlt hS hno
  refine ⟨h2, hl, hex, ?_⟩
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨L₀, u₀, hL₀⟩ := hl K₀ hK₀
  exact exists_omegaLieU
    ((Uniform.citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr hcit)
    (hypOmegaModU_liftFam hS.hyp.conjInvariant) ⟨_, satU_mem_liftFam hK₀ hL₀⟩ hS.oddFree hlt

end Lie

section Sec

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem q8Section_secFam (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) :
    Q8Section (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) (secFam Ω c) where
  hyp := hypOmegaGen_secFam hΩ hc2
  two := secFam_twoGroup h2
  q8 := secFam_q8 hc2 hq
  oddFree := oddCore_quot_eq_bot
  aEmpty := secFam_aEmpty hΩ hA hc2
  gen := omegaGen_quotFamily_eq_top _ _
    (omegaGen_restrictFamily_eq_top (cFam Ω c) (coreHull Ω c) rfl)

end Sec

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
