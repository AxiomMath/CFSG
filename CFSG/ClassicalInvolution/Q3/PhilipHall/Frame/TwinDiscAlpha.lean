module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscSigma

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

namespace TwinDisc



section Alpha

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure AlphaSteps (Ω : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Ω
  trans : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : G, conjSub g M = N
  hyp51 : ∀ A ∈ frameSet Ω, Hyp51 A

namespace AlphaSteps

variable (hs : AlphaSteps Ω) {K K' J : Subgroup G} {z u t : G} (h : TwinFrameData Ω K K' z u J t)
include hs h

theorem alpha_eq : Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u, z} : Set G)))) ∧
    ∀ A : Subgroup G, A ≤ Subgroup.closure ({z, u, t} : Set G) → IsElemAbelian2 A 2 →
      alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hle : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) :=
    Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp)
  exact lemma54_odd_and_eq (hs.hyp51 _ (closure_mem_frameSet h)) hle
    (isElemAbelian2_closure_uz hs.hyp h)

theorem alpha_zt : alphaOf (Subgroup.closure ({z, t} : Set G)) =
    alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  obtain ⟨hB, -⟩ := shape_of_frameData hs.hyp h
  have hle : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) :=
    Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp)
  exact (hs.alpha_eq h).2 _ hle
    (isElemAbelian2_of_mem_signalizer hB (closure_zt_mem hs.hyp h))

theorem exists_mem_normalizer {M : Subgroup G} (hM : M ∈ dComp Ω K) :
    ∃ y ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G),
      conjSub y K = M := by
  obtain ⟨y, hy⟩ := hs.trans K h.mem M (mem_of_mem_dComp h.mem hM)
  exact ⟨y, mem_normalizer_alpha_of_mem_dComp hs.hyp hs.trans hs.hyp51 h (hy ▸ hM), hy⟩

theorem centralizer_le :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
  centralizer_le_normalizer_alpha hs.hyp hs.trans hs.hyp51 h

theorem twin_le {L : Subgroup G} (hL : L ∈ twinSet Ω K) :
    L ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
  twin_le_normalizer_alpha hs.hyp h (hs.alpha_eq h).2 hL

theorem sup_le_normalizer :
    K ⊔ K' ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
  sup_le (hs.twin_le h (mem_twinSet_self h.mem h.hz)) (hs.twin_le h h.hK')

end AlphaSteps

end Alpha

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
