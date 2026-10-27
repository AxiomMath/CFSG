module

public import CFSG.ClassicalInvolution.Q3.Q3AM710Cls
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf10Hyp51
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Alpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Fourth

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)
open scoped commutatorElement

section Three

section Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

open Classical in
theorem card_twins_ne_three (hP : Q3CL.PartIHypG Ω) (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (hperp : KPerp Ω K = twinSet Ω K)
    (hV : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (ρ : Subgroup G → Rep Ω W) (hρ : ∀ M ∈ ({K, K', K₃} : Finset (Subgroup G)), (ρ M).K = M)
    (hnc : ¬ DbarConnected Ω W) : False := by
  classical
  set S : Finset (Subgroup G) := {K, K', K₃} with hSdef
  have hKS : K ∈ S := by simp [hSdef]
  have hS : ∀ M ∈ S, M ∈ twinSet Ω K := by
    intro M hM
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton] at hM
    rcases hM with rfl | rfl | rfl
    · exact mem_twinSet_self hd.mem hd.hz
    · exact hd.hK'
    · exact hd.hK₃
  set g : Subgroup G → ↥(muGroup Ω W) := fun M => muTabElt (ρ M) with hg
  have hinj : Set.InjOn g (↑S : Set (Subgroup G)) := by
    intro M hM M' hM' e
    have := (Q3T6.Mu.muTabElt_eq_iff hP hW (ρ M) (ρ M')).mp e
    rwa [hρ M hM, hρ M' hM'] at this
  have hset : Star3T.cent (muDelta Ω W) (g K) = ↑(S.image g) := by
    ext y
    constructor
    · intro hy
      rcases Q3AM710.cent_subset hP hW (ρ K) hy with h | ⟨τ, rfl, hτ⟩
      · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨K, hKS, h.symm⟩)
      · have hτK : (τ.K) ∈ twinSet Ω K := by
          rw [← hperp]
          exact Or.inr (by rw [hρ K hKS] at hτ; exact hτ)
        have hτS : τ.K ∈ S := by
          rcases hV _ hτK with h | h | h <;> simp [hSdef, h]
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨τ.K, hτS, ?_⟩)
        exact (Q3T6.Mu.muTabElt_eq_iff hP hW (ρ τ.K) τ).mpr (hρ τ.K hτS)
    · intro hy
      obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      refine ⟨muTabElt_mem _, ?_⟩
      by_cases hMK : M = K
      · rw [hMK]
      · have hnb : (ρ M).K ∈ omegaNbr Ω (ρ K).K := by
          rw [hρ M hM, hρ K hKS]
          exact adj_of_twins' hd hperp (hS K hKS) (hS M hM) hMK
        exact ((Q3T6.Mu.muTab_commute_iff hP hW (ρ K) (ρ M)
          (by rw [hρ M hM, hρ K hKS]; exact Ne.symm hMK)).mpr hnb).symm
  have hcard : (Star3T.cent (muDelta Ω W) (g K)).ncard = 3 := by
    rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]
    have h1 : K ≠ K' := hd.hne.symm
    have h2 : K ≠ K₃ := hd.hK₃K.symm
    have h3 : K' ≠ K₃ := hd.hK₃K'.symm
    simp [hSdef, Finset.card_insert_of_notMem, h1, h2, h3]
  rcases Q3T8.Asc77.thompsonClique G Ω hP W hW hnc (g K) (muTabElt_mem _) with h | h | ⟨h, -⟩ <;>
    omega

end Gen

section Named

variable {n : ℕ}

@[expose] def V3Hyp51U3E8 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → ¬ TwinE4 Y →
      ∀ (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y),
        A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ →
          (∀ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M = K ∨ M = K' ∨ M = K₃) →
            ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
              (∃ ρ : Rep (CoreAssembly.conjClass (tightCore R)) W, ρ.K = K) →
                DbarConnected (CoreAssembly.conjClass (tightCore R)) W →
                  Hyp51At (Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y)) (u₁ * u₂)

theorem v3Hyp51U3_of_conn (h : V3Hyp51U3E8 n) : V3Hyp51U3 n := by
  classical
  intro Y _ _ R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d hV
  have hC := CoreData.of_S hP.core
  have hPG := hC.partIHypG
  have hperp := kPerp_datum hP d.mem d.hz
  obtain ⟨W, hW, ρ, hρ⟩ := exists_reps_of_family' d.hyp d.hz ({K, K', K₃} : Finset (Subgroup Y))
    (by simp) (by
      intro M hM
      simp only [Finset.mem_insert, Finset.mem_singleton] at hM
      rcases hM with rfl | rfl | rfl
      · exact mem_twinSet_self d.mem d.hz
      · exact d.hK'
      · exact d.hK₃)
  by_cases hconn : DbarConnected (CoreAssembly.conjClass (tightCore R)) W
  · exact h Y R S t hP h3 hE K K' K₃ u₁ u₂ u₃ d hV W hW ⟨ρ K, hρ K (by simp)⟩ hconn
  · exact (card_twins_ne_three hPG d hperp hV hW ρ hρ hconn).elim

end Named

end Three

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
