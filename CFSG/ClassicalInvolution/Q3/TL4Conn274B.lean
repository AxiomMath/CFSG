module

import CFSG.ClassicalInvolution.Q3.Q3CLFrame274
import CFSG.StronglyEmbedded.UniqueCosetFixedEng
public import CFSG.ClassicalInvolution.Q3.Q3CLFrame

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Asc77.AscP1Nine3
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.StronglyEmbedded.UniqueCoset
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem mem_H274_of_min (hs : Std8Core Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    (hmin : ∀ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) →
      8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)} →
        ∀ x : G, x ∈ (S₂ : Subgroup G) → x * x = 1 → x ≠ 1 →
          (∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) →
            Subgroup.centralizer ({x} : Set G) ≤ H274 Ω K z)
    {g : G} (hgH : g⁻¹ * (z * t) * g ∈ H274 Ω K z) : g ∈ H274 Ω K z :=
  Q3CL.Frame.T8.mem_H274_of_min hs.toFrame hcomp hmin hgH

theorem fixesUniqueCoset_zt_of_min (hs : Std8Core Ω K J S R T W z t)
    (hcomp : dComp Ω K = dstarComp Ω K)
    (hmin : ∀ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) →
      8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)} →
        ∀ x : G, x ∈ (S₂ : Subgroup G) → x * x = 1 → x ≠ 1 →
          (∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) →
            Subgroup.centralizer ({x} : Set G) ≤ H274 Ω K z) :
    FixesUniqueCoset (z * t) (H274 Ω K z) := by
  have hzt : z * t ∈ H274 Ω K z :=
    centralizer_mul_le_H274 hs.hJ hs.ht (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  refine CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_mem hzt (fun g hg => ?_)
  exact mem_H274_of_min hs hcomp hmin hg

end CFSG.ClassicalInvolution.Q3.TL4
