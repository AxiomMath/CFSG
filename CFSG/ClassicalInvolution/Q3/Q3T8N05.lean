module

public import CFSG.ClassicalInvolution.Q3.Q3T8Std8
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
public import CFSG.ClassicalInvolution.Q3.Q3T8Sect
public import CFSG.ClassicalInvolution.Q3.Q3T8C262Stmt
public import CFSG.ClassicalInvolution.Q3.Q3T8C261
public import CFSG.ClassicalInvolution.Q3.Q3T8C262A
public import CFSG.ClassicalInvolution.Q3.Q3T8ThompsonD
public import CFSG.ClassicalInvolution.Q3.Q3T8E4Base
public import CFSG.ClassicalInvolution.Q3.Q3T8L278A
public import CFSG.ClassicalInvolution.Q3.Q3T8L278B
public import CFSG.ClassicalInvolution.Q3.Q3T8C262Sec
public import CFSG.ClassicalInvolution.Q3.Q3T7E9BarNbr
public import CFSG.ClassicalInvolution.Q3.Q3T8E4A
public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen
public import CFSG.ClassicalInvolution.Q3.Q3T8E4B
public import CFSG.ClassicalInvolution.Q3.Q3T8NTri
public import CFSG.ClassicalInvolution.Q3.Q3T8E4NRDef
public import CFSG.ClassicalInvolution.Q3.Q3T8N01
public import CFSG.ClassicalInvolution.Q3.Q3T8N02
public import CFSG.ClassicalInvolution.Q3.Q3T8NTri
public import CFSG.ClassicalInvolution.Asc77.AscT8Y3
public import CFSG.ClassicalInvolution.Asc77.AscT8Y4
public import CFSG.ClassicalInvolution.Q3.Q3T7M04

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Rep
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
end Rep
section Std
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
end Std
section Klein
variable {Q : Type} [Group Q]
end Klein
section Dichotomy
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
end Dichotomy
section LayerTri
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem dstarConnected_layerFam3_of_reps {K₀ : Subgroup G} (hst : AscStand Ω K₀)
    {W : Subgroup G} (hP : PartIHyp Ω) (hW : W ∈ WSet Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) (ρ : Fin 3 → Rep Ω W) (zz : Fin 3 → G)
    (hzz : ∀ i, IsUniqueInvolution (ρ i).K (zz i)) (hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K)
    (hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K)
    (hnc : ¬ ({zz 0 * zz 1} : Set G) ⊆ Subgroup.center G) :
    T3.DStarConnected (Q3T7.layerFam3 Ω (zz 0 * zz 1)) := by
  have c := Q3CL.T8.ctxOf hP hW
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hzW : ∀ i, zz i ∈ W := fun i =>
    (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW (ρ i).hK (ρ i).hR (ρ i).hRK (hzz i)).2
  have hzzc : ∀ i j, zz i * zz j = zz j * zz i := fun i j => c.comm_W _ (hzW i) _ (hzW j)
  have haa : zz 0 * zz 1 * (zz 0 * zz 1) = 1 := by
    calc zz 0 * zz 1 * (zz 0 * zz 1) = zz 0 * (zz 1 * zz 0) * zz 1 := by group
      _ = zz 0 * (zz 0 * zz 1) * zz 1 := by rw [hzzc 1 0]
      _ = (zz 0 * zz 0) * (zz 1 * zz 1) := by group
      _ = 1 := by rw [(hzz 0).sq, (hzz 1).sq, one_mul]
  have haW : zz 0 * zz 1 ∈ W := W.mul_mem (hzW 0) (hzW 1)
  have hrel : ∀ i j, (ρ j).K = (ρ i).K ∨ (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j
    by_cases h : i = j
    · subst h
      exact Or.inl rfl
    · exact Or.inr (hnbr i j h)
  have hRc : ∀ i j, (ρ i).R ≤ Subgroup.centralizer ({zz j} : Set G) := fun i j =>
    rep_le_centralizer c (ρ i) (ρ j) (hrel i j) (hzz j)
  have hRa : ∀ i, (ρ i).R ≤ cenZ (zz 0 * zz 1) := by
    intro i r hr
    rw [mem_cenZ_iff]
    have h0 := Subgroup.mem_centralizer_singleton_iff.mp (hRc i 0 hr)
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hRc i 1 hr)
    calc r * (zz 0 * zz 1) = (r * zz 0) * zz 1 := by group
      _ = (zz 0 * r) * zz 1 := by rw [h0]
      _ = zz 0 * (r * zz 1) := by group
      _ = zz 0 * (zz 1 * r) := by rw [h1]
      _ = (zz 0 * zz 1) * r := by group
  have hX : ∀ i, XMem Ω (zz 0 * zz 1) (ρ i).K := by
    intro i
    refine ⟨(ρ i).hK, ?_, (ρ i).R, (ρ i).hRK, fun r hr => mem_cenZ_iff.mp (hRa i hr)⟩
    exact centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (ρ i).hK (hnt _ (ρ i).hK) (hzz i)
      (Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_W _ haW (zz i) (hzW i)))
  have hzne : ∀ i j, i ≠ j → zz i ≠ zz j := by
    intro i j hij h
    have hj : IsUniqueInvolution (ρ j).K (zz i) := by rw [h]; exact hzz j
    exact hne i j hij (hnt _ (ρ i).hK _ ⟨(ρ j).hK, zz i, hzz i, hj⟩).symm
  have hKt : ∀ i, (ρ i).K ∈ Q3NL.tqMembers3 Ω (zz 0 * zz 1) := fun i =>
    (hX i).mem_tqMembers3 hΩ haa
  have hs3 : Q3.Disc3.AscStand3 Ω K₀ := hst.toStand3
  have hL : Layer.LayerHyp Ω (zz 0 * zz 1) := Layer.LayerHyp.of_stand3 hs3 haa ⟨_, hKt 0⟩
  have hne0 : (Q3NL.tqMembers3 Ω (zz 0 * zz 1)).Nonempty := ⟨_, hKt 0⟩
  have himg : ∀ i j, i ≠ j →
      Layer.layerImg3 Ω (zz 0 * zz 1) (ρ i).K ≠ Layer.layerImg3 Ω (zz 0 * zz 1) (ρ j).K := fun i j
          hij =>
    Layer.layerImg3_ne_of_involutions hL (hX i) (hX j) (hzz i) (hzz j) (hzzc i j)
      (hzne i j hij)
  have hadj : ∀ i j, i ≠ j → Layer.layerImg3 Ω (zz 0 * zz 1) (ρ j).K ∈
      omegaNbr (Q3T7.layerFam3 Ω (zz 0 * zz 1)) (Layer.layerImg3 Ω (zz 0 * zz 1) (ρ i).K) := by
    intro i j hij
    refine Layer.layerImg3_omegaNbr (hKt i) (hKt j) (ρ j).hRK (hRa j) ?_ (himg i j hij)
    exact hΩ.le_normalizer_of_le_centralizer (ρ i).hK (ρ j).hK (hne i j hij) (hzz i)
      (ρ j).hRK.1 (ρ j).hRK.2.1
      (by have := hΩ.eight_le_of_mem_RSet (ρ j).hR.1; omega) (hRc j i)
  have hlt := Q3T7.card_layerQuot3_lt (Ω := Ω) hnc
  exact dstarConnected_of_triangle3 hst.ih hst.below hlt
    (Q3T7.hypOmegaModU_layerFam3 hs3 hL.hc2 hne0) Q3T7.layerQuot3_oddCore_eq_bot
    (Q3T7.omegaGen_layerFam3 hs3 hL.hc2 hne0) (Q3T7.aEmpty_layerFam3 hs3 hL.hc2 hne0)
    (fun i => Layer.layerImg3 Ω (zz 0 * zz 1) (ρ i).K) (fun i => Layer.layerImg3_mem (hKt i))
    (fun i j h => by
      by_contra hij
      exact himg i j hij h) hadj
end LayerTri
end T8
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Conj
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
end Conj
section Cases
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem dstarConnected_layerFam3_of_abelian [IsSimpleGroup G]
    (hs : Std8 Ω K J S R T W z t) (hE4 : ¬ MuIsoE4 Ω W)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) :
    T3.DStarConnected (Q3T7.layerFam3 Ω (z * t)) := by
  have hP := partIHyp_of_std8 hs
  have hc := Q3CL.T8.ctxOf hP hs.hW.1
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨τ, hτK, hτJ⟩ := exists_third_of_abelian hs hE4 hab
  obtain ⟨z₂, hz₂⟩ := hΩ.exists_uniqueInvolution τ.hK
  let ρ : Fin 3 → Rep Ω W := ![stdRepK hs, stdRepJ hs, τ]
  let zz : Fin 3 → G := ![z, t, z₂]
  have hzz : ∀ i, IsUniqueInvolution (ρ i).K (zz i) := by
    intro i
    fin_cases i
    · exact hs.hz
    · exact hs.ht
    · exact hz₂
  have hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hs.hJ.2.1.symm
    · exact hτK.symm
    · exact hs.hJ.2.1
    · exact absurd rfl hij
    · exact hτJ.symm
    · exact hτK
    · exact hτJ
    · exact absurd rfl hij
  have hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j hij
    refine (repElt_commute_iff hc (ρ i) (ρ j) (hne i j hij)).mp ?_
    exact Subtype.ext (hab _ (repElt (ρ i)).2 _ (repElt (ρ j)).2)
  exact dstarConnected_layerFam3_of_reps hs.stand hP hs.hW.1 hnt ρ zz hzz hne hnbr
    (Layer.zt_not_central3 hs)
end Cases
end T8
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
