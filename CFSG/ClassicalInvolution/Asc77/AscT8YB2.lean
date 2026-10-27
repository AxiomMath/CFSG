module

public import CFSG.ClassicalInvolution.Asc77.AscT8YB1
public import CFSG.ClassicalInvolution.Asc77.AscT7V3
public import CFSG.ClassicalInvolution.Asc77.AscT7FD

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab

namespace T8YY


variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem frame_prod_eq_one (c : Ctx p f Ω W) (hnc : ¬ DbarConnected Ω W)
    (ρ : Fin 4 → Rep Ω W) (hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K)
    (hadj : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) {zz : Fin 4 → G}
    (hz : ∀ i, IsUniqueInvolution (ρ i).K (zz i)) : zz 0 * zz 1 * zz 2 * zz 3 = 1 := by
  obtain ⟨σ, tt, g, ht, -, hg, hrel⟩ := c.exists_relation hnc ρ hne hadj
  have hgW : ∀ i, g i ∈ W := fun i => (hg i).1.2
  have hsq : ∀ i, g i ^ 2 = zz i := by
    intro i
    have h4 : g i ^ 4 = 1 := by rw [← (hg i).2]; exact pow_orderOf_eq_one _
    have hmem : g i * g i ∈ (ρ i).K := (ρ i).K.mul_mem (hg i).1.1 (hg i).1.1
    have hyy : (g i * g i) * (g i * g i) = 1 := by
      have : (g i * g i) * (g i * g i) = g i ^ 4 := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [this, h4]
    rcases (hz i).unique _ hmem hyy with h | h
    · exfalso
      have h2 : g i ^ 2 = 1 := by rw [pow_two]; exact h
      have := orderOf_dvd_of_pow_eq_one h2
      rw [(hg i).2] at this
      omega
    · rw [pow_two]; exact h
  have hcomm : ∀ x y : G, x ∈ W → y ∈ W → Commute x y := fun x y hx hy => c.comm_W x hx y hy
  have hW01 : g 0 * g 1 ∈ W := W.mul_mem (hgW 0) (hgW 1)
  have hW012 : g 0 * g 1 * g 2 ∈ W := W.mul_mem hW01 (hgW 2)
  have hexp : (g 0 * g 1 * g 2 * g 3) ^ 2 = g 0 ^ 2 * g 1 ^ 2 * g 2 ^ 2 * g 3 ^ 2 := by
    rw [(hcomm _ _ hW012 (hgW 3)).mul_pow, (hcomm _ _ hW01 (hgW 2)).mul_pow,
      (hcomm _ _ (hgW 0) (hgW 1)).mul_pow]
  have ht2 : tt ^ 2 = 1 := by rw [pow_two]; exact ht.sq
  calc zz 0 * zz 1 * zz 2 * zz 3 = g 0 ^ 2 * g 1 ^ 2 * g 2 ^ 2 * g 3 ^ 2 := by
        rw [hsq 0, hsq 1, hsq 2, hsq 3]
    _ = (g 0 * g 1 * g 2 * g 3) ^ 2 := hexp.symm
    _ = 1 := by rw [← hrel]; exact ht2

theorem exists_rep_not_mem_dComp (hs : Std8 p f Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ∃ σ : Rep Ω W, σ.K ∉ dComp Ω K := by
  by_contra hcon
  push Not at hcon
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  obtain ⟨K₁, hK₁d, J₁, hJ₁, hJ₁n⟩ := exists_boundary_of_dComp_ne hp hq hΩ hK hne
  have hK₁ : K₁ ∈ Ω := mem_of_mem_dComp' hK hK₁d
  obtain ⟨g, ρ, σ, hρ, hσ⟩ := c.exists_conj_reps_of_mem_omegaStarNbr hK₁ hJ₁
  have h1 : ρ.K ∈ dComp Ω K := hcon ρ
  have h2 : σ.K ∈ dComp Ω K := hcon σ
  have h3 : σ.K ∈ dComp Ω ρ.K := by
    rw [T8.dComp_eq_of_mem hK h1]
    exact h2
  rw [hρ, hσ] at h3
  have h4 := mem_dComp_conjSub hΩ.conjInvariant h3 g⁻¹
  rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h4
  exact hJ₁n (dComp_trans' hK₁d h4)

theorem mgrp_not_le_sigmaNorm (hs : Std8 p f Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ MGrp Ω W ≤ sigmaNorm Ω K := by
  intro hle
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  obtain ⟨σ, hσ⟩ := exists_rep_not_mem_dComp hs hne
  obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hnc (T8.stdRepK hs) σ
  have hK' : conjSub m K ∈ dComp Ω K := (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).mp (hle hm)
  rw [T8.stdRepK_K hs] at hmK
  rw [hmK] at hK'
  exact hσ hK'

structure FrameData (Ω : Set (Subgroup G)) (W K J : Subgroup G) (z t : G) where
  ρ : Fin 4 → Rep Ω W
  zz : Fin 4 → G
  h0 : (ρ 0).K = K
  h1 : (ρ 1).K = J
  hz : ∀ i, IsUniqueInvolution (ρ i).K (zz i)
  hz0 : zz 0 = z
  hz1 : zz 1 = t
  hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K
  hadj : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K
  hclos : ∀ (σ : Rep Ω W) (i : Fin 4), (σ.K = (ρ i).K ∨ σ.K ∈ omegaNbr Ω (ρ i).K) →
    ∃ j, σ.K = (ρ j).K
  hprod : zz 0 * zz 1 * zz 2 * zz 3 = 1
  hinj : ∀ i j, i ≠ j → zz i ≠ zz j
  hW : ∀ i, zz i ∈ W

theorem exists_frameData (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) : Nonempty (FrameData Ω W K J z t) := by
  classical
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  obtain ⟨ρ, h0, h1, hne, hadj, hclos⟩ := exists_frame_closed hs hμ hnc
  have hex : ∀ i, ∃ zi : G, IsUniqueInvolution (ρ i).K zi := fun i =>
    hΩ.exists_uniqueInvolution hs.stand.odd hs.stand.five (ρ i).hK
  choose zz hz using hex
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  refine ⟨⟨ρ, zz, h0, h1, hz, ?_, ?_, hne, hadj, hclos, frame_prod_eq_one c hnc ρ hne hadj hz,
    ?_, fun i => mem_W_of_uniqueInvolution c (ρ i) (hz i)⟩⟩
  · exact (hz 0).eq (by rw [h0]; exact hs.hz)
  · exact (hz 1).eq (by rw [h1]; exact hs.ht)
  · intro i j hij heq
    have hmem : (ρ j).K ∈ twinSet Ω (ρ i).K :=
      ⟨(ρ j).hK, zz j, heq ▸ hz i, hz j⟩
    exact hne j i (Ne.symm hij) (hnt _ (ρ i).hK _ hmem)

namespace FrameData

variable {W K J : Subgroup G} {z t : G}

theorem mgrp_le_centralizer (c : Ctx p f Ω W) (F : FrameData Ω W K J z t) (i j : Fin 4) :
    MGrp Ω W ≤ Subgroup.centralizer ({F.zz i * F.zz j} : Set G) := by
  refine iSup₂_le fun R'' hR'' x hx => ?_
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_frame_prod_of_mem_DSet c F.ρ F.hadj F.hclos F.hz hR'' hx i j)

theorem mul_ne_one (F : FrameData Ω W K J z t) (i j : Fin 4) (hij : i ≠ j) :
    F.zz i * F.zz j ≠ 1 := by
  intro h
  have : F.zz i = F.zz j := by
    have h' := congrArg (· * F.zz j) h
    simpa [mul_assoc, (F.hz j).sq] using h'
  exact F.hinj i j hij this

end FrameData

end T8YY

end CFSG.ClassicalInvolution.Asc77
