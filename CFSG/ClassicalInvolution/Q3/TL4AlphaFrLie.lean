module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdLieNR
public import CFSG.ClassicalInvolution.Q3.Q3T8AFZ03
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdentLie

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Uniform

section Cit3


variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem SecIdLie3.linkGen (hd : TightDatum R S t) (hc : TightCls Y R S t) (hl : SecIdLie3 R t)
    {B : Subgroup Y} (hB : B ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    {v : Y} (hv : IsUniqueInvolution B v) :
    Subgroup.centralizer ({t} : Set Y) ⊔ Subgroup.centralizer ({v} : Set Y) ⊔
      Subgroup.centralizer ({t * v} : Set Y) = ⊤ := by
  set Δ := CoreAssembly.conjClass (tightCore R) with hΔ
  have hΩ : HypOmegaGen Δ := hd.hypOmegaGen
  have hK : tightCore R ∈ Δ := CoreAssembly.mem_conjClass_self _
  have ht := hd.isUniqueInvolution_core
  have hnt : ∀ L ∈ Δ, ∀ L' ∈ twinSet Δ L, L' = L := fun L hL' =>
    T8.noTwins_of_mem hΩ.conjInvariant (fun J hJ => hJ) (fun K' hK' => by
      rw [hd.twinSet_eq] at hK'
      exact hK') hL'
  have h2 : ∀ J ∈ Δ, IsPGroup 2 ↥J := hl.isPGroup_members hc.2.2
  have hO : classicalInvolutionOddCore Y = ⊥ := hc.2.2
  have hlifts := hl.hasLifts hd
  have hOC := hl.oddCoreIn_centralizer_eq_bot hc.2.2
    (orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one)
  obtain ⟨hΛ, -, -⟩ := hl.liftFam_hyp hd hc
  have hntΛ := SecIdLie3.liftFam_noTwins hd hnt
  obtain ⟨L, hKL, hLm, -, hLie⟩ := hl
  have hlift : IsLiftOf (tightCore R) L t := ⟨ht, hKL, hLm⟩
  have hfam : liftFam Δ = CoreAssembly.conjClass L := by
    rw [liftFam_conjClass hΩ hlift, satU_eq_of_oddCoreIn_eq_bot hOC]
  rw [← hfam] at hLie
  obtain ⟨ι, -, ⟨D⟩⟩ := TwinIdent.lieSystem3_of_oddCore_eq_bot hO hLie
  have hMA : L ∈ liftFam Δ := by
    have := satU_mem_liftFam hK hlift
    rwa [satU_eq_of_oddCoreIn_eq_bot hOC] at this
  obtain ⟨LB, uB, hLB⟩ := hlifts B hB.1
  have hMB := satU_mem_liftFam hB.1 hLB
  have htL : IsUniqueInvolution L t := isUniqueInvolution_liftFam_of_le hMA ht hKL
  have hvM : IsUniqueInvolution (satU (.sl2 3 1) LB uB) v :=
    isUniqueInvolution_liftFam_of_le hMB hv hLB.le_sat
  have hBΛ := mem_omegaNbr_liftFam_of_mem hΩ h2 hK hMA hKL hMB hLB.le_sat hB
  obtain ⟨i, R₁, hR₁, hLR⟩ := D.fundamental L hMA
  obtain ⟨j, R₂, hR₂, hMR⟩ := D.fundamental _ hMB
  have htR : t ∈ R₁.map (D.hom i) := hLR ▸ htL.mem
  have hvR : v ∈ R₂.map (D.hom j) := hMR ▸ hvM.mem
  obtain ⟨r, -, hr⟩ := htR
  obtain ⟨s, -, hs⟩ := hvR
  have hcomp : ∀ k, k ≠ i → (D.hom k).range ≤ Subgroup.centralizer ({t} : Set Y) := by
    intro k hk
    rintro _ ⟨r', rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hr]
    exact D.commute k i hk r' r
  rw [eq_top_iff, ← D.generate]
  refine iSup_le fun k => ?_
  by_cases hk : k = i
  · subst hk
    by_cases hj : j = k
    · subst hj
      obtain ⟨hgenZ, -⟩ := Q3T8.Asc77.zLinkFacts3_proved Y (liftFam Δ) ι D hΛ hntΛ L _ hMA hBΛ
        j R₁ R₂ hR₁ hR₂ hLR hMR
      exact hgenZ t v htL hvM
    · rintro _ ⟨r', rfl⟩
      refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)
      rw [Subgroup.mem_centralizer_singleton_iff, ← hs]
      exact D.commute k j (Ne.symm hj) r' s
  · exact (hcomp k hk).trans (le_sup_left.trans le_sup_left)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
