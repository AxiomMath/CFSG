module

public import CFSG.ClassicalInvolution.Q3.TL3T5

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]
variable {Ω : Set (Subgroup G)} {K : Subgroup G} (hS : ThinStd Ω K)
include hS

theorem ThinStd.nbrAdj_of_centX_mul {M N N' : Subgroup G} (hN : MaxAdj (nbrAdj Ω) M N)
    (hN' : MaxAdj (nbrAdj Ω) M N') (hne : N ≠ N') {u u' : G} (hu : IsUniqueInvolution N u)
    (hu' : IsUniqueInvolution N' u') (hc : CentX Ω M (u * u')) : nbrAdj Ω N N' := by
  have hNΩ := hN.1.2.1
  have hN'Ω := hN'.1.2.1
  have hN'u : ∀ n ∈ N', n * u = u * n := by
    intro n hn
    have h1 : (u * u') * n = n * (u * u') := hc N' hN' n hn
    have h2 : n * u' = u' * n := comm_of_conj_eq (hu'.conj_eq (conjSub_eq_self_of_mem hn))
    calc n * u = n * (u * u') * u'⁻¹ := by group
      _ = (u * u') * n * u'⁻¹ := by rw [← h1]
      _ = u * (u' * n) * u'⁻¹ := by group
      _ = u * (n * u') * u'⁻¹ := by rw [← h2]
      _ = u * n := by group
  have hN'N : N' ≤ Subgroup.normalizer (N : Set G) := fun n hn =>
    hS.tight N hNΩ u hu (Subgroup.mem_centralizer_singleton_iff.mpr (hN'u n hn))
  exact ⟨hNΩ, (mem_omegaNbr_iff hS.hyp hS.two).mpr ⟨hN'Ω, Ne.symm hne, hN'N⟩⟩

theorem ThinStd.maxAdj_of_centX_mul (hZ : Subgroup.center G = ⊥) {M N N' : Subgroup G}
    (hN : MaxAdj (nbrAdj Ω) M N) (hN' : MaxAdj (nbrAdj Ω) M N') (hne : N ≠ N') {u u' : G}
    (hu : IsUniqueInvolution N u) (hu' : IsUniqueInvolution N' u') (hc : CentX Ω M (u * u')) :
    MaxAdj (nbrAdj Ω) N N' := by
  by_contra hmax
  have hF := hS.graphFam
  have hadj := hS.nbrAdj_of_centX_mul hN hN' hne hu hu' hc
  have hNM : MaxAdj (nbrAdj Ω) N M := ⟨hF.graph.symm hN.1, orbOf_mem_maxOrbs hF hN.1 hN.2⟩
  have hsep : ∀ L : Subgroup G, MaxAdj (nbrAdj Ω) N L → ∀ l ∈ L, ∀ n ∈ N', l * n = n * l := by
    intro L hL
    have hnot : N' ∉ orbOf (nbrAdj Ω) N L := by
      intro h
      apply hmax
      refine ⟨hadj, ?_⟩
      rw [orbOf_eq_of_mem h]
      exact hL.2
    exact hS.commutes_of_nbrAdj (hS.sep hL.1 hadj hnot)
  have hcN : CentX Ω N (u * u') := by
    intro L hL l hl
    have h1 := hsep L hL l hl u' hu'.mem
    have h2 := hS.commutes_of_nbrAdj hL.1 u hu.mem l hl
    calc u * u' * l = u * (u' * l) := by group
      _ = u * (l * u') := by rw [← h1]
      _ = (u * l) * u' := by group
      _ = (l * u) * u' := by rw [h2]
      _ = l * (u * u') := by group
  have hcen : u * u' ∈ Subgroup.center G := by
    have hle : (⨆ J ∈ Ω, J) ≤ Subgroup.centralizer ({u * u'} : Set G) := by
      refine iSup₂_le fun J hJ => ?_
      refine (le_iSup_of_maxOrb hF hN.1 hN.2 J hJ).trans ?_
      refine iSup₂_le fun L hL => ?_
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hL with hL | hL
      · have hL' : MaxAdj (nbrAdj Ω) M L :=
          ⟨adj_of_mem_orbOf hF.graph hN.1 hL, by rw [orbOf_eq_of_mem hL]; exact hN.2⟩
        exact (hc L hL' l hl).symm
      · have hL' : MaxAdj (nbrAdj Ω) N L :=
          ⟨adj_of_mem_orbOf hF.graph hNM.1 hL, by rw [orbOf_eq_of_mem hL]; exact hNM.2⟩
        exact (hcN L hL' l hl).symm
    rw [hS.gen] at hle
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  rw [hZ, Subgroup.mem_bot] at hcen
  have heq : u' = u := by
    calc u' = u * (u * u') := by rw [← mul_assoc, hu.sq, one_mul]
      _ = u := by rw [hcen, mul_one]
  have hu'' : IsUniqueInvolution N' u := by
    rw [← heq]
    exact hu'
  exact hne (hS.eq_of_uniqueInvolution hN.1.2.1 hN'.1.2.1 hu hu'')

end CFSG.ClassicalInvolution.Q3.TC.Thin
