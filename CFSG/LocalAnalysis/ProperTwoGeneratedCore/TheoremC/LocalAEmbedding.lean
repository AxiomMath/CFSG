module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.LocalAQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X} {u z : X}

theorem fusionStronglyEmbedded_of_quasiHullTwoPointOdd (hc : CoreConfig Y u z)
    {a : X ⧸ CFSG.Open.pCore 2 X} (ha : orderOf a = 2)
    (haz : Commute a (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z))
    (hesc : ¬ Subgroup.centralizer ({a} : Set (X ⧸ CFSG.Open.pCore 2 X)) ≤
      Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)))
    (hodd : QuasiHullTwoPointOdd Y z (quasiPreimage a)) :
    fusionStronglyEmbedded ((Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X))).subgroupOf
      (localInvolutionPointHull (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z) a)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 X)
  set L := localInvolutionPointHull (π z) a
  set Yt := Y.map π
  refine ⟨?_, ?_, ?_⟩
  ·
    intro htop
    obtain ⟨c, hcC, hcY⟩ := Set.not_subset.mp hesc
    have hca : Commute c a := Subgroup.mem_centralizer_singleton_iff.mp hcC
    have hcz : c * π z * c⁻¹ ∈ L := by
      refine mem_localInvolutionPointHull (conj_mem_involutionPointClass' c) ?_
      exact (hca.mul_left haz.symm).mul_left hca.inv_left
    have hmem : (⟨_, hcz⟩ : L) ∈ Yt.subgroupOf L := htop ▸ Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at hmem
    exact hcY ((hc.conj_mk_lever_mem_iff c).mp hmem)
  ·
    have hzL : π z ∈ L := distinguished_mem_localInvolutionPointHull haz
    have hzY : (⟨π z, hzL⟩ : L) ∈ Yt.subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ hc.lever_mem)
    refine Nat.not_odd_iff_even.mp (not_odd_card_of_orderOf_eq_two hzY ?_)
    rw [Subgroup.orderOf_mk]
    exact hc.orderOf_mk_lever
  ·
    intro g hg
    by_contra hnodd
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2
      (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnodd))
    have hw1 : (w : L) ∈ Yt.subgroupOf L := w.2.1
    have hw2 : (w : L) ∈ (Yt.subgroupOf L).map (MulAut.conj g⁻¹).toMonoidHom := w.2.2
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv] at hw2
    rw [Subgroup.mem_subgroupOf] at hw1 hw2 hg
    have hLmap := map_quasiHull_eq ha z
    obtain ⟨x, hxQ, hx⟩ : ((w : L) : X ⧸ CFSG.Open.pCore 2 X) ∈
        (quasiHull z (quasiPreimage a)).map π := by
      rw [hLmap]
      exact (w : L).2
    obtain ⟨ℓ, hℓQ, hℓ⟩ : (g : X ⧸ CFSG.Open.pCore 2 X) ∈
        (quasiHull z (quasiPreimage a)).map π := by
      rw [hLmap]
      exact g.2
    have hword : orderOf (π x) = 2 := by
      rw [hx, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
    refine hodd x hxQ ?_ ?_ ℓ hℓQ ?_ ?_ ?_
    · rw [← mk_twoCore_eq_one_iff, map_mul, ← pow_two]
      simpa only [hword] using pow_orderOf_eq_one (π x)
    · rw [← mk_twoCore_eq_one_iff]
      intro h
      rw [h, orderOf_one] at hword
      exact absurd hword (by decide)
    · intro h
      apply hg
      rw [← hℓ]
      exact Subgroup.mem_map_of_mem _ h
    · rw [← hc.mk_mem_map_iff, hx]
      exact hw1
    · rw [← hc.mk_mem_map_iff, map_mul, map_mul, map_inv, hx, hℓ]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hw2

end CFSG.ProperTwoGeneratedCore.TheoremC
