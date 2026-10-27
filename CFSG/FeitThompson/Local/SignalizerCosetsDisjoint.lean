module

public import CFSG.FeitThompson.Local.SignalizerProductComponents

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Set Pointwise Subgroup CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep09

universe u

theorem FTS_signalizer_cosets_disjoint
    (h₁ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_signalizer_cosets_disjoint.{u} := by
  intro G _ _ hG x hx y hy hxy
  have hamb : IsFTAmbient G :=
    { isSimpleGroup := hG.isSimpleGroup
      not_isMulCommutative := hG.not_isMulCommutative
      odd_natCard := hG.odd_natCard
      isSolvable := hG.isSolvable_of_ne_top }
  have hpc := FTS_signalizer_product_components h₁ h₂ G hG
  have hself : ∀ z ∈ sigmaSupport G, ∀ t ∈ sigmaSignalizer z,
      z ∈ sigmaConstituents (z * t) := by
    intro z hz t ht
    rcases eq_or_ne t 1 with h | h
    · rw [((hpc z hz).1 t ht).1 h]; exact Set.mem_singleton z
    · rw [(((hpc z hz).1 t ht).2 h).1]; exact Set.mem_insert _ _
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro g ⟨hgx, hgy⟩
  obtain ⟨r, hr, hrg⟩ := Set.mem_smul_set.1 hgx
  obtain ⟨s, hs, hsg⟩ := Set.mem_smul_set.1 hgy
  rw [SetLike.mem_coe] at hr hs
  have heq : x * r = y * s := by
    have h1 : x * r = g := by simpa using hrg
    have h2 : y * s = g := by simpa using hsg
    rw [h1, h2]
  have hxin : x ∈ sigmaConstituents (y * s) := heq ▸ hself x hx r hr
  have hyin : y ∈ sigmaConstituents (x * r) := heq ▸ hself y hy s hs
  have hr1 : r ≠ 1 := by
    intro h
    rw [((hpc x hx).1 r hr).1 h] at hyin
    exact hxy (Set.mem_singleton_iff.1 hyin).symm
  have hs1 : s ≠ 1 := by
    intro h
    rw [((hpc y hy).1 s hs).1 h] at hxin
    exact hxy (Set.mem_singleton_iff.1 hxin)
  have hyr : y = r := by
    rw [(((hpc x hx).1 r hr).2 hr1).1] at hyin
    rcases hyin with h | h
    · exact absurd h.symm hxy
    · exact h
  have hxs : x = s := by
    rw [(((hpc y hy).1 s hs).2 hs1).1] at hxin
    rcases hxin with h | h
    · exact absurd h hxy
    · exact h
  have hyR : y ∈ sigmaSignalizer x := hyr ▸ hr
  have hxR : x ∈ sigmaSignalizer y := hxs ▸ hs
  obtain ⟨M, hM, hxM, hx1⟩ := mem_sigmaSupport.1 hx
  obtain ⟨-, -, -, hy1⟩ := mem_sigmaSupport.1 hy
  have hRne : sigmaSignalizer x ≠ ⊥ := fun h => hy1 (by simpa [h] using hyR)
  obtain ⟨N, hN, -, hRN, hxMN, -⟩ :=
    (h₁ G hamb x hx).2.2.2.2.2 hRne M (mem_sigmaSupportingMaximals.2 ⟨hM, hxM⟩)
  obtain ⟨-, hinter⟩ := (h₁ G hamb y hy).2.2.2.2.1 N
    (mem_sigmaSupportingMaximals.2 ⟨mem_maximalSubgroups.1 hN, hRN hyR⟩)
  have hmem : x ∈ sigmaSignalizer y ⊓ N := Subgroup.mem_inf.2 ⟨hxR, (Subgroup.mem_inf.1 hxMN).2⟩
  rw [hinter] at hmem
  exact hx1 (Subgroup.mem_bot.1 hmem)

end

end CFSG.FeitThompson.Proofs
