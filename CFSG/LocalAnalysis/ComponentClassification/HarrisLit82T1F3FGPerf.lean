module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGCoreLie
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGCoreSpor
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAlt
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLie

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup Assembly.LowTwoRank

section Certified


theorem knownRowThree_perfect {G : Type} [Group G] [Finite G]
    (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G))
    (hcat : Blueprint.Catalog (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
      Open.fusionZStar ↥(GH74.GLS.oPrimeResidual 2 G)))
    {z : G} (hz : orderOf z = 2) {L : Subgroup G} (hL : IsTwoComponentIn L (centralizer {z}))
    (hzL : z ∈ L) (hT : PerfType3 ↥L) :
    IsChevalleyOver 3 (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
        pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) ∨
      Nonempty (G ⧸ pPrimeCore 2 G ≃* ↥Blueprint.NativeSporadic.M11) := by
  set Y := GH74.GLS.oPrimeResidual 2 G
  by_cases hp' : LieChar 3 (↥Y ⧸ Open.fusionZStar ↥Y)
  · obtain ⟨τ, n, f, hm⟩ := hp'
    obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥Y
    exact .inl (.inl ⟨hY.2, τ, n, f, GSThmB.OddQuot.lieModel_of_equiv eZ hm⟩)
  rcases hcat with ⟨q, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, r, f, hm⟩ | hex | hsp
  ·
    exfalso
    obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥Y
    obtain ⟨a, b, hab⟩ := hY.2.2.2
    apply hab
    apply (eZ.symm.trans e).injective
    rw [map_mul, map_mul, mul_comm]
  · exact .inl (rowFor3_of_core (fun S S' _ _ e h => RowAlt.alt_of_mulEquiv 3 S S' e h)
      rowCore3_alt G hY z hz L hL hzL hT ⟨⟨n, hn, ⟨e⟩⟩, hp'⟩)
  · have hLie : LieChar r (↥Y ⧸ Open.fusionZStar ↥Y) :=
      ⟨t, n, f, .inl ⟨by
        rcases Milestones.statedClassicalModel_tag_mem _ t n r f hm with h | h | h | h | h | h <;>
          subst h <;> decide, hm⟩⟩
    exact .inl (rowFor3_of_core (fun S S' _ _ e h => RowLie.lieOther_of_mulEquiv 3 S S' e h)
      rowCore3_lieOther G hY z hz L hL hzL hT ⟨⟨r, fun h => hp' (h ▸ hLie), hLie⟩, hp'⟩)
  · have hLie : ∃ r : ℕ, LieChar r (↥Y ⧸ Open.fusionZStar ↥Y) := by
      rcases hex with ⟨t, r, f, ht, hm⟩ | ⟨t, r, f, ht, hm⟩ | ⟨r, f, hm⟩
      · exact ⟨r, t, 0, f, .inr (.inl ⟨rfl, ht, hm⟩)⟩
      · exact ⟨r, t, 0, f, .inr (.inr (.inl ⟨rfl, ht, hm⟩))⟩
      · exact ⟨r, .twistedB2, 0, f, .inr (.inr (.inr ⟨rfl, rfl, hm⟩))⟩
    obtain ⟨r, hLie⟩ := hLie
    exact .inl (rowFor3_of_core (fun S S' _ _ e h => RowLie.lieOther_of_mulEquiv 3 S S' e h)
      rowCore3_lieOther G hY z hz L hL hzL hT ⟨⟨r, fun h => hp' (h ▸ hLie), hLie⟩, hp'⟩)
  · by_cases hm11 : Nonempty (↥Y ⧸ Open.fusionZStar ↥Y ≃* ↥Blueprint.NativeSporadic.M11)
    · exact .inr (nonempty_quotient_equiv_m11 hY hm11.some)
    · exact .inl (rowFor3_of_core (fun S S' _ _ e h => RowAlt.spor_of_mulEquiv e h)
        rowCore3_spor G hY z hz L hL hzL hT ⟨hsp, hm11⟩)

end Certified

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
