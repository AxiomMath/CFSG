module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93Dispatch
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.Level

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem i9List93At_of_residual (G : Type) [Group G] [Finite G] (p : ℕ)
    (hM : ListedMultiplierBound p) (hH : HatOddMultiplierBound) (hR23 : Rank23At G)
    (hF : I9List93Residual) : I9List93At G p := by
  intro hp hp2 X L B _hX hL hC2 hlev hB hBN hcard hH4
  have hk : IsChevSimple p (PSimple p L) ∨ catalogIs (PSimple p L) (k2 p) := by
    rw [fullCoverLevel_pQuot_eq hM hH hp hp2 hL] at hlev
    unfold kLevel at hlev
    by_cases h1 : IsChevSimple p (PSimple p L)
    · exact Or.inl h1
    · by_cases h2 : catalogIs (PSimple p L) (k2 p)
      · exact Or.inr h2
      · rw [if_neg h1, if_neg h2] at hlev
        split_ifs at hlev <;> omega
  rcases i9List93_dispatch hF hp hp2 (PSimple p L) hC2 hk with h | ⟨rfl, h94⟩ | hnoE
  · exact h
  · obtain ⟨hcenter, hD4, -⟩ := hR23 X L hL h94
    rcases hH4 with ⟨b, hb, hnin⟩ | hdvd
    · have hpow : b ^ 3 = 1 := hB.2 b hb
      have hD := hD4 b (hBN hb) hpow hnin
      exact List93.catalogIs_mono (fun i hi => Or.inr ⟨rfl, Or.inl hi⟩) hD
    · rw [hcenter, Subgroup.card_bot] at hdvd
      exact absurd hdvd (by norm_num)
  · exact absurd (exists_elemAb_chevAut hp hL hB hBN hcard) hnoE

end CFSG.LocalAnalysis.GLTheoremA

end
