module

public import CFSG.ClassicalInvolution.Asc77.WP3S28BIndep
public import CFSG.ClassicalInvolution.Asc77.WP3S28BFuzzy
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalAll
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwAll
import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28B

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.SCV

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {z t z' : G}

theorem eq_conjClass_of_setting (hs : ChainFrameSetting p f Ω K J K' z t z') :
    Ω = CoreAssembly.conjClass K := by
  ext M
  constructor
  · intro hM
    obtain ⟨g, hg⟩ := hs.trans M hM
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    exact hs.hyp.conjInvariant g K hs.frame.mem

theorem thirdZTMod_of_dconn_noIndep (hs : ChainFrameSetting p f Ω K J K' z t z')
    (hD : DConnected Ω) (hno : ¬ CoreAssembly.IndepTriple p f Ω)
    {N : Subgroup G} (hN : N ∈ Ω) (hNK : N ≠ K) (hNJ : N ≠ J) (hzN : z ∈ trivialOnQuot N)
    (htN : t ∈ trivialOnQuot N) {w : G} (hw : IsUniqueInvolution N w) :
    z * t * w ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) := by
  by_cases hne : w = z * t
  · rw [hne, zt_sq hs]
    exact Subgroup.one_mem _
  · exfalso
    have hfr := fuzzyFrame_of_third hs hN hNK hNJ hzN htN hw hne
    have hfd := hs.frame
    have hKz : IsClassicalMember p f K z :=
      isClassicalMember_of_twin hs.hyp hfd.mem hfd.hz
    have hΩeq := eq_conjClass_of_setting hs
    subst hΩeq
    exact hno (indepTriple_of_fuzzy (layerGenerationHybrid p)
      (ModelFacts.commutingFundamentalFactsFive_all hs.odd) hs.nonabelian hs.odd hs.five hKz
      hs.hyp hs.below hD ⟨_, hfr⟩)

end Main

end CFSG.ClassicalInvolution.Asc77.S28B
