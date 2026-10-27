module

public import CFSG.ClassicalInvolution.Asc77.WP3S28BEdge
public import CFSG.ClassicalInvolution.SmallCases.DSplitBoot


public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28B

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.Q27 CFSG.ClassicalInvolution.Disconnected

section Boot

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem fuzzy_alphaDelta_bot (hmodel : LayerGenerationHybrid p)
    (hMFC : ModelFacts.CommutingFundamentalFactsFive p) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hD : DConnected (CoreAssembly.conjClass K))
    (hfz : ∃ A₀ : Subgroup G, Theorem5.FuzzyFrameOn p f (CoreAssembly.conjClass K) A₀) :
    ∀ A : Subgroup G, Theorem5.FuzzyFrameOn p f (CoreAssembly.conjClass K) A →
      ∀ F ∈ signalizerFunctorEk 2 2 A, alphaCore F = ⊥ ∧ deltaCore F = ⊥ := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hinv : ConjInvariant (CoreAssembly.conjClass K) := hΩ.conjInvariant
  have hmap : ∀ A ∈ Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K), ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ∈ Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K) :=
    fun A hA g => Theorem5.FuzzyFrameOn.map hinv hA g
  have hchain := tqChain_of_dConnected hp2 hq hz hD
  have hedge : ∀ M ∈ CoreAssembly.conjClass K, ∀ N ∈ CoreAssembly.conjClass K, ∀ zM zN : G,
      IsClassicalMember p f M zM → IsClassicalMember p f N zN → tqAdjSymm p f M N → zM ≠ zN →
      Theorem5.FrameAdj (Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K))
        (Theorem5.fuzzyVertices p f (CoreAssembly.conjClass K)) zM zN := by
    intro M hM N hN zM zN hMc hNc hE hne
    rcases hE with ⟨a, ha, hNa⟩ | ⟨a, ha, hMa⟩
    · have : a = zM := hMc.eq_of_isCentralInvolution hp2 hf ha.isCentralInvolution
      subst this
      exact frameAdj_of_fuzzy hnab hp2 hq hz hBelow hfz hM hN hMc hNc hNa hne
    · have : a = zN := hNc.eq_of_isCentralInvolution hp2 hf ha.isCentralInvolution
      subst this
      obtain ⟨B, hB, h1, h2⟩ := frameAdj_of_fuzzy hnab hp2 hq hz hBelow hfz hN hM hNc
        hMc hMa hne.symm
      exact ⟨B, hB, h2, h1⟩
  have hcon := Theorem5.shareFour_connected_of_vertexGraph_modOdd
    (𝒯 := Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K)) hmap
    (fun A hA => by
      obtain ⟨J, z, -, -, hel, hcard, -⟩ := hA
      exact ⟨hel, hcard⟩)
    (Theorem5.fuzzyVertices p f (CoreAssembly.conjClass K)) (fun A _ z hz => hz.1)
    (fun A hA => hA.exists_vertex)
    (fun A _ A' _ a ha a' ha' => by
      obtain ⟨-, J, hJ, hJa, -⟩ := ha
      obtain ⟨-, J', hJ', hJ'a, -⟩ := ha'
      exact Theorem5.reflTransGen_frameAdj_of_adj hp2 hf (fun M N => tqAdjSymm p f M N)
        hΩ.classical hchain (Theorem5.fuzzyVertices p f (CoreAssembly.conjClass K)) hedge hJ hJ'
        hJa hJ'a)
    (fun a A hA A' hA' ha ha' =>
      linkMove_connected_noConn hMFC hnab hp2 hq hz hBelow a hA hA' ha ha')
  have hbal : ∀ A ∈ Theorem5.fuzzyFrames p f (CoreAssembly.conjClass K), RankThreeBalance A :=
    fun A hA => rankThreeBalance_of_fuzzyFrameOn_hybrid_free hnab hp2 hq hBelow hA hmodel
  have hO := componentClassificationOddCore_eq_bot_of_simple hnab
  have hα := Theorem5.alphaCore_eq_bot_of_connected_frames hO hmap hbal hcon
  have hΔ := Theorem5.deltaCore_eq_bot_of_connected_frames hO hmap hbal hcon
  exact fun A hA F hF => ⟨hα A hA F hF, hΔ A hA F hF⟩

end Boot

end CFSG.ClassicalInvolution.Asc77.S28B
