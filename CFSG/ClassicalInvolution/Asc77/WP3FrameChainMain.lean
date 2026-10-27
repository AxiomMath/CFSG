module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieE
public import CFSG.ClassicalInvolution.Asc77.WP3FrameStarE
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

section Inputs

variable (p f : ℕ) [Fact p.Prime]

@[expose] def HypOmegaModAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → HypOmegaMod p f (CoreAssembly.conjClass K)

@[expose] def AEmptyAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → ∀ M ∈ CoreAssembly.conjClass K,
        AEmpty (CoreAssembly.conjClass K) M

@[expose] def NoTwinsAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → ∀ M ∈ CoreAssembly.conjClass K,
        ∀ M' ∈ twinSet (CoreAssembly.conjClass K) M, M' = M

abbrev ChainShapePred : ShapePred :=
  fun _ _ _ K z => ChainShape p f (CoreAssembly.conjClass K) z

@[expose] def ChainFrameGenT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K J K' : Subgroup G) (z t z' : G), ChainFrameSetting p f Ω K J K' z t z' →
      CentralizerGenerationStar Ω (Subgroup.closure ({z, t, z'} : Set G)) t

@[expose] def ChainFrameNine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K J K' : Subgroup G) (z t z' : G), ChainFrameSetting p f Ω K J K' z t z' →
      p ^ f = 9 → LocalLeviComponent p f Ω z

end Inputs

section Frames

variable {p f : ℕ} [Fact p.Prime]

theorem chainFrame_exists_on (hΩ : HypOmegaModAll p f) (hA : AEmptyAll p f)
    (hT : NoTwinsAll p f) (hGen : ChainFrameGenT p f)
    (hNine : ChainFrameNine p f) (h51t : ChainFrameHyp51t p f) (h51zt : ChainFrameHyp51zt p f) :
    FrameExistsOnE p f (ChainShapePred (p := p) (f := f)) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow _ hshape
  have hΩmod : HypOmegaMod p f (CoreAssembly.conjClass K) := hΩ G hnab hp2 hq K z hz hBelow
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := hshape
  have hpairD : ChainPair (fundamentalSubgroups (D.tag i₁) (compModel D i₁).D) :=
    chainPair_model hp2 (D.tag i₁) (D.rank i₁) (D.exp i₁) ht₁ (by omega) (D.admissible i₁)
  let C : ChainCtx p f (CoreAssembly.conjClass K) z :=
    { K := K, hK := CoreAssembly.mem_conjClass_self K, hKz := hKz, hΩ := hΩmod, hp := hp2,
      hq := hq, D := D, card_eq := hcard, i₀ := i₀, i₁ := i₁, ne := hne, tag₁ := ht₁,
      tag₀ := ht₀, rank₀ := hr₀, pair := hpairD }
  obtain ⟨L⟩ := C.exists_lift
  have htrans : ∀ M ∈ CoreAssembly.conjClass K, ∃ g : G, conjSub g K = M := fun M hM => hM
  have hset : ChainFrameSetting p f (CoreAssembly.conjClass K) K L.J L.K' z L.t L.z' :=
    { odd := hp2
      five := hq
      hyp := hΩmod
      aEmpty := hA G hnab hp2 hq K z hz hBelow
      noTwins := hT G hnab hp2 hq K z hz hBelow
      trans := htrans
      below := hBelow
      shape := ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩
      frame := L.frameData
      symm := L.symm
      toral := L.toral }
  have hKJ : ∀ a : G, IsClassicalMember p f K a → a = z := fun a ha =>
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq ha).eq hKz
  have hJt : ∀ a : G, IsClassicalMember p f L.J a → a = L.t := fun a ha =>
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq ha).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq L.hJt)
  have hframe : FrameSideTwoStar p f (CoreAssembly.conjClass K)
      (Subgroup.closure ({z, L.t, L.z'} : Set G)) ({K, L.J} : Set (Subgroup G)) :=
    { elem := L.frameData.isElemAbelian hp2 hΩmod
      card := (L.frameData.natCard_eight hp2 hq hΩmod).ge
      subset := by
        rintro M (rfl | rfl)
        · exact CoreAssembly.mem_conjClass_self _
        · exact L.hJ.1
      nonempty := ⟨K, Set.mem_insert _ _⟩
      involution := by
        rintro M (rfl | rfl)
        · exact ⟨z, L.z_mem_B, hz⟩
        · exact ⟨L.t, L.t_mem_B, L.hJt⟩
      generation := by
        rintro a - ⟨M, (rfl | rfl), hMa⟩
        · rw [hKJ a hMa]
          exact L.generation_z
        · rw [hJt a hMa]
          exact hGen G (CoreAssembly.conjClass K) K L.J L.K' z L.t L.z' hset
      link := by
        rintro a - ⟨M, (rfl | rfl), hMa⟩
        · rw [hKJ a hMa]
          exact L.link_z_star
        · rw [hJt a hMa]
          exact L.link_t_star htrans }
  refine ⟨K, z, Subgroup.closure ({z, L.t, L.z'} : Set G), {K, L.J}, z, ?_, ?_⟩
  · exact
      { mem := CoreAssembly.mem_conjClass_self K
        cls := hz
        z₀A := L.z_mem_B
        tq := L.frameData.tq_B hp2 hq hΩmod
        frame := hframe
        aA := L.z_mem_B
        a1 := hKz.ne_one
        aClassical := ⟨K, CoreAssembly.mem_conjClass_self K, hz⟩
        cover := fun M hM _ => L.cover_z htrans hM
        nine := fun h9 => ⟨z, L.z_mem_B, hKz.ne_one, fun M hM => L.cover_z htrans hM,
          hNine G (CoreAssembly.conjClass K) K L.J L.K' z L.t L.z' hset h9⟩ }
  · exact chainFrameHyp51_of_vertices' p f h51t h51zt G (CoreAssembly.conjClass K) K L.J L.K' z
      L.t L.z' hset

end Frames

end CFSG.ClassicalInvolution.Asc77
