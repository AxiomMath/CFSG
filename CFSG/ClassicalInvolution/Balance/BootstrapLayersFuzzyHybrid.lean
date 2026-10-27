module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyPairFrames
public import CFSG.ClassicalInvolution.Balance.LayerGenerationHybrid

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance.Theorem5 (FuzzyFrameOn MemberClass FuzzyFrameBalance)

section Layers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem layerGenerationLie_sec_hybrid {A : Subgroup G} {S : Set G} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h0 : ModelClauseZero) (hBelow : CITBelowU p f (Nat.card G)) (hs : SecData p f a Φ)
    (T : SecToral Φ a A S) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hF3 : NoComponentOverF3 p f Φ a) (hmodel : LayerGenerationHybrid p) :
    LayerGenerationLie Φ A a := by
  have ha1 : a ≠ 1 := fun h => hnc (by simp [h])
  have hΦ : ∀ K ∈ Φ, K ≤ Subgroup.centralizer ({a} : Set G) →
      IsInvolutionMember (modOdd a K) := fun K hK _ => by
    obtain ⟨z, hz⟩ := hs.member K hK
    exact isInvolutionMember_modOdd_of_isSectionMember hz hq
  unfold LayerGenerationLie LayerGenerationOn
  intro L hL hlie hjoin F₀ hF
  obtain ⟨Dsys⟩ := hs.nonempty_lieSystem hBelow hnc
  obtain ⟨D', hD'Q, -⟩ := hs.lieDecomposition_comp hp2 h0 fundamentalWholeA1 hq Dsys
  have : (memberJoin Φ a).Normal := memberJoin_normal_of_normalizes hs.normalizes
  have hL' : CFSG.Open.IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D'.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · obtain ⟨j, hj⟩ := hD'Q i
    have hQ : D'.Q i = (secComponentHom hs.normalizes Dsys j).range := hj.symm
    have h5 : 5 ≤ p ^ Dsys.exp j :=
      five_le_pow_of_ne_three Fact.out hp2 hq ((Dsys.exp_eq j).imp id And.right) (hF3 Dsys j)
    rcases hmodel (Dsys.tag j) (Dsys.rank j) (Dsys.exp j) (Dsys.isFundTag j)
      (Dsys.admissible j) hp2 h5 with hA | ⟨hG2, hD4, hB⟩
    · obtain ⟨R₁, hR₁, R₂, hR₂, z₁, hz₁, z₂, hz₂, hc₁, hc₂, hc₁₂, hc₂₁, f₁, hf₁, f₂, hf₂, hf₁1,
        hf₂1, hf₁₂, hact₁, hact₂⟩ := T.exists_pair_frame_data hs ha1 Dsys j hQ
        (fun K hK => modOdd_le_or_commutes D' i hK) hF
      rw [hQ] at hF hL ⊢
      obtain ⟨hF₀A, h4, hFn, hfaith⟩ := hF
      have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := fun g hg =>
        T.mem_centralizer (hF₀A hg)
      have hF2 : ∀ g ∈ F₀, g * g = 1 := fun g hg => T.sq (hF₀A hg)
      exact OddCentralizerFree.of_le_layers (hA (OddQuot a)
        (secComponentHom hs.normalizes Dsys j)
        (secComponentHom_ker_le_center hs.normalizes Dsys j) hL R₁ hR₁ R₂ hR₂ z₁ hz₁ z₂ hz₂ hc₁
        hc₂ hc₁₂ hc₂₁ (modOdd a F₀) (by rw [card_modOdd_of_exponent_two hFC hF2, h4])
        (modOdd_sq_eq_one (fun x hx => T.sq hx) hF₀A) hFn hfaith f₁ hf₁ f₂ hf₂ hf₁1 hf₂1 hf₁₂
        hact₁ hact₂)
    · have hsingle : FundamentalSingleClass (Dsys.tag j) (compModel Dsys j).D :=
        ModelFacts.fundamentalSingleClass (Dsys.tag j) (Dsys.rank j) p (Dsys.exp j) Fact.out
          (Dsys.isFundTag j) (Dsys.admissible j) hG2 hD4
      have hperf : ∀ R ∈ fundamentalSubgroups (Dsys.tag j) (compModel Dsys j).D, ⁅R, R⁆ = R :=
        fun R hR => commutator_self_eq_of_le (ModelFacts.fundPerfect_core (Dsys.tag j)
          (Dsys.rank j) p (Dsys.exp j) hp2 (Dsys.isFundTag j) (Dsys.admissible j) (by omega) R hR)
      exact oddCentralizerFree_of_centralizedGenerated_sec (fun x hx => T.sq hx) hΦ hL hlie hF
        (T.centralizedGeneratedAt hs ha1 Dsys j hsingle hperf hB hQ
          (fun K hK => modOdd_le_or_commutes D' i hK) hF)
  · exfalso
    exact not_commutes_self_of_isQuasisimple hL'.2.2 fun x hx y hy => hcomm x hx y (hjoin hy)

theorem componentLayersAt_sec_hybrid {A : Subgroup G} {S : Set G} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hBelow : CITBelowU p f (Nat.card G))
    (hs : SecData p f a Φ) (T : SecToral Φ a A S) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hF3 : NoComponentOverF3 p f Φ a) (hmodel : LayerGenerationHybrid p) :
    ComponentLayersAt Φ A a :=
  componentLayersAt_of_layerGenerationOn (P := fun L => IsOddLieComponent L)
    (fun _ hL => hs.trichotomy hp2 h0 fundamentalWholeA1 hq hBelow hnc hL)
    (layerGenerationLie_sec_hybrid hp2 hq h0 hBelow hs T hnc hF3 hmodel)

end Layers

section Triangle

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {J₁ J₂ J₃ : Subgroup G}
  {z₁ z₂ z₃ : G}

theorem AxisTriangle.rankThreeBalance_hybrid [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hBelow : CITBelowU p f (Nat.card G)) (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃)
    (hne₁₂ : z₁ ≠ z₂) (hne₁₃ : z₁ ≠ z₃) (hne₂₃ : z₂ ≠ z₃) (hind : z₁ * z₂ ≠ z₃)
    (hmodel : LayerGenerationHybrid p)
    (hF3 : ∀ b ∈ triangleAxis z₁ z₂ z₃, b ≠ 1 →
      NoComponentOverF3 p f (triangleSecFamily J₁ J₂ J₃ b) b) :
    RankThreeBalance (triangleAxis z₁ z₂ z₃) := by
  have hcard := hT.card_axis hne₁₂ hne₁₃ hne₂₃ hind
  refine ⟨hT.isElemAbelian, hcard, hT.weakBalanced hnab hp2 hq h0 hA1 hBelow, ?_⟩
  refine twoBalancedWrt_of_secToral (S := {z₁, z₂, z₃}) hT.isElemAbelian fun a ha ha1 => ?_
  have hs := hT.secData ha
  have hnc := not_subset_center_of_ne_one hnab ha1
  obtain ⟨Dsys⟩ := hs.nonempty_lieSystem hBelow hnc
  have hqs : ∀ K ∈ triangleSecFamily J₁ J₂ J₃ a, CFSG.Open.IsQuasisimple ↥(modOdd a K) :=
    fun K hK => hs.isQuasisimple_modOdd Dsys (fun j R hR => by
      have h5 : 5 ≤ p ^ Dsys.exp j := five_le_pow_of_ne_three Fact.out hp2 hq
        ((Dsys.exp_eq j).imp id And.right) (hF3 a ha ha1 Dsys j)
      exact fundQuasisimple_core hp2 (Dsys.isFundTag j) (Dsys.admissible j) (by omega) R hR) hK
  have T := hT.secToral ha hcard hqs
  exact ⟨_, T, componentLayersAt_sec_hybrid hp2 hq h0 hBelow hs T hnc (hF3 a ha ha1) hmodel⟩

theorem rankThreeBalance_of_fuzzyFrameOn_hybrid [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hBelow : CITBelowU p f (Nat.card G)) {Ω : Set (Subgroup G)} {A : Subgroup G}
    (hA : FuzzyFrameOn p f Ω A) (hmodel : LayerGenerationHybrid p)
    (hF3 : ∀ (J₁ J₂ J₃ : Subgroup G) (z₁ z₂ z₃ : G), J₁ ∈ Ω → J₂ ∈ Ω → J₃ ∈ Ω →
      AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃ → triangleAxis z₁ z₂ z₃ = A →
        ∀ b ∈ A, b ≠ 1 → NoComponentOverF3 p f (triangleSecFamily J₁ J₂ J₃ b) b) :
    RankThreeBalance A := by
  obtain ⟨J₁, J₂, J₃, z₁, z₂, z₃, h1, h2, h3, hT, hne12, hne13, hne23, hind, hax⟩ :=
    hA.exists_axisTriangle
  have hB := hT.rankThreeBalance_hybrid hnab hp2 hq ModelFacts.modelClauseZero
    fundamentalWholeA1 hBelow hne12 hne13 hne23 hind hmodel fun b hb hb1 =>
      hF3 J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT hax b (hax ▸ hb) hb1
  rwa [hax] at hB

theorem fuzzyFrameBalance_of_hybrid {𝒞 : MemberClass} (hmodel : LayerGenerationHybrid p)
    (hF3 : FuzzyNoF3 p f 𝒞) : FuzzyFrameBalance p f 𝒞 := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind A hA
  exact rankThreeBalance_of_fuzzyFrameOn_hybrid hnab hp2 hq hBelow hA hmodel
    fun J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT hax b hb hb1 =>
      hF3 G hnab hp2 hq K z hz hBelow hconn hind J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT b (hax ▸ hb) hb1

end Triangle

end CFSG.ClassicalInvolution.Balance.Bootstrap
