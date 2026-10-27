module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.SplitFrame
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Main
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignTori

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

section SplitE8

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false

theorem e8SplitFrame (K : Type) [Field K] [Finite K] (hK : 5 ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, orderOf ζ = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdvd : 5 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hK
  exact exists_prime_orderOf_dvd_card' 5 hdvd

section Def


@[expose] def zSplitE8 (K : Type) [Field K] (ζ : Kˣ) : adjointGroup Tag.E8 K :=
  ⟨rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) ζ),
    CFSG.SeitzReduction.E8Pilot.rootDiagUnit_mem_adjointGroup_E8 _⟩

end Def


theorem e8SplitFrame_of (K : Type) [Field K] [Finite K] (hK : 5 ∣ Nat.card K - 1) (ζ : Kˣ)
    (hζ : orderOf ζ = 5) :
    zSplitE8 K ζ ≠ 1 ∧ zSplitE8 K ζ ^ 5 = 1 ∧
      ∃ X : Subgroup (adjointGroup Tag.E8 K), ClosingFrameAt (zSplitE8 K ζ) X := by
  have hK4 : 4 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  set a : Fin Tag.E8.rank → Kˣ := Pi.mulSingle (4 : Fin Tag.E8.rank) ζ with ha
  have hchar : ∀ α : Fin Tag.E8.rank → ℤ, rootChar a α = ζ ^ (α 4) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single (4 : Fin Tag.E8.rank)]
    · simp [ha]
    · intro j _ hj
      simp [ha, Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hS : ∀ α ∈ cosetRoots Tag.E8 4 5, IsRoot Tag.E8 α ∧ rootChar a α = 1 := by
    intro α hα
    refine ⟨hα.1, ?_⟩
    rw [hchar, ← orderOf_dvd_iff_zpow_eq_one, hζ]
    exact_mod_cast hα.2
  have hXS : XS K ≤ adjointGroup Tag.E8 K := rootSpan_le_adjointGroup K _
  have h5 : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  refine ⟨?_, ?_, frameIn (XS K), ?_⟩
  · intro h
    have h1 : rootDiagUnit Tag.E8 a = 1 := congrArg Subtype.val h
    have h2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective
      (h1.trans (rootDiagUnit_one (τ := Tag.E8) (K := K)).symm)
    have h3 := congrFun h2 4
    simp [ha] at h3
    rw [h3] at hζ
    simp at hζ
  · apply Subtype.ext
    change (rootDiagUnitHom Tag.E8 K a) ^ 5 = 1
    rw [← map_pow]
    have : a ^ 5 = 1 := by
      funext i
      by_cases hi : i = 4
      · subst hi
        simp [ha, h5]
      · simp [ha, Pi.mulSingle_eq_of_ne hi]
    rw [this, map_one]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hy' : (y : ModGL .E8 K) ∈ XS K := hy
      have := Subgroup.mem_centralizer_singleton_iff.1
        (rootSpan_le_centralizer_rootDiagUnit (K := K) a hS hy')
      exact this
    · refine nonsolvable_frameIn hXS ?_
      intro hs
      haveI := hs
      haveI h2 : Group.IsSolvable ↥(X2 K) :=
        solvable_of_solvable_injective (Subgroup.inclusion_injective (X2_le_XS K))
      obtain ⟨hperf, -, a₀, b₀, hab⟩ := X2_quasisimple K
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a₀
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b₀
      haveI : Nontrivial ↥(X2 K) := ⟨⟨x, 1, fun h => hab (by rw [h]; simp)⟩⟩
      exact (IsSolvable.commutator_lt_top_of_nontrivial (↥(X2 K))).ne hperf.commutator_eq_top
    · exact closing_of_twFrameClosing hXS
        ((frameClosing_iff Tag.E8 K _).1
          (frameClosing_of_detection_E8 K (frameDetection_E8 K)))
    · exact normalizerSolvable_of_twFrame hXS
        ((frameNormalizerSolvable_iff Tag.E8 K _).1 (frameNormalizerSolvable_E8 K hK4))

end SplitE8

end CFSG.LieType.SeitzGeneration.ExcHigh
