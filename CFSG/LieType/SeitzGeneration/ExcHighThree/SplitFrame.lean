module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.FrameTransport
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.RootClosureF4Sound
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Main
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Normalizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree


section SplitF4

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem rootSpan_le_centralizer_rootDiagUnit {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α ∧ rootChar a α = 1) :
    rootSpan τ K S ≤ Subgroup.centralizer ({rootDiagUnit τ a} : Set (ModGL τ K)) := by
  refine iSup₂_le fun α hα => ?_
  rw [rootSubgroup]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have h := rootDiagUnit_conj_pinnedX (K := K) a (hS α hα).1 c
  rw [(hS α hα).2, Units.val_one, one_mul] at h
  exact ((mul_inv_eq_iff_eq_mul.1 h).symm)

theorem f4SplitFrame_of (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1) (ω : Kˣ)
    (hω : orderOf ω = 3) :
    zSplit K ω ≠ 1 ∧ zSplit K ω ^ 3 = 1 ∧
      ∃ X : Subgroup (adjointGroup .F4 K), ClosingFrameAt (zSplit K ω) X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK4 : 4 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  set a : Fin Tag.F4.rank → Kˣ := Pi.mulSingle (1 : Fin Tag.F4.rank) ω with ha
  have hchar : ∀ α : Fin Tag.F4.rank → ℤ, rootChar a α = ω ^ (α 1) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single (1 : Fin Tag.F4.rank)]
    · simp [ha]
    · intro j _ hj
      simp [ha, Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hS : ∀ α ∈ cosetRoots Tag.F4 1 3, IsRoot Tag.F4 α ∧ rootChar a α = 1 := by
    intro α hα
    refine ⟨hα.1, ?_⟩
    rw [hchar, ← orderOf_dvd_iff_zpow_eq_one, hω]
    exact_mod_cast hα.2
  have hXS : XS K ≤ adjointGroup .F4 K := rootSpan_le_adjointGroup K _
  have h3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  refine ⟨?_, ?_, frameIn (XS K), ?_⟩
  · intro h
    have h1 : rootDiagUnit .F4 a = 1 := congrArg Subtype.val h
    have h2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective
      (h1.trans (rootDiagUnit_one (τ := Tag.F4) (K := K)).symm)
    have h3 := congrFun h2 1
    simp [ha] at h3
    rw [h3] at hω
    simp at hω
  · apply Subtype.ext
    change (rootDiagUnitHom Tag.F4 K a) ^ 3 = 1
    rw [← map_pow]
    have : a ^ 3 = 1 := by
      funext i
      by_cases hi : i = 1
      · subst hi
        simp [ha, h3]
      · simp [ha, Pi.mulSingle_eq_of_ne hi]
    rw [this, map_one]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hy' : (y : ModGL .F4 K) ∈ XS K := hy
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
        ((frameClosing_iff Tag.F4 K _).1
          (frameClosing_of_detection_F4 K (by omega) (DetectF4.frameDetection_F4 K (by omega))))
    · exact normalizerSolvable_of_twFrame hXS
        ((frameNormalizerSolvable_iff Tag.F4 K _).1 (frameNormalizerSolvable_F4 K hK4))

theorem f4SplitFrame (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1) :
    ∃ z : adjointGroup .F4 K, z ≠ 1 ∧ z ^ 3 = 1 ∧
      ∃ X : Subgroup (adjointGroup .F4 K), ClosingFrameAt z X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    have : 1 ≤ Nat.card K := Nat.card_pos
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  exact ⟨zSplit K ω, f4SplitFrame_of K hK ω hω⟩

end SplitF4

end CFSG.LieType.SeitzGeneration.ExcHighThree
