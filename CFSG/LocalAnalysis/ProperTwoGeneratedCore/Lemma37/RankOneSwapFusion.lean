module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOne
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneSwapInvolution
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionCommutatorFusion

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) {s : EscapingQuotient z}
  (hsS : s ∈ escapingSylowImage S z)
  (hs : s ∉ Subgroup.normalizer (J : Set (EscapingQuotient z)))
include h hsS hs

theorem false_of_swap :
    False := by
  have hz := h.square.central
  have hbar : ∀ u : (S : Subgroup G), sylowBar hz u ∈ escapingSylowImage S z := fun u => by
    rw [← sylowBar_range hz]
    exact ⟨u, rfl⟩
  have hsq1 : ∀ u : (S : Subgroup G), (u : G) * u = 1 → sylowBar hz u * sylowBar hz u = 1 :=
    fun u hu => by
      rw [← map_mul, ← map_one (sylowBar hz)]
      exact congrArg _ (Subtype.ext hu)
  refine false_of_involution_commutators h.square.core.simple h.square.core.nonabelian hz ?_ ?_
  · intro x hx y hy hx2 hy2
    rcases h.sq_mul_eq_of_mul_self_eq_one hsS hs (hbar ⟨x, hx⟩) (hbar ⟨y, hy⟩)
      (hsq1 ⟨x, hx⟩ hx2) (hsq1 ⟨y, hy⟩ hy2) with h1 | h1
    · left
      rw [← map_mul, ← map_pow, ← map_one (sylowBar hz)] at h1
      have h2 := congrArg Subtype.val (sylowBar_injective hz h1)
      simpa using h2
    · right
      rw [← map_mul, ← map_pow, sylowBar_eq_bar_iff] at h1
      simpa using h1
  · intro t ht ht2 htz
    have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have ht2' : sylowBar hz ⟨t, ht⟩ * sylowBar hz ⟨t, ht⟩ = 1 := hsq1 ⟨t, ht⟩ htt
    have ht1 : sylowBar hz ⟨t, ht⟩ ≠ 1 := fun h1 => by
      have h2 := orderOf_sylowBar hz ⟨t, ht⟩
      rw [h1, orderOf_one] at h2
      rw [← h2] at ht2
      exact absurd ht2 (by decide)
    have htz' : sylowBar hz ⟨t, ht⟩ ≠ escapingBar z := fun h1 =>
      htz ((sylowBar_eq_bar_iff hz _).mp h1)
    obtain ⟨i₁, hi₁S, i₂, hi₂S, hi₁, hi₂, hc₁, hc₂, h12⟩ :=
      h.exists_involution_pair hsS hs (hbar ⟨t, ht⟩) ht2' ht1 htz'
    obtain ⟨a, rfl⟩ := exists_sylowBar_eq hz hi₁S
    obtain ⟨b, rfl⟩ := exists_sylowBar_eq hz hi₂S
    refine ⟨a, a.2, b, b.2, mul_self_eq_one_of_sylowBar hz hi₁,
      mul_self_eq_one_of_sylowBar hz hi₂, commute_of_sylowBar hz hc₁.eq,
      commute_of_sylowBar hz hc₂.eq, ?_⟩
    rw [← map_mul, ← map_pow, sylowBar_eq_bar_iff] at h12
    simpa using h12

end RankOneSetting

theorem squareCaseRankOneSwapOuterImpossible :
    SquareCaseRankOneSwapOuterImpossible := by
  intro G _ _ S H z hsq J hJ hJH hJinv s hsS hs _ _ _ _
  exact RankOneSetting.false_of_swap ⟨hsq, hJ, hJH, hJinv⟩ hsS hs

theorem squareCaseRankOneImpossible :
    SquareCaseRankOneImpossible :=
  squareCaseRankOneImpossible_of_swapOuter squareCaseRankOneSwapOuterImpossible

end CFSG.ProperTwoGeneratedCore.Lemma37
