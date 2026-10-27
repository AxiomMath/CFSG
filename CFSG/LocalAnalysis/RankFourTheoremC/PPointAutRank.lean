module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSignalizer
import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem pRank_le_one_of_isCyclic {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {S : Subgroup X} (hS : IsCyclic S) : Open.pRank p S ≤ 1 :=
  CFSG.SectionRank.pRank_le_one_of_isCyclic hp hS

theorem pRank_le_one_add_pRank_mulAut {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {K : Subgroup X} [K.Normal] (hDc : IsCyclic (centralizer (K : Set X))) (R : Subgroup X) :
    Open.pRank p R ≤ 1 + Open.pRank p (⊤ : Subgroup (MulAut K)) := by
  obtain ⟨E, hER, hE, hcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp R
  have h := CFSG.PreuniquenessRankFour.Helpers.elementary_rank_le_kernel_rank_add_image_rank p hp
    (MulAut.conjNormal : X →* MulAut K) hE _ hcard
  have hker : (MulAut.conjNormal : X →* MulAut K).ker = centralizer (K : Set X) := by
    ext g
    exact mem_ker_conjNormal
  rw [hker] at h
  have h1 : Open.pRank p (centralizer (K : Set X)) ≤ 1 := pRank_le_one_of_isCyclic hp hDc
  have h2 : Open.pRank p (E.map (MulAut.conjNormal : X →* MulAut K)) ≤
      Open.pRank p (⊤ : Subgroup (MulAut K)) :=
    CFSG.SectionRank.pRank_mono hp.one_lt le_top
  omega

theorem conj_injective_of_center_eq_bot {K : Type*} [Group K] (hZ : center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  intro g g' h
  have hc : g'⁻¹ * g ∈ center K := mem_center_iff.2 fun x => by
    have hx := congrArg (fun φ : MulAut K => φ x) h
    simp only [MulAut.conj_apply] at hx
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
      _ = g'⁻¹ * g * x := by group
  rw [hZ, mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem pRank_mulAut_le_add_pRank_outer {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hZ : center K = ⊥) :
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤
      Open.pRank p (⊤ : Subgroup K) + Open.pRank p (⊤ : Subgroup (Outer K)) := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp
    (⊤ : Subgroup (MulAut K))
  have h := CFSG.PreuniquenessRankFour.Helpers.elementary_rank_le_kernel_rank_add_image_rank p hp
    (QuotientGroup.mk' (inner K)) hE _ hcard
  rw [QuotientGroup.ker_mk'] at h
  have h1 : Open.pRank p (inner K) ≤ Open.pRank p (⊤ : Subgroup K) := by
    have e1 : inner K = (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) :=
      MonoidHom.range_eq_map _
    rw [e1, CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp _
      (conj_injective_of_center_eq_bot hZ)]
  have h2 : Open.pRank p (E.map (QuotientGroup.mk' (inner K))) ≤
      Open.pRank p (⊤ : Subgroup (Outer K)) :=
    CFSG.SectionRank.pRank_mono hp.one_lt le_top
  omega

end CFSG.LocalAnalysis.RankFourTheoremC
