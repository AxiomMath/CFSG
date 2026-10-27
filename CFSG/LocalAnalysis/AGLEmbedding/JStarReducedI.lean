module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

namespace JStarHyp

variable {Y : Type} [Group Y] [Finite Y] {p n : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
  {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* PSL2GF p n}

theorem inf_isElemAbelian (h : JStarHyp p n Rb Y₀ Jt Xt φ) :
    IsElemAbelian p ((Rb : Subgroup Y) ⊓ Jt) ∧
      Nat.card ((Rb : Subgroup Y) ⊓ Jt : Subgroup Y) = p ^ n := by
  have hS : CFSG.ABGLocalTools.IsSylowOf p (Rb : Subgroup Y)
      (Subgroup.normalizer (Jt : Set Y)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨h.le_normalizer, Rb.isPGroup', fun hdvd => Rb.not_dvd_index
      (hdvd.trans (Subgroup.relIndex_dvd_index_of_le h.le_normalizer))⟩
  obtain ⟨Q, hQ⟩ := hS.inf_of_le_normalizer Subgroup.le_normalizer le_rfl
  obtain ⟨hQel, hQcard⟩ := h.sylow_isElemAbelian Q
  rw [← hQ]
  exact ⟨elementary_abelian_map p hQel _,
    by rw [Subgroup.card_map_of_injective Jt.subtype_injective, hQcard]⟩

theorem eq_one_of_inf_centralizer_le_ker (h : JStarHyp p n Rb Y₀ Jt Xt φ) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤)
    (hker : Jt ⊓ Subgroup.centralizer (K : Set Y) ≤ φ.ker.map Jt.subtype) {z : Y}
    (hzR : z ∈ (Rb : Subgroup Y)) (hzC : z ∈ Subgroup.centralizer (K : Set Y)) : z = 1 := by
  have hNC : Subgroup.normalizer (K : Set Y) ≤
      Subgroup.normalizer (Subgroup.centralizer (K : Set Y) : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      inferInstance
  refine h.faithful z hzR fun j hj => hker ⟨?_, ?_⟩
  · exact Jt.mul_mem ((Subgroup.mem_normalizer_iff.mp (h.le_normalizer hzR) j).mp hj)
      (Jt.inv_mem hj)
  · have hjz : j * z⁻¹ * j⁻¹ ∈ Subgroup.centralizer (K : Set Y) :=
      (Subgroup.mem_normalizer_iff.mp (hNC (h.le_normalizer_component hK hj)) z⁻¹).mp
        (Subgroup.inv_mem _ hzC)
    have heq : z * j * z⁻¹ * j⁻¹ = z * (j * z⁻¹ * j⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ hzC hjz

theorem false_of_mem_centralizer (h : JStarHyp p n Rb Y₀ Jt Xt φ) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) (hKY₀ : ¬ K ≤ Y₀) {z : Y} (hzR : z ∈ (Rb : Subgroup Y))
    (hzp : orderOf z = p) (hzC : z ∈ Subgroup.centralizer (K : Set Y)) : False := by
  have hp : p.Prime := Fact.out
  rcases h.le_centralizer_or_inf_le_ker hK with hJC | hker
  · obtain ⟨hEel, hEcard⟩ := h.inf_isElemAbelian
    have h1 := h.red.pRank_inf_centralizer_le_one_of_not_le hK hKY₀
    have h2 : n ≤ Open.pRank p ((Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y)) :=
      le_csSup (pRank_bddAbove p hp _) ⟨_, inf_le_inf_left _ hJC, hEel, hEcard⟩
    have := h.three_le
    omega
  · have hz1 := h.eq_one_of_inf_centralizer_le_ker hK hker hzR hzC
    rw [hz1, orderOf_one] at hzp
    exact hp.one_lt.ne hzp

end JStarHyp

theorem jStarI : StmtJStarI := fun h _ hK _ hKY₀ _ hzR _ hzp hzC =>
  h.false_of_mem_centralizer hK hKY₀ hzR hzp hzC

end CFSG.AGLEmbedding
