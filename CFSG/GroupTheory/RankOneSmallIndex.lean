module

public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient

public section

namespace CFSG

theorem one_lt_pRank_of_small_index_of_elemAbelian_quotient
    {P E : Type*} [Group P] [Finite P] [Group E] [Finite E]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : CFSG.Open.IsElemAbelian p (⊤ : Subgroup E))
    (f : P →* E) (hf : Function.Surjective f)
    (hcard : p ^ 3 ≤ Nat.card E)
    (S : Subgroup P) (hindex : S.index < p ^ 2) :
    1 < CFSG.Open.pRank p S := by
  by_contra h
  have hSrank : CFSG.pRank p S ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact Nat.le_of_not_gt h
  let D : Subgroup E := S.map f
  let g : S →* D :=
    (f.comp S.subtype).codRestrict D fun x => Subgroup.mem_map_of_mem f x.2
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hDrank : CFSG.pRank p D ≤ 1 :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective
      hp hp2 hSrank g hg
  have hDpg : IsPGroup p D := fun x => ⟨1, Subtype.ext (by
    simpa using hE.2 (x : E) (Subgroup.mem_top _))⟩
  have hDcyc : IsCyclic D :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one
      hp hp2 hDpg hDrank
  have hDcard : Nat.card D ≤ p := by
    obtain ⟨x, hx⟩ := hDcyc.exists_generator
    have hord : orderOf x = Nat.card D := orderOf_eq_card_of_forall_mem_zpowers hx
    have hxp : x ^ p = 1 := Subtype.ext (by
      simpa using hE.2 (x : E) (Subgroup.mem_top _))
    have hdvd : Nat.card D ∣ p := hord ▸ orderOf_dvd_of_pow_eq_one hxp
    exact Nat.le_of_dvd hp.pos hdvd
  have hDindex : D.index ≤ S.index := by
    refine Nat.le_of_dvd (Nat.pos_of_ne_zero ?_) (Subgroup.index_map_dvd S hf)
    exact Subgroup.FiniteIndex.index_ne_zero (self := Subgroup.finiteIndex_of_finite)
  have hlt : Nat.card E < p ^ 3 := by
    rw [← Subgroup.index_mul_card D]
    calc
      D.index * Nat.card D ≤ S.index * p := Nat.mul_le_mul hDindex hDcard
      _ < p ^ 2 * p := Nat.mul_lt_mul_of_pos_right hindex hp.pos
      _ = p ^ 3 := by ring
  omega

end CFSG

end
