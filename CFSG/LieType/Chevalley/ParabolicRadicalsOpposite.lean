module

public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {τ : Tag} {k : Type} [Field k]

theorem parabolicLevi_le_normalizer_opposite
    {w₀ : WeylGroup τ} {δ : Fin τ.rank → Fin τ.rank}
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin τ.rank)) :
    parabolicLevi τ k J ≤ Subgroup.normalizer
      (((parabolicRadical τ k (δ '' J)).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) k w₀)⁻¹).toMonoidHom :
          Subgroup (ModGL τ k)) : Set (ModGL τ k)) := fun _ hm =>
  mem_normalizer_map_conj_inv (((parabolicLevi_le_parabolicSubgroup (δ '' J)).trans
    (parabolicSubgroup_le_normalizer_parabolicRadical (δ '' J)))
    (map_conj_parabolicLevi_le hδ J (Subgroup.mem_map_of_mem _ hm)))

theorem adjointGroup_le_parabolicRadical_sup_opposite
    [Finite k] {r : ℕ} [Fact r.Prime] [CharP k r] [IsSimpleGroup (adjointGroup τ k)]
    {w₀ : WeylGroup τ} {δ : Fin τ.rank → Fin τ.rank} (hδinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) :
    adjointGroup τ k ≤ parabolicRadical τ k J ⊔ (parabolicRadical τ k (δ '' J)).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) k w₀)⁻¹).toMonoidHom := by
  have := finite_modGL (τ := τ) (K := k)
  obtain ⟨-, hR, -⟩ := canonical_weyl_root_transport τ k
  have hnC : canonicalRep (coxeterSystem τ) k w₀ ∈ adjointGroup τ k :=
    canonicalRep_mem_adjointGroup _ k w₀
  set n := canonicalRep (coxeterSystem τ) k w₀
  set Q := parabolicRadical τ k J
  set Q' := (parabolicRadical τ k (δ '' J)).map (MulAut.conj n⁻¹).toMonoidHom
  set C := adjointGroup τ k
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := parabolic_root_radical_Levi_factors τ k J
  have hQ1 : Q ≠ ⊥ := (hfin r).2.2 hJ
  have hQC : Q ≤ C := rootSpan_le_adjointGroup k _
  have hQ'C : Q' ≤ C := by
    rintro _ ⟨q, hq, rfl⟩
    exact mul_mem (mul_mem (inv_mem hnC) (rootSpan_le_adjointGroup k _ hq)) (inv_inv n ▸ hnC)
  have hMQ : parabolicLevi τ k J ≤ Subgroup.normalizer (Q : Set (ModGL τ k)) :=
    (parabolicLevi_le_parabolicSubgroup J).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical J)
  have hMQ' : parabolicLevi τ k J ≤ Subgroup.normalizer (Q' : Set (ModGL τ k)) :=
    parabolicLevi_le_normalizer_opposite hδ J
  have hgen : C ≤ Q ⊔ Q' ⊔ parabolicLevi τ k J := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, hg | hg⟩
    · have hg' : g = xUnit τ k i c := Units.ext (hg.trans (coe_xUnit i c).symm)
      rw [hg']
      by_cases hi : i ∈ J
      · exact Subgroup.mem_sup_right (xUnit_mem_parabolicLevi hi c)
      · refine Subgroup.mem_sup_left (Subgroup.mem_sup_left ?_)
        rw [← pinnedX_single]
        exact pinnedX_mem_rootSpan (mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ i,
          by rw [height_single]; exact one_pos, i, hi, by simp⟩) c
    · have hg' : g = yUnit τ k i c := Units.ext (hg.trans (coe_yUnit i c).symm)
      rw [hg']
      by_cases hi : i ∈ J
      · exact Subgroup.mem_sup_right (yUnit_mem_parabolicLevi hi c)
      · refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)
        have hmem : (MulAut.conj n).toMonoidHom (yUnit τ k i c) ∈
            (rootSubgroup τ k (-Pi.single i 1)).map (MulAut.conj n).toMonoidHom :=
          Subgroup.mem_map_of_mem _
            (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨c, pinnedX_neg_single τ k i c⟩)
        rw [hR w₀ _ (isRoot_neg_single τ i), smul_neg, hδ, neg_neg] at hmem
        have hδi : Pi.single (δ i) 1 ∈ parabolicRadicalRoots τ (δ '' J) :=
          mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ (δ i),
            by rw [height_single]; exact one_pos, δ i,
            fun ⟨j, hj, hji⟩ => hi (hδinj hji ▸ hj), by simp⟩
        have hmem' : (MulAut.conj n).toMonoidHom (yUnit τ k i c) ∈
            parabolicRadical τ k (δ '' J) :=
          (le_biSup (rootSubgroup τ k) hδi) hmem
        refine Subgroup.mem_map.2 ⟨_, hmem', ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MulAut.conj_apply]
        group
  have hXC : Q ⊔ Q' ≤ C := sup_le hQC hQ'C
  have hN : C ≤ Subgroup.normalizer ((Q ⊔ Q' : Subgroup (ModGL τ k)) : Set (ModGL τ k)) :=
    hgen.trans (sup_le Subgroup.le_normalizer fun m hm =>
      mem_normalizer_sup_of_mem (hMQ hm) (hMQ' hm))
  have : ((Q ⊔ Q').subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).2 hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q ⊔ Q').subgroupOf C) with h | h
  · exfalso
    apply hQ1
    have hdis := Subgroup.subgroupOf_eq_bot.1 h
    exact eq_bot_iff.2 fun q hq => (Subgroup.disjoint_def.1 hdis)
      (Subgroup.mem_sup_left hq) (hQC hq) ▸ Subgroup.mem_bot.2 rfl
  · exact Subgroup.subgroupOf_eq_top.1 h

end CFSG.LieType.Chevalley
