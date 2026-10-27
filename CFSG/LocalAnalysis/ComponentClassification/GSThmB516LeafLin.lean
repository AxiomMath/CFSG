module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOdd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOrd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRecog

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.CatLeafProof.X10Sp
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open Pump516

namespace Pump516

theorem center_eq_bot_of_nonabelian {S : Type} [Group S] [IsSimpleGroup S]
    (hna : ∃ x y : S, x * y ≠ y * x) : center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
  · exact h
  · obtain ⟨x, y, hxy⟩ := hna
    exact absurd (mem_center_iff.mp (h ▸ mem_top y) x) hxy

theorem eq_of_two_lieModels_psl_two {X : Type} [Group X] {p e e' : ℕ} (hp2 : p ≠ 2)
    (h : Blueprint.LieModel X .PSL 2 p e) (h' : Blueprint.LieModel X .PSL 2 p e') : e = e' := by
  have h1 := (lieOrder_of_lieModel (Or.inl rfl) hp2 (by norm_num) h).2
  have h2 := (lieOrder_of_lieModel (Or.inl rfl) hp2 (by norm_num) h').2
  simp only [lieSylowExponent] at h1 h2
  omega

theorem eq_four_of_l2_model {X : Type} [Group X] {p f n e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {τ' : StatedLieTag} {n' e' : ℕ}
    (hT : (τ', n', e') ∈ linInnerTuples n e ∨ (τ', n', e') ∈ linUInnerTuples n e)
    (hadm' : StatedLieAdmissible τ' n' p e') (hX' : Blueprint.LieModel X τ' n' p e')
    (hX : Blueprint.LieModel X .PSL 2 p (2 * f)) : n = 4 ∧ e = f := by
  have hcase : Even n → (τ', n', e') = (.PSL, n / 2, 2 * e) → n = 4 ∧ e = f := by
    intro hn h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have h2 : 2 ≤ n / 2 := hadm'.2.2.1
    rcases Nat.lt_or_ge (n / 2) 3 with h3 | h3
    · have hn4 : n = 4 := by obtain ⟨m, hm⟩ := hn; omega
      refine ⟨hn4, ?_⟩
      rw [hn4] at hX'
      have := eq_of_two_lieModels_psl_two hp2 hX' hX
      omega
    · exact (false_of_two_lieModels_l2 hp hp2 hf (Or.inl ⟨rfl, h3⟩) hadm' hX' hX).elim
  rcases hT with (⟨k, -, hk3, -, h⟩ | ⟨hn, h⟩) | (⟨k, hk3, -, h⟩ | ⟨hn, h⟩)
  · obtain ⟨rfl, rfl, rfl⟩ : τ' = .PSL ∧ n' = k ∧ e' = e := by
      simp only [Prod.mk.injEq] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    exact (false_of_two_lieModels_l2 hp hp2 hf (Or.inl ⟨rfl, hk3⟩) hadm' hX' hX).elim
  · exact hcase hn h
  · obtain ⟨rfl, rfl, rfl⟩ : τ' = .PSU ∧ n' = k ∧ e' = e := by
      simp only [Prod.mk.injEq] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    exact (false_of_two_lieModels_l2 hp hp2 hf (Or.inr (Or.inl rfl)) hadm' hX' hX).elim
  · exact hcase hn h

end Pump516

theorem cf516LinRow :
    CF516LinRow := by
  intro S _ _ τ n r e hr hr2 hτ hadm hm hs hna _ σ P hP p f hp hp2 hf hPm t _ ht2 J hJC hJ hJm
    _ _ _ _ _ _
  have : IsSimpleGroup S := hs
  have hZ := center_eq_bot_of_nonabelian hna
  have hQ : FixedTwoComponentsQuasisimple S :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna ⟨τ, n, r, e, hr, hr2, hadm, hm⟩
  have hct := orderOf_conj_eq_two hZ ht2
  have hc2 : MulAut.conj t * MulAut.conj t = 1 := by
    rw [← pow_two, ← hct, pow_orderOf_eq_one]
  have hc1 : MulAut.conj t ≠ 1 := fun h => by
    rw [h, orderOf_one] at hct
    omega
  have hJα : J ≤ fixedSubgroup (MulAut.conj t) := by
    rw [fixedSubgroup_conj]
    exact hJC
  have hJα' : IsPComponent 2 (J.subgroupOf (fixedSubgroup (MulAut.conj t))) := by
    rw [fixedSubgroup_conj]
    exact hJ
  have hJs : IsSimpleGroup (J ⧸ pPrimeCore 2 J) :=
    Pump516.isSimpleGroup_of_lieModel_psl (by norm_num) hJm
  obtain ⟨hJc, hJZ, ⟨eJ⟩⟩ := fixed_component_data hQ hc2 hc1 hJα hJα' hJs
  have hJm' := lieModel_center_of_fixed eJ hJm
  have hcases : ComponentCases r (linInnerTuples n e) (J.subgroupOf (fixedSubgroup
      (MulAut.conj t))) ∨ ComponentCases r (linUInnerTuples n e) (J.subgroupOf (fixedSubgroup
      (MulAut.conj t))) := by
    rcases hτ with rfl | rfl
    · exact Or.inl (psl_inner_component_cases hr hr2 hadm hm hct hJc)
    · exact Or.inr (psu_inner_component_cases hr2 hadm hm hct hJc)
  obtain ⟨τ', n', e', hT, hadm', hX'⟩ : ∃ τ' n' e', ((τ', n', e') ∈ linInnerTuples n e ∨
      (τ', n', e') ∈ linUInnerTuples n e) ∧ CentralModel r τ' n' e'
        (J.subgroupOf (fixedSubgroup (MulAut.conj t))) := by
    rcases hcases with (⟨z, hz, hzc, hzz, hz1⟩ | ⟨τ', n', e', hT, hcm⟩) |
        (⟨z, hz, hzc, hzz, hz1⟩ | ⟨τ', n', e', hT, hcm⟩)
    · exact absurd (hJZ z hz hzc hzz) hz1
    · exact ⟨τ', n', e', Or.inl hT, hcm⟩
    · exact absurd (hJZ z hz hzc hzz) hz1
    · exact ⟨τ', n', e', Or.inr hT, hcm⟩
  have hrp : r = p := char_eq_of_psl_two_sq hp hp2 hf hr2 hJm' hX'
  subst hrp
  obtain ⟨rfl, rfl⟩ := eq_four_of_l2_model hp hp2 hf hT hadm' hX' hJm'
  have hS : Blueprint.LieModel S .PSL 4 r e ∨ Blueprint.LieModel S .PSU 4 r e := by
    rcases hτ with rfl | rfl
    · exact Or.inl hm
    · exact Or.inr hm
  exact false_of_card_le_quotient hP.2.2.2 (card_le_of_l4u4 hp hp2 hf hPm hS)

end CFSG.ComponentClassification.GSThmB
