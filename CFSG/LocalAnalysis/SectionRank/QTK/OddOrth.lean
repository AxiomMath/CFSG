module

public import CFSG.LocalAnalysis.SectionRank.QTK.Basic
public import CFSG.RankThree.CentralLift.ClassicalCenterTrivial
import CFSG.RankThree.PartOne.S11c.OrthogonalRank
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly.LowTwoRank QuadraticMap
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LieType.Universal.Spin (quadOdd quadPlus quadMinus)

theorem four_le_localRank_of_statedOmega {S : Type} [Group S] [Finite S] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (Q : QuadraticForm K (ι → K)) {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hd : 7 ≤ Fintype.card ι) (hB : (polarBilin Q).Nondegenerate)
    (e : S ≃* StatedProj (StatedOmega Q₀)) : 4 ≤ localRank p S := by
  obtain ⟨e'⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived hQ
  set ψ : (⊤ : Subgroup S) ≃* CFSG.RankThree.Classical2.ProjOrthDerived Q :=
    Subgroup.topEquiv.trans (e.trans e')
  refine CFSG.RankThree.PartOne.orthogonal_central_cover_four_le_localRank ⊤ hp hp2 hf hK Q ?_ hB
    ψ.toMonoidHom ψ.surjective ?_
  · rw [Module.finrank_fintype_fun_eq_card]
    exact hd
  · intro x hx
    have hx1 : x = 1 := ψ.injective (by rw [map_one]; exact hx)
    rw [hx1]
    exact Subgroup.one_mem _

theorem not_evenRank_le_two_of_omegaOdd {S : Type} [Group S] [Finite S] {n p f : ℕ}
    (hm : StatedClassicalModel S .POmegaOdd n p f) : ¬ CFSG.Open.evenRank S ≤ 2 := by
  obtain ⟨⟨hp, hf, hn, hp2⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : CharP K p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hp hf hK
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  refine not_evenRank_le_two_of_localRank e hp hp2 (le_trans (by norm_num)
    (four_le_localRank_of_statedOmega hp hp2 hf hK (quadOdd n K)
      (CFSG.LieType.Universal.Spin.coe_quadOdd n K) ?_
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd n K h2) (MulEquiv.refl _)))
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  omega

theorem not_evenRank_le_two_of_omegaPlus {S : Type} [Group S] [Finite S] {n p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel S .POmegaPlus n p f) : ¬ CFSG.Open.evenRank S ≤ 2 := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  refine not_evenRank_le_two_of_localRank e hp hp2 (le_trans (by norm_num)
    (four_le_localRank_of_statedOmega hp hp2 hf hK (quadPlus n K)
      (CFSG.LieType.Universal.Spin.coe_quadPlus n K) ?_
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K) (MulEquiv.refl _)))
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem not_evenRank_le_two_of_omegaMinus {S : Type} [Group S] [Finite S] {n p f : ℕ}
    (hp2 : p ≠ 2) (hm : StatedClassicalModel S .POmegaMinus n p f) :
    ¬ CFSG.Open.evenRank S ≤ 2 := by
  obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hm
  refine not_evenRank_le_two_of_localRank e hp hp2 (le_trans (by norm_num)
    (four_le_localRank_of_statedOmega hp hp2 hf hK (quadMinus n K b c)
      (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c) ?_
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
      (MulEquiv.refl _)))
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end CFSG.SectionRank.QTK
