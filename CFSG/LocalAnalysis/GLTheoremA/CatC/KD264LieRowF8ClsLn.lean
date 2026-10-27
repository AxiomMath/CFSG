module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8LnModel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpStruct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Final

theorem linear_rank_bounds {N : ℕ} (hN : 3 ≤ N) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    (A : Subgroup (MulAut (projectiveSL N K))) (hA : IsElemAbelian 3 A)
    (h3 : 3 ≤ CFSG.Open.pRank 3 A) (h4 : CFSG.Open.pRank 3 A ≤ 4)
    (hout : ∀ a ∈ A, a ∉ (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)).range →
      ∀ E : Subgroup (projectiveSL N K), E ≤ fixSubgroup a → IsElemAbelian 3 E →
        CFSG.Open.pRank 3 E + 1 ≤ CFSG.Open.pRank 3 A)
    (hnot : ¬ A ≤ innAutDerived (projectiveSL N K)) : 4 ≤ N ∧ N ≤ 7 := by
  classical
  haveI := finite_mulAut' (P := projectiveSL N K)
  obtain ⟨b, hbA, hbout⟩ := SetLike.not_le_iff_exists.1 hnot
  have hb3 : b ^ 3 = 1 := hA.2 b hbA
  obtain ⟨ι, hιinj, hιfix, hιnorm, hι3⟩ := exists_descent hN hK b hb3 hbout
  have hZ := center_projectiveSL_eq_bot (K := K) hN
  have hconjinj := conj_injective' hZ
  have hbnotinn : b ∉ (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)).range :=
    fun h => hbout (inner_le_innAutDerived _ h)
  obtain ⟨E0, hE0, hE0card⟩ := exists_elemAb_card (Fin N → ZMod 2) N (Module.finrank_fin_fun _)
  have hbound : N / 2 + 1 ≤ CFSG.Open.pRank 3 A := by
    have hE0ab : IsElemAbelian 3 (E0.map ι) := isElemAbelian_map_gen ι hE0
    have hc : Nat.card (E0.map ι) = 3 ^ (N / 2) := by
      rw [Subgroup.card_map_of_injective hιinj, hE0card]
    have h1 := hout b hbA hbnotinn (E0.map ι) (by
      rintro _ ⟨v, -, rfl⟩
      exact mem_fixSubgroup.2 (hιfix v)) hE0ab
    rwa [pRank_eq_of_card' Nat.prime_three hE0ab hc] at h1
  refine ⟨?_, by omega⟩
  by_contra hN4
  have hN3 : N = 3 := by omega
  have hAcard := card_eq_pow_pRank hA
  have hout3 := outCycAt_projectiveSL (K := K) hN Nat.prime_three (by norm_num) A hA
  have hA0inn : A ⊓ innAutDerived (projectiveSL N K) ≤
      (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)).range :=
    fun a ha => mem_inner_of_pow_three hN hK ha.2 (hA.2 a ha.1)
  let Ebar : Subgroup (projectiveSL N K) :=
    A.comap (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K))
  have hEbar_map : Ebar.map (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)) =
      (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)).range ⊓ A :=
    Subgroup.map_comap_eq _ _
  have hA0le : A ⊓ innAutDerived (projectiveSL N K) ≤
      Ebar.map (MulAut.conj : projectiveSL N K →* MulAut (projectiveSL N K)) := by
    rw [hEbar_map]
    exact le_inf hA0inn inf_le_left
  have hcardEbar : 9 ≤ Nat.card Ebar := by
    have h1 := Subgroup.card_le_of_le hA0le
    rw [Subgroup.card_map_of_injective hconjinj] at h1
    have h2 : 3 ^ 3 ≤ Nat.card A := by
      rw [hAcard]
      exact Nat.pow_le_pow_right (by norm_num) h3
    have h3' : 9 * 3 ≤ 3 * Nat.card Ebar := by
      calc 9 * 3 = 3 ^ 3 := by norm_num
        _ ≤ Nat.card A := h2
        _ ≤ 3 * Nat.card ↥(A ⊓ innAutDerived (projectiveSL N K)) := hout3
        _ ≤ 3 * Nat.card Ebar := Nat.mul_le_mul_left _ h1
    omega
  have hEbar_ab : IsElemAbelian 3 Ebar := by
    refine isElemAbelian_of_map_injective _ hconjinj ?_
    exact isElemAbelian_of_le (by rw [hEbar_map]; exact inf_le_right) hA
  have hEbar_fix : ∀ x ∈ Ebar, b x = x := by
    intro x hx
    have hcomm : Commute b (MulAut.conj x) := kd264F8_commute hA hbA hx
    have h1 : MulAut.conj (b x) = MulAut.conj x := by
      rw [← mulAut_conj_conj, hcomm.eq]
      group
    exact hconjinj h1
  have hEbar_ι : Ebar ≤ ι.range := by
    intro x hx
    have hx3 : x ^ 3 = 1 := by
      apply hconjinj
      rw [map_pow, map_one]
      exact hA.2 _ hx
    exact hι3 x (hEbar_fix x hx) hx3
  let Et : Subgroup (VecAut N) := Ebar.comap ι
  have hEt_map : Et.map ι = Ebar := Subgroup.map_comap_eq_self hEbar_ι
  have hEt_card : 9 ≤ Nat.card Et := by
    rw [← Subgroup.card_map_of_injective (K := Et) hιinj, hEt_map]
    exact hcardEbar
  have hEt_ab : IsElemAbelian 3 Et :=
    isElemAbelian_of_map_injective ι hιinj (by rw [hEt_map]; exact hEbar_ab)
  haveI : Fintype Et := Fintype.ofFinite Et
  have hle := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp.card_le_three_pow_half Et hEt_ab
  have h9 : 9 ≤ 3 ^ (Module.finrank (ZMod 2) (Fin N → ZMod 2) / 2) :=
    hEt_card.trans (Nat.card_eq_fintype_card.le.trans hle)
  rw [Module.finrank_fin_fun] at h9
  have h2 : N / 2 = 1 := by omega
  rw [h2] at h9
  omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln

end
