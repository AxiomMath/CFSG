module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.ExcE6Sign
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Pair2E6Image
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Pair2E6Theta
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models.TwistedPairs
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.ClassicalInvolution.RouteD (path6 path6_ne theta6)
open scoped MatrixGroups

section Center

variable {k : Type} [Field k]

private lemma coe_negOneTwo_eq_scalar_neg_one (k : Type) [Field k] :
    (negOneTwo k : Matrix (Fin 2) (Fin 2) k) = Matrix.scalar (Fin 2) (-1 : k) := by
  have hcen : negOneTwo k ∈ center SL(2, k) :=
    Subgroup.mem_center_iff.mpr (fun g => (negOneTwo_mul_comm g).symm)
  obtain ⟨s, hs, hsr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcen
  rw [Fintype.card_fin] at hs
  have hs2 : s ^ 2 = 1 := by simpa using hs
  by_cases h2 : (2 : k) = 0
  · have hneg : (-1 : k) = 1 := by
      rw [show (-1 : k) = 1 - 2 by ring, h2, sub_zero]
    rcases sq_eq_one_iff.mp hs2 with h1 | h1
    · rw [h1] at hsr
      rw [hneg]
      exact hsr.symm
    · rw [h1] at hsr
      exact hsr.symm
  · rcases sq_eq_one_iff.mp hs2 with h1 | h1
    · exfalso
      apply negOneTwo_ne_one h2
      apply Subtype.ext
      rw [← hsr, h1]
      simp
    · rw [h1] at hsr
      exact hsr.symm

private lemma fieldAutSL_negOneTwo (ψ : k ≃+* k) :
    fieldAutSL ψ 2 (negOneTwo k) = negOneTwo k := by
  apply Subtype.ext
  rw [coe_fieldAutSL, coe_negOneTwo_eq_scalar_neg_one k]
  ext i j
  by_cases h : i = j <;>
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply, h]

private lemma neg_blocks_mul_comm :
    blockSL2 k 5 4 (negOneTwo k) * blockSL2 k 5 2 (negOneTwo k) *
      blockSL2 k 5 0 (negOneTwo k) =
    blockSL2 k 5 0 (negOneTwo k) * blockSL2 k 5 2 (negOneTwo k) *
      blockSL2 k 5 4 (negOneTwo k) := by
  simp only [mul_assoc]
  rw [(blockSL2_comm 5 0 2 (by decide) (negOneTwo k) (negOneTwo k)).symm,
    blockSL2_comm 5 2 4 (by decide) (negOneTwo k) (negOneTwo k)]
  simp only [← mul_assoc]
  rw [(blockSL2_comm 5 0 4 (by decide) (negOneTwo k) (negOneTwo k)).symm]

private lemma coe_negOneSix_eq_scalar_neg_one [Finite k] (hk : Nat.card k = 9) :
    (negOneSix k : Matrix (Fin 6) (Fin 6) k) = Matrix.scalar (Fin 6) (-1 : k) := by
  letI : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card k = 9 := by
    rw [Fintype.card_eq_nat_card]; exact hk
  have hF : ringChar k ≠ 2 := by
    intro h2
    have hmod : Fintype.card k % 2 = 0 := (FiniteField.even_card_iff_char_two).1 h2
    rw [hcard] at hmod; norm_num at hmod
  have h2k : (2 : k) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨s, -, hsr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (negOneSix_mem_center k)
  have hs2 : s ^ 2 = 1 := by
    have hpow : (negOneSix k) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one (negOneSix k)
      rw [orderOf_negOneSix h2k] at h
      exact h
    have hmat : (Matrix.scalar (Fin 6) s : Matrix (Fin 6) (Fin 6) k) ^ 2 = 1 := by
      calc (Matrix.scalar (Fin 6) s : Matrix (Fin 6) (Fin 6) k) ^ 2
          = ((negOneSix k : SL(6, k)) : Matrix (Fin 6) (Fin 6) k) ^ 2 := by rw [← hsr]
        _ = (((negOneSix k) ^ 2 : SL(6, k)) : Matrix (Fin 6) (Fin 6) k) :=
            (Matrix.SpecialLinearGroup.coe_pow (negOneSix k) 2).symm
        _ = 1 := by rw [hpow, Matrix.SpecialLinearGroup.coe_one]
    have hsc : Matrix.scalar (Fin 6) (s ^ 2) = Matrix.scalar (Fin 6) (1 : k) := by
      rw [map_pow, hmat, map_one]
    exact Matrix.scalar_inj.mp hsc
  rcases sq_eq_one_iff.mp hs2 with h1 | h1
  · exfalso
    rw [h1, map_one] at hsr
    have hne : negOneSix k = 1 := Subtype.ext hsr.symm
    have hord := orderOf_negOneSix h2k
    rw [hne, orderOf_one] at hord
    norm_num at hord
  · rw [h1] at hsr
    exact hsr.symm

theorem eq_one_or_eq_negOneSix_of_mem_center_card_nine [Finite k] (hk : Nat.card k = 9)
    {g : SL(6, k)} (hg : g ∈ center SL(6, k)) : g = 1 ∨ g = negOneSix k := by
  letI : Fintype k := Fintype.ofFinite k
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (6 : ℕ) ≠ 0)] at hr
    exact zero_ne_one hr
  have hcard : Fintype.card k = 9 := by
    rw [Fintype.card_eq_nat_card]; exact hk
  have h8 : r ^ 8 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    rw [hcard] at h
    simpa using h
  have h2 : r ^ 2 = 1 := by
    rw [show (8 : ℕ) = 6 + 2 by norm_num, pow_add] at h8
    rwa [hr, one_mul] at h8
  rcases sq_eq_one_iff.mp h2 with rfl | rfl
  · left
    apply Subtype.ext
    rw [← hrg]
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.one_apply, h]
  · right
    apply Subtype.ext
    rw [← hrg]
    exact (coe_negOneSix_eq_scalar_neg_one hk).symm

theorem negOneSix_mem_unitaryGroup6 (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    negOneSix k ∈ unitaryGroup6 θ hθ := by
  rw [mem_unitaryGroup6]
  rw [negOneSix_eq_mul_blocks k, map_mul, map_mul,
    sigmaA6_blockSL2, sigmaA6_blockSL2, sigmaA6_blockSL2,
    fieldAutSL_negOneTwo]
  exact neg_blocks_mul_comm

end Center

section Kernel

variable {k : Type} [Field k]

theorem ker_theta6_le_center (hF : ringChar k ≠ 2) {Θ : SL(6, k) →* e6Data_valid.minGroup k}
    (h : ∀ i : Fin 5, Θ.comp (blockSL2 k 5 i) = e6Rank1 k (path6 i)) :
    Θ.ker ≤ center SL(6, k) := by
  refine CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (K := k) (n := 6)
      (by norm_num)) ?_
  refine ⟨blockSL2 k 5 0 (negOneTwo k), ?_⟩
  have h0 : Θ (blockSL2 k 5 0 (negOneTwo k)) = e6Rank1 k (path6 0) (negOneTwo k) :=
    DFunLike.congr_fun (h 0) (negOneTwo k)
  rw [h0]
  intro hcontra
  exact negOneTwo_ne_one (Ring.two_ne_zero hF)
    (e6Rank1_injective (path6 0) (hcontra.trans (map_one _).symm))

end Kernel

section Block

variable {k : Type} [Field k] [Finite k]

theorem e6EpsK_theta_block_neg (hF : ringChar k ≠ 2) (hε : Function.Injective (e6Isogeny k))
    {Θ : SL(6, k) →* e6Data_valid.minGroup k}
    (h : ∀ i : Fin 5, Θ.comp (blockSL2 k 5 i) = e6Rank1 k (path6 i)) (i : Fin 5) :
    e6EpsK k (Θ (blockSL2 k 5 i (negOneTwo k))) =
      rootDiagUnit .E6 (thetaDiag (Pi.single (path6 i : Fin (Tag.rank .E6)) 1) (-1 : kˣ)) := by
  have hγ : IsRoot .E6 (Pi.single (path6 i : Fin (Tag.rank .E6)) 1) := isRoot_single .E6 _
  have hmemR : ∀ x : SL(6, k), x ∈ (blockSL2 k 5 i).range →
      Θ x ∈ stdRankOne (e6Datum k) (Pi.single (path6 i : Fin (Tag.rank .E6)) 1) := by
    intro x hx
    have h' := Subgroup.mem_map_of_mem Θ hx
    rw [map_blockSL2_range_theta6 h i] at h'
    exact h'
  have hbmem : blockSL2 k 5 i (negOneTwo k) ∈ (blockSL2 k 5 i).range := ⟨_, rfl⟩
  have hz : e6Isogeny k (Θ (blockSL2 k 5 i (negOneTwo k))) ∈
      stdRankOne (e6AdjDatum k) (Pi.single (path6 i : Fin (Tag.rank .E6)) 1) := by
    rw [← map_stdRankOne_e6_genK (k := k) hγ]
    exact Subgroup.mem_map_of_mem _ (hmemR _ hbmem)
  have hzc : ∀ r ∈ stdRankOne (e6AdjDatum k) (Pi.single (path6 i : Fin (Tag.rank .E6)) 1),
      e6Isogeny k (Θ (blockSL2 k 5 i (negOneTwo k))) * r =
      r * e6Isogeny k (Θ (blockSL2 k 5 i (negOneTwo k))) := by
    intro r hr
    rw [← map_stdRankOne_e6_genK (k := k) hγ] at hr
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hr
    have hs' : s ∈ (blockSL2 k 5 i).range.map Θ := by
      rw [map_blockSL2_range_theta6 h i]
      exact hs
    obtain ⟨a, ⟨A, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hs'
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      negOneTwo_mul_comm A]
  rcases central_stdRankOne_e6_gen hF hγ hz hzc with h1 | h1
  · exfalso
    have h2 : e6EpsK k (Θ (blockSL2 k 5 i (negOneTwo k))) = e6EpsK k 1 := by
      rw [map_one]
      exact h1
    have h3 : Θ (blockSL2 k 5 i (negOneTwo k)) = 1 := e6EpsK_injective hε h2
    have h4 : e6Rank1 k (path6 i) (negOneTwo k) = 1 := by
      rw [← DFunLike.congr_fun (h i) (negOneTwo k)]
      simpa only [MonoidHom.comp_apply] using h3
    exact negOneTwo_ne_one (Ring.two_ne_zero hF)
      (e6Rank1_injective (path6 i) (h4.trans (map_one _).symm))
  · exact h1

theorem e6EpsK_theta_negOneSix (hF : ringChar k ≠ 2) (hε : Function.Injective (e6Isogeny k))
    {Θ : SL(6, k) →* e6Data_valid.minGroup k}
    (h : ∀ i : Fin 5, Θ.comp (blockSL2 k 5 i) = e6Rank1 k (path6 i)) :
    e6EpsK k (Θ (negOneSix k)) = rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : kˣ)) := by
  rw [negOneSix_eq_mul_blocks, map_mul, map_mul, map_mul, map_mul,
    e6EpsK_theta_block_neg hF hε h 0, e6EpsK_theta_block_neg hF hε h 2,
    e6EpsK_theta_block_neg hF hε h 4, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
    thetaDiag_mul_blocks]

theorem theta6_negOneSix_ne_one (hF : ringChar k ≠ 2) (hε : Function.Injective (e6Isogeny k))
    {Θ : SL(6, k) →* e6Data_valid.minGroup k}
    (h : ∀ i : Fin 5, Θ.comp (blockSL2 k 5 i) = e6Rank1 k (path6 i)) :
    Θ (negOneSix k) ≠ 1 := by
  intro h1
  have h2 := e6EpsK_theta_negOneSix hF hε h
  rw [h1, map_one] at h2
  exact rootDiagUnit_thetaDiag_ne_one_e6 hF isRoot_thetaE6 h2.symm

theorem theta6_injective (hk : Nat.card k = 9) (hF : ringChar k ≠ 2)
    (hε : Function.Injective (e6Isogeny k)) {Θ : SL(6, k) →* e6Data_valid.minGroup k}
    (h : ∀ i : Fin 5, Θ.comp (blockSL2 k 5 i) = e6Rank1 k (path6 i)) :
    Function.Injective Θ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases eq_one_or_eq_negOneSix_of_mem_center_card_nine hk
      (ker_theta6_le_center hF h hg) with h' | h'
  · exact h'
  · rw [h'] at hg
    exact absurd hg (theta6_negOneSix_ne_one hF hε h)

end Block

end CFSG.OddStandard.HigherRank.F3
