module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

@[expose] def swapMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  kron 1 !![0, 1; 1, 0]

theorem swapMat_symplectic :
    (swapMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K * swapMat = formJ 2 K := by
  have hσ : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K)ᵀ * !![0, 1; 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [swapMat]
  exact (kron_symplectic_iff (1 : Matrix (Fin 2) (Fin 2) K) !![0, 1; 1, 0]).mpr (by
    rw [det_one, one_smul, hσ])

theorem swapMat_mul_blk (g h : Matrix (Fin 2) (Fin 2) K) :
    swapMat * blk g h = blk h g * swapMat := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [swapMat, kron, blk, diag2, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

variable (K) in
@[expose] def swapSp : StatedSp 2 K := toSp swapMat swapMat_symplectic

theorem swapSp_mul_swapSp : swapSp K * swapSp K = 1 := by
  apply sp_ext
  have hσ : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Subgroup.coe_mul, Units.val_mul, coe_toSp, swapSp, swapMat]
  rw [kron_mul, hσ, one_mul, kron_one_one]
  simp

theorem swapSp_mul_blkSL
    (x : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    swapSp K * blkSL K x = blkSL K x.swap * swapSp K := by
  apply sp_ext
  change swapMat * blk (x.1 : Matrix (Fin 2) (Fin 2) K) (x.2 : Matrix (Fin 2) (Fin 2) K) =
    blk (x.2 : Matrix (Fin 2) (Fin 2) K) (x.1 : Matrix (Fin 2) (Fin 2) K) * swapMat
  rw [swapMat_mul_blk]

theorem swapMat_mul_blk_one_neg_one :
    swapMat * blk (1 : Matrix (Fin 2) (Fin 2) K) (-1) =
      -1 * (blk (1 : Matrix (Fin 2) (Fin 2) K) (-1) * swapMat) := by
  rw [swapMat_mul_blk]
  have hneg : blk (-1 : Matrix (Fin 2) (Fin 2) K) 1 = -blk 1 (-1) := by
    simpa using (blk_neg (1 : Matrix (Fin 2) (Fin 2) K) (-1)).symm
  rw [hneg, Matrix.neg_mul, neg_one_mul]

@[expose] def swapCentralizerNegOne : StatedSp 2 K :=
  toSp (-1) (by
    rw [transpose_neg, transpose_one, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg,
      Matrix.mul_one, neg_neg])

theorem proj_swapCentralizerNegOne :
    proj 2 K (swapCentralizerNegOne (K := K)) = 1 := by
  rw [← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff]
  exact Or.inr rfl

theorem swapSp_mul_T1 :
    swapSp K * T1 K = swapCentralizerNegOne * (T1 K * swapSp K) := by
  apply sp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, swapSp, swapCentralizerNegOne, coe_T1, coe_toSp]
  exact swapMat_mul_blk_one_neg_one (K := K)

theorem proj_swapSp_mem_centralizer_u1 :
    proj 2 K (swapSp K) ∈ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))) := by
  rw [mem_centralizer_singleton_iff, u1, ← map_mul, ← map_mul]
  calc proj 2 K (swapSp K * T1 K)
      = proj 2 K (swapCentralizerNegOne * (T1 K * swapSp K)) := by rw [swapSp_mul_T1]
    _ = proj 2 K (swapCentralizerNegOne) * proj 2 K (T1 K * swapSp K) := by rw [map_mul]
    _ = 1 * proj 2 K (T1 K * swapSp K) := by rw [proj_swapCentralizerNegOne]
    _ = proj 2 K (T1 K * swapSp K) := by rw [one_mul]

theorem proj_swapSp_not_mem_X0 (h2 : (2 : K) ≠ 0) : proj 2 K (swapSp K) ∉ X0 K := by
  intro h
  obtain ⟨y, hy⟩ := (mem_X0 h2).mp h
  have hmat := eq_or_eq_neg_of_proj_eq hy
  have h0 : (((blkSL K y : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inl 1) = 0 := by
    rw [coe_blkSL]
    simp [blk, diag2]
  have hs1 : (((swapSp K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inl 1) = 1 := by
    rw [swapSp, coe_toSp]
    simp [swapMat, kron]
  rcases hmat with hmat | hmat
  · have := congrFun (congrFun hmat (Sum.inl 0)) (Sum.inl 1)
    rw [hs1, h0] at this
    exact one_ne_zero this
  · have := congrFun (congrFun hmat (Sum.inl 0)) (Sum.inl 1)
    rw [hs1, Matrix.neg_apply, h0, neg_zero] at this
    exact one_ne_zero this

theorem card_ker_proj_blkSL (h2 : (2 : K) ≠ 0) :
    Nat.card ((proj 2 K).comp (blkSL K)).ker = 2 := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      StatedProj (StatedSp 2 K) := (proj 2 K).comp (blkSL K)
  let z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K :=
    (negOneSL, negOneSL)
  have hz : z ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    change proj 2 K (blkSL K z) = 1
    exact (proj_blkSL_eq_one_iff z).mpr (Or.inr ⟨rfl, rfl⟩)
  have hmem : ∀ u : f.ker, u = ⟨1, f.ker.one_mem⟩ ∨ u = ⟨z, hz⟩ := by
    intro u
    have hu : u.1 ∈ f.ker := u.2
    rw [MonoidHom.mem_ker] at hu
    change proj 2 K (blkSL K u.1) = 1 at hu
    rcases (proj_blkSL_eq_one_iff u.1).mp hu with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · left
      exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2'))
    · right
      exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2'))
  have hne : (⟨z, hz⟩ : f.ker) ≠ ⟨1, f.ker.one_mem⟩ := by
    intro h
    have hp : z = (1 : Matrix.SpecialLinearGroup (Fin 2) K ×
        Matrix.SpecialLinearGroup (Fin 2) K) := Subtype.ext_iff.mp h
    have h1 : ((negOneSL : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (1 : Matrix (Fin 2) (Fin 2) K) := by
      have := congrArg (fun p : Matrix.SpecialLinearGroup (Fin 2) K ×
          Matrix.SpecialLinearGroup (Fin 2) K => (p.1 : Matrix (Fin 2) (Fin 2) K)) hp
      simpa [z] using this
    rw [coe_negOneSL] at h1
    exact one_ne_neg_one_mat h2 h1.symm
  rw [Nat.card_eq_two_iff' (⟨1, f.ker.one_mem⟩ : f.ker)]
  refine ⟨⟨z, hz⟩, hne, ?_⟩
  intro u hu
  rcases hmem u with h1 | h1
  · exact absurd h1 hu
  · exact h1

theorem two_mul_card_X0 [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (X0 K) * 2 = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) ^ 2 := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      StatedProj (StatedSp 2 K) := (proj 2 K).comp (blkSL K)
  have hker : Nat.card f.ker = 2 := by
    change Nat.card ((proj 2 K).comp (blkSL K)).ker = 2
    exact card_ker_proj_blkSL h2
  have hrange : f.range = X0 K := by
    ext x
    rw [MonoidHom.mem_range, mem_X0 h2]
    rfl
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, Nat.card_prod] at hcard
  rw [pow_two, mul_comm (Nat.card (X0 K)) 2]
  exact hcard

theorem swapSp_conj_blkSL_sq
    (x : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    swapSp K * blkSL K x * swapSp K = blkSL K x.swap := by
  rw [swapSp_mul_blkSL, mul_assoc, swapSp_mul_swapSp, mul_one]

theorem inv_swapSp : (swapSp K)⁻¹ = swapSp K :=
  inv_eq_of_mul_eq_one_right swapSp_mul_swapSp

theorem swapSp_mem_normalizer_blkSL_range :
    swapSp K ∈ Subgroup.normalizer ((blkSL K).range : Set (StatedSp 2 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  simp only [inv_swapSp]
  intro y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.swap, (swapSp_conj_blkSL_sq x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨x.swap, ?_⟩
    have hy : y = blkSL K x.swap := by
      calc y = (swapSp K * swapSp K) * y * (swapSp K * swapSp K) := by
            rw [swapSp_mul_swapSp, one_mul, mul_one]
        _ = swapSp K * (swapSp K * y * swapSp K) * swapSp K := by group
        _ = swapSp K * blkSL K x * swapSp K := by rw [← hx]
        _ = blkSL K x.swap := swapSp_conj_blkSL_sq x
    exact hy.symm

theorem swapSp_mem_normalizer_centralizer (h2 : (2 : K) ≠ 0) :
    swapSp K ∈
      Subgroup.normalizer ((centralizer ({T1 K} : Set (StatedSp 2 K))) :
        Set (StatedSp 2 K)) := by
  have hC : (centralizer ({T1 K} : Set (StatedSp 2 K))) = (blkSL K).range := by
    ext x
    exact mem_centralizer_T1_iff h2
  rw [hC]
  exact swapSp_mem_normalizer_blkSL_range

theorem proj_swapSp_mem_normalizer_X0 (h2 : (2 : K) ≠ 0) :
    proj 2 K (swapSp K) ∈ Subgroup.normalizer (X0 K) := by
  have hC := swapSp_mem_normalizer_centralizer h2
  have hmap : proj 2 K (swapSp K) ∈
      (Subgroup.normalizer (centralizer ({T1 K} : Set (StatedSp 2 K)))).map (proj 2 K) :=
    Subgroup.mem_map_of_mem (proj 2 K) hC
  have hle := Subgroup.le_normalizer_map (H := centralizer ({T1 K} : Set (StatedSp 2 K)))
    (proj 2 K) hmap
  simpa [X0] using hle

theorem orderOf_proj_swapSp (h2 : (2 : K) ≠ 0) :
    orderOf (proj 2 K (swapSp K)) = 2 := by
  have hg_sq : proj 2 K (swapSp K) * proj 2 K (swapSp K) = 1 := by
    rw [← map_mul, swapSp_mul_swapSp, map_one]
  have hg_ne : proj 2 K (swapSp K) ≠ 1 := by
    intro h
    exact proj_swapSp_not_mem_X0 h2 (h ▸ (X0 K).one_mem)
  apply orderOf_eq_prime
  · rwa [pow_two]
  · exact hg_ne

theorem disjoint_X0_zpowers_proj_swapSp [Finite K] (h2 : (2 : K) ≠ 0) :
    Disjoint (X0 K) (Subgroup.zpowers (proj 2 K (swapSp K))) := by
  rw [disjoint_iff]
  let g := proj 2 K (swapSp K)
  have hord : orderOf g = 2 := orderOf_proj_swapSp h2
  haveI : Finite (Subgroup.zpowers g) := by
    rw [finite_zpowers, ← orderOf_pos_iff, hord]
    norm_num
  have hdvd : Nat.card ↥(X0 K ⊓ Subgroup.zpowers g) ∣ 2 := by
    have := Subgroup.card_dvd_of_le
      (inf_le_right : X0 K ⊓ Subgroup.zpowers g ≤ Subgroup.zpowers g)
    rwa [Nat.card_zpowers, hord] at this
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2card
  · exact (Subgroup.card_eq_one).mp h1
  · exfalso
    have hIeq : X0 K ⊓ Subgroup.zpowers g = Subgroup.zpowers g := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_right
      rw [h2card, Nat.card_zpowers, hord]
    have hgmem : g ∈ X0 K ⊓ Subgroup.zpowers g := by
      rw [hIeq]
      exact Subgroup.mem_zpowers g
    exact proj_swapSp_not_mem_X0 h2 hgmem.1

theorem card_sl2_sq_dvd_card_centralizer_u1 [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) ^ 2 ∣
      Nat.card (centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))) := by
  let g := proj 2 K (swapSp K)
  let Y : Subgroup (StatedProj (StatedSp 2 K)) := X0 K ⊔ Subgroup.zpowers g
  have hYle : Y ≤ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))) := by
    rw [show Y = X0 K ⊔ Subgroup.zpowers g from rfl, sup_le_iff]
    exact ⟨X0_le_centralizer,
      Subgroup.zpowers_le.mpr (proj_swapSp_mem_centralizer_u1)⟩
  have hcardY : Nat.card Y = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) ^ 2 := by
    have hsup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (X0 K) (Subgroup.zpowers g)
      (Subgroup.zpowers_le.mpr (proj_swapSp_mem_normalizer_X0 h2))
      (disjoint_X0_zpowers_proj_swapSp h2)
    have hcard : Nat.card ↥(X0 K ⊔ Subgroup.zpowers g) = Nat.card (X0 K) * 2 := by
      rw [hsup, Nat.card_zpowers, orderOf_proj_swapSp h2]
    rw [show Y = X0 K ⊔ Subgroup.zpowers g from rfl, hcard, two_mul_card_X0 h2]
  have hdvd := Subgroup.card_dvd_of_le hYle
  rwa [hcardY] at hdvd

end CFSG.ComponentClassification.CatFactsSp4
