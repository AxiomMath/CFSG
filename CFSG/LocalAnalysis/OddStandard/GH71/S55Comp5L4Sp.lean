module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Gen

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

namespace C5

theorem det_of_mem_statedSp {A : GL (Fin 2 ⊕ Fin 2) K} (hA : A ∈ StatedSp 2 K) :
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).det = 1 :=
  SymplecticGroup.det_eq_one (TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp
    ((ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := K)).le hA))

@[expose] noncomputable def spSL : StatedSp 2 K →* SpecialLinearGroup (Fin 4) K where
  toFun M := ⟨reindexAlgEquiv K K finSumFinEquiv
      ((M : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K), by
    rw [coe_reindexAlgEquiv, det_reindex_self]
    exact det_of_mem_statedSp M.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' M N := Subtype.ext (by
    change reindexAlgEquiv K K finSumFinEquiv
        (((M * N : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      reindexAlgEquiv K K finSumFinEquiv
          ((M : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        reindexAlgEquiv K K finSumFinEquiv
          ((N : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    rw [Subgroup.coe_mul, Units.val_mul, map_mul])

theorem coe_spSL (M : StatedSp 2 K) :
    ((spSL M : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      reindex finSumFinEquiv finSumFinEquiv
        ((M : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  change reindexAlgEquiv K K finSumFinEquiv _ = _
  rw [coe_reindexAlgEquiv]

theorem spSL_injective : Function.Injective (spSL (K := K)) := by
  intro M N h
  have h' := congrArg (fun A : SpecialLinearGroup (Fin 4) K => (A : Matrix (Fin 4) (Fin 4) K)) h
  simp only [coe_spSL] at h'
  exact Subtype.ext (Units.ext ((reindex finSumFinEquiv finSumFinEquiv).injective h'))

theorem reindex_scalar (c : K) :
    reindex finSumFinEquiv finSumFinEquiv (scalar (Fin 2 ⊕ Fin 2) c) = scalar (Fin 4) c := by
  ext i j
  simp [scalar_apply, diagonal_apply]

end C5

open C5

theorem ker_projSp :
    ((proj 4 K).comp spSL).ker = (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K) := by
  ext M
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars,
    Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨c, -, hc⟩
    refine ⟨c, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar]
    apply (reindex finSumFinEquiv finSumFinEquiv).injective
    rw [reindex_scalar, ← coe_spSL, hc]
  · rintro ⟨c, hc⟩
    have hM : ((spSL M : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        scalar (Fin 4) (c : K) := by
      rw [coe_spSL, ← hc, GeneralLinearGroup.coe_scalar, reindex_scalar]
    refine ⟨c, Units.ext ?_, hM⟩
    have hd := (spSL M).2
    rw [hM, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hd
    rw [Units.val_pow_eq_pow_val, hd, Units.val_one]

noncomputable def projSpEquiv :
    StatedProj (StatedSp 2 K) ≃* ↥((proj 4 K).comp (spSL (K := K))).range :=
  ((QuotientGroup.quotientKerEquivRange _).symm.trans
    (QuotientGroup.quotientMulEquivOfEq ker_projSp)).symm

theorem index_range_spSL [Finite K] :
    (spSL (K := K)).range.index = Nat.card K ^ 2 * (Nat.card K ^ 3 - 1) := by
  have h1 := Subgroup.card_mul_index (spSL (K := K)).range
  rw [← Nat.card_congr (MonoidHom.ofInjective spSL_injective).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 2,
    LinearFlag.card_SL_eq (by norm_num)] at h1
  set q := Nat.card K
  have hq : 1 < q := Finite.one_lt_card
  have p1 : ∏ j ∈ Finset.Icc 1 2, (q ^ (2 * j) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) := by
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  have p2 : ∏ j ∈ Finset.Icc 2 4, (q ^ j - 1) = (q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)) := by
    rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
      Finset.prod_pair (by norm_num)]
  rw [p1, p2] at h1
  norm_num at h1
  have hA : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero hq)
  have hC : 0 < q ^ 4 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq)
  generalize q ^ 2 - 1 = A at h1 hA
  generalize q ^ 3 - 1 = B at h1 ⊢
  generalize q ^ 4 - 1 = C at h1 hC
  refine Nat.eq_of_mul_eq_mul_left (n := q ^ 4 * (A * C)) (by positivity) ?_
  rw [h1]
  ring

theorem index_range_projSp_dvd [Finite K] :
    ((proj 4 K).comp (spSL (K := K))).range.index ∣ Nat.card K ^ 2 * (Nat.card K ^ 3 - 1) := by
  rw [MonoidHom.range_comp, ← index_range_spSL]
  exact Subgroup.index_map_dvd _ (proj_surjective 4 K)

theorem card_scalars_le [Finite K] : Nat.card (scalars 4 K) ≤ Nat.card K - 1 := by
  rw [← Nat.card_units K]
  refine Nat.card_le_card_of_injective
    (fun A => Units.mk0 (((A : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0)
      (by
        obtain ⟨c, -, hc⟩ := mem_scalars.mp A.2
        rw [hc, scalar_apply, diagonal_apply_eq]
        exact c.ne_zero)) ?_
  intro A B h
  have h' := congrArg Units.val h
  simp only [Units.val_mk0] at h'
  obtain ⟨a, -, ha⟩ := mem_scalars.mp A.2
  obtain ⟨b, -, hb⟩ := mem_scalars.mp B.2
  rw [ha, hb, scalar_apply, scalar_apply, diagonal_apply_eq, diagonal_apply_eq] at h'
  apply Subtype.ext
  apply Subtype.ext
  rw [ha, hb, h']

theorem range_projSp_ne_top [Finite K] : ((proj 4 K).comp (spSL (K := K))).range ≠ ⊤ := by
  intro htop
  set q := Nat.card K
  have h1 : Nat.card (SpecialLinearGroup (Fin 4) K ⧸ scalars 4 K) ≤ Nat.card (StatedSp 2 K) := by
    have e : Nat.card ↥((proj 4 K).comp (spSL (K := K))).range =
        Nat.card (SpecialLinearGroup (Fin 4) K ⧸ scalars 4 K) := by
      rw [htop, Subgroup.card_top]
    rw [← e]
    exact Nat.card_le_card_of_surjective _ ((proj 4 K).comp spSL).rangeRestrict_surjective
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars 4 K)
  have h3 := card_scalars_le (K := K)
  have h4 := Subgroup.card_mul_index (spSL (K := K)).range
  rw [index_range_spSL, ← Nat.card_congr (MonoidHom.ofInjective spSL_injective).toEquiv] at h4
  have hpos : 0 < Nat.card (StatedSp 2 K) := Nat.card_pos
  have h5 : Nat.card (StatedSp 2 K) * (q ^ 2 * (q ^ 3 - 1)) ≤
      Nat.card (StatedSp 2 K) * (q - 1) := by
    rw [h4, h2]
    exact Nat.mul_le_mul h1 h3
  have h6 := Nat.le_of_mul_le_mul_left h5 hpos
  have hq : 1 < q := Finite.one_lt_card
  have h7 : q < q ^ 3 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ < q ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
  have h8 : q - 1 < q ^ 2 * (q ^ 3 - 1) := by
    calc q - 1 < q ^ 3 - 1 := by omega
      _ ≤ q ^ 2 * (q ^ 3 - 1) := Nat.le_mul_of_pos_left _ (by positivity)
  omega

end CFSG.OddStandard.GH71.S55
