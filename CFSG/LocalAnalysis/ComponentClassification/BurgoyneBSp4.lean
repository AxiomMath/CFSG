module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSlices
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpBasic

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam coe_lam pairMat sl2Diag
  coe_sl2Diag statedSp_ext mem_statedSp_iff isSupp_pairMat IsSupp.commute)
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K]

theorem lam_zero_commute_lam_one (X Y : SL(2, K)) :
    lam (k := K) (0 : Fin 2) X * lam 1 Y = lam 1 Y * lam 0 X := by
  apply statedSp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_lam]
  refine (IsSupp.commute (isSupp_pairMat _) (isSupp_pairMat _) ?_).eq
  rw [Set.disjoint_left]
  rintro x (rfl | rfl) (h | h) <;> simp_all

theorem lrInv_zero_mul_lrInv_one :
    (((lrInv K (0 : Fin 2) * lrInv K 1 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
  simp only [Subgroup.coe_mul, Units.val_mul, coe_lrInv]
  ext x y
  rcases x with (x | x) <;> rcases y with (y | y) <;> fin_cases x <;> fin_cases y <;>
    simp [offInd, lrPair, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      diagonal_apply, one_apply] <;> norm_num

omit [Field K] in
theorem lrInv_mul_self [Field K] (i : Fin 2) : lrInv K i * lrInv K i = 1 :=
  mul_self_eq_one_of_sl (lrInv_mem i) (longRootEquiv K i) (longRootEquiv_lrInv i)

theorem lrInv_one_inv_mul :
    (lrInv K (1 : Fin 2))⁻¹ * lrInv K (0 : Fin 2) = lrInv K 0 * lrInv K 1 := by
  rw [inv_eq_of_mul_eq_one_right (lrInv_mul_self 1)]
  exact (lam_zero_commute_lam_one (sl2Diag (-1)) (sl2Diag (-1))).symm

theorem projH_lrInv_one :
    projH (StatedSp 2 K) (lrInv K 1) = projH (StatedSp 2 K) (lrInv K (0 : Fin 2)) := by
  rw [projH_eq_projH_iff, lrInv_one_inv_mul, mem_subgroupOf]
  refine ⟨-1, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, lrInv_zero_mul_lrInv_one]
  ext i j
  by_cases h : i = j <;> simp [h]

abbrev sp4u (K : Type) [Field K] : MulAut (StatedProj (StatedSp 2 K)) :=
  conjProjH (StatedSp 2 K) (lrInv K (0 : Fin 2))

theorem conjProjH_lrInv_one :
    conjProjH (StatedSp 2 K) (lrInv K (1 : Fin 2)) = sp4u K := by
  change MulAut.conj (projH _ (lrInv K 1)) = MulAut.conj (projH _ (lrInv K 0))
  rw [projH_lrInv_one]

theorem slice_commute {a b : MulAut (StatedProj (StatedSp 2 K))}
    (ha : a ∈ slice (longRoot K (0 : Fin 2))) (hb : b ∈ slice (longRoot K (1 : Fin 2))) :
    a * b = b * a := by
  obtain ⟨_, ⟨X, rfl⟩, rfl⟩ := ha
  obtain ⟨_, ⟨Y, rfl⟩, rfl⟩ := hb
  rw [← map_mul, ← map_mul, lam_zero_commute_lam_one]

theorem conjProjH_lrInv (i : Fin 2) : conjProjH (StatedSp 2 K) (lrInv K i) = sp4u K := by
  fin_cases i
  · rfl
  · exact conjProjH_lrInv_one

theorem sp4u_mem_slice (i : Fin 2) : sp4u K ∈ slice (longRoot K i) := by
  fin_cases i
  · exact ⟨_, lrInv_mem 0, rfl⟩
  · exact ⟨_, lrInv_mem 1, conjProjH_lrInv_one⟩

variable [Finite K]

omit [Finite K] in
theorem orderOf_sp4u (hK : ringChar K ≠ 2)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K)))) : orderOf (sp4u K) = 2 :=
  orderOf_sliceInv hinj (longRoot_inf le_rfl 0) hK (lrInv_mem 0) (longRootEquiv K 0)
    (longRootEquiv_lrInv 0)

omit [Finite K] in
theorem slice_inter
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))))
    (hu2 : sp4u K * sp4u K = 1) {x : MulAut (StatedProj (StatedSp 2 K))}
    (hx₀ : x ∈ slice (longRoot K (0 : Fin 2))) (hx₁ : x ∈ slice (longRoot K (1 : Fin 2))) :
    x = 1 ∨ x = sp4u K := by
  have hZ := center_slice hinj (longRoot_inf le_rfl 0) (lrInv_mem 0) (longRootEquiv K 0)
    (longRootEquiv_lrInv 0)
  have hxZ : x ∈ (center (slice (longRoot K (0 : Fin 2)))).map
      (slice (longRoot K (0 : Fin 2))).subtype := by
    refine ⟨⟨x, hx₀⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    rintro ⟨a, ha⟩
    exact Subtype.ext (slice_commute ha hx₁)
  rw [hZ] at hxZ
  exact eq_one_or_eq_of_mem_zpowers (by rw [pow_two]; exact hu2) hxZ

omit [Finite K] in
theorem slice_le_centralizer_sp4u (i : Fin 2) :
    slice (longRoot K i) ≤ centralizer ({sp4u K} : Set (MulAut (StatedProj (StatedSp 2 K)))) := by
  have h := slice_le_centralizer (longRoot_commute (K := K) i)
  rwa [conjProjH_lrInv i] at h

theorem slice_isPComponent_sp4u (hK : ringChar K ≠ 2) (h5 : 5 ≤ Nat.card K)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range ≤
      B) (i : Fin 2) :
    IsPComponent 2 ((slice (longRoot K i)).subgroupOf
      (B ⊓ centralizer ({sp4u K} : Set (MulAut (StatedProj (StatedSp 2 K)))))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have h := slice_isPComponent hinj hB (longRoot_inf le_rfl i) hK (by omega) (lrInv_mem i)
    (longRootEquiv K i) (longRootEquiv_lrInv i) (longRoot_commute i) (longRoot_normalized h2 i)
  rwa [conjProjH_lrInv i] at h

abbrev PairScalar (i : Fin 2) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) : Prop :=
  M (Sum.inl i) (Sum.inr i) = 0 ∧ M (Sum.inr i) (Sum.inl i) = 0 ∧
    M (Sum.inl i) (Sum.inl i) = M (Sum.inr i) (Sum.inr i)

theorem sp4_actsProperly
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp 2 K) →*
      MulAut (StatedProj (StatedSp 2 K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp 2 K)))} {A : gsp 2 K}
    (hAt : orderOf (conjAut 2 K A) = 2)
    (hAblk : ∀ i : Fin 2, BlockDiag (lrPair i)
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (hAnc : ∀ i : Fin 2, ¬ PairScalar i
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (hcore : ∀ y ∈ oddCoreIn B (conjAut 2 K A), ∃ D : gsp 2 K, y = conjAut 2 K D ∧
      (∀ i : Fin 2, BlockDiag (lrPair i)
        ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ∧
      ∀ i : Fin 2, PairScalar i
        ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) →
        conjAut 2 K D = 1)
    {Y : Subgroup (MulAut (StatedProj (StatedSp 2 K)))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (conjAut 2 K A)) (i : Fin 2) :
    ActsProperly (conjAut 2 K A) Y (slice (longRoot K i)) ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  refine actsProperly_of_core hAt hY hYO (conjAut_mem_normalizer_slice (hAblk i)) ?_ ?_ ?_
  · by_contra h
    push Not at h
    exact hAnc i (pairBlock_scalar_of_commute_slice (p := p) hinj (hAblk i) h)
  · intro y hy
    obtain ⟨D, rfl, hDb, -⟩ := hcore y hy
    exact conjAut_mem_normalizer_slice (hDb i)
  · intro y hy hc
    obtain ⟨D, rfl, hDb, hDs⟩ := hcore y hy
    exact hDs i (pairBlock_scalar_of_commute_slice (p := p) hinj (hDb i) hc)

end CFSG.ComponentClassification.Burgoyne.B
