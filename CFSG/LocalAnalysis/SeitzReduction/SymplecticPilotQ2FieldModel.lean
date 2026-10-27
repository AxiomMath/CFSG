module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SwapOverlap
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactEquivariance

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

section SL2

theorem entries_of_commute_zThreeSL {B : SL(2, K)} (h : B * zThreeSL = zThreeSL * B) :
    (B : Matrix (Fin 2) (Fin 2) K) 1 0 = -(B : Matrix (Fin 2) (Fin 2) K) 0 1 ∧
      (B : Matrix (Fin 2) (Fin 2) K) 1 1 =
        (B : Matrix (Fin 2) (Fin 2) K) 0 0 - (B : Matrix (Fin 2) (Fin 2) K) 0 1 := by
  have hM := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_zThreeSL] at hM
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, zThreeMat, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one] at h00 h01
  constructor
  · linear_combination -h00
  · linear_combination -h01

theorem commute_zThreeSL_of_entries {B : SL(2, K)}
    (h10 : (B : Matrix (Fin 2) (Fin 2) K) 1 0 = -(B : Matrix (Fin 2) (Fin 2) K) 0 1)
    (h11 : (B : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (B : Matrix (Fin 2) (Fin 2) K) 0 0 - (B : Matrix (Fin 2) (Fin 2) K) 0 1) :
    B * zThreeSL = zThreeSL * B := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_zThreeSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, zThreeMat, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one, h10,
      h11] <;> ring

theorem commute_of_commute_zThreeSL {B B' : SL(2, K)} (h : B * zThreeSL = zThreeSL * B)
    (h' : B' * zThreeSL = zThreeSL * B') : B * B' = B' * B := by
  obtain ⟨h10, h11⟩ := entries_of_commute_zThreeSL h
  obtain ⟨h10', h11'⟩ := entries_of_commute_zThreeSL h'
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.isValue, Fin.mk_one, h10,
      h11, h10', h11'] <;> ring

end SL2

section Centralizer

variable {k : Fin n}

theorem exists_eq_mul_of_commute_nsElt_of_charTwo [CharP K 2] {x : StatedSp n K}
    (hx : x * nsElt k = nsElt k * x) :
    ∃ B : SL(2, K), B * zThreeSL = zThreeSL * B ∧ ∃ y ∈ complSp K k, x = longBlock K n k B * y := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  have hoff : ∀ r t, r ∉ coords k → t ∈ coords k → mat n K x r t = 0 := by
    intro r t hr ht
    rcases mem_coords.1 ht with rfl | rfl
    · exact (mat_apply_eq_zero_of_commute_nsElt hx hr).1
    · exact (mat_apply_eq_zero_of_commute_nsElt hx hr).2
  have hdet : (stdBlock k (mat n K x)).det = 1 :=
    det_stdBlock_eq_one x k fun r hr => hoff r _ hr (inl_mem_coords k)
  have hM := congrArg (mat n K) hx
  rw [map_mul, map_mul] at hM
  have e1 := mul_mat_nsElt_apply (mat n K x) (Sum.inl k) (inl_mem_coords k)
  have e2 := mul_mat_nsElt_apply (mat n K x) (Sum.inl k) (inr_mem_coords k)
  rw [hM, mat_nsElt_mul_apply _ (inl_mem_coords k)] at e1 e2
  rw [mat_nsElt_inl_inl, mat_nsElt_inl_inr, mat_nsElt_inr_inl] at e1
  rw [mat_nsElt_inl_inl, mat_nsElt_inl_inr, mat_nsElt_inr_inr] at e2
  set B : SL(2, K) := mkSL (stdBlock k (mat n K x)) hdet with hB
  have hBC : B * zThreeSL = zThreeSL * B := by
    apply commute_zThreeSL_of_entries
    · simp only [hB, coe_mkSL, stdBlock, of_apply, cons_val', cons_val_zero, cons_val_one,
        empty_val', cons_val_fin_one]
      linear_combination e1
    · simp only [hB, coe_mkSL, stdBlock, of_apply, cons_val', cons_val_zero, cons_val_one,
        empty_val', cons_val_fin_one]
      linear_combination e2
  set a : StatedSp n K := longBlock K n k B with ha
  have hcol : ∀ u t, t ∈ coords k → mat n K x u t = mat n K a u t := by
    intro u t ht
    by_cases hu : u ∈ coords k
    · rw [ha, mat_longBlock, hB, coe_mkSL]
      rcases mem_coords.1 hu with rfl | rfl <;> rcases mem_coords.1 ht with rfl | rfl <;>
        simp [stdBlock, blockMat, hpq.symm]
    · rw [hoff u t hu ht, ha, mat_longBlock, blockMat_apply_of_not_mem k _ (fun h => hu h.1)]
      exact (Matrix.one_apply_ne (fun e => hu (by rw [e]; exact ht))).symm
  refine ⟨B, hBC, a⁻¹ * x, ?_, (mul_inv_cancel_left a x).symm⟩
  rw [complSp, mem_suppGroup_iff (parClosed_coords k).compl]
  intro t ht r
  have ht' : t ∈ coords k := by simpa using ht
  rw [map_mul, Matrix.mul_apply, Finset.sum_congr rfl (fun u _ => by rw [hcol u t ht']),
    ← Matrix.mul_apply, ← map_mul, inv_mul_cancel, map_one]

theorem commutator_mem_complSp_of_commute_nsElt [CharP K 2] {g g' : StatedSp n K}
    (hg : g * nsElt k = nsElt k * g) (hg' : g' * nsElt k = nsElt k * g') :
    g * g' * g⁻¹ * g'⁻¹ ∈ complSp K k := by
  set A : Subgroup (StatedSp n K) :=
    (centralizer ({zThreeSL} : Set SL(2, K))).map (longBlock K n k) with hA
  have hAmem : ∀ B : SL(2, K), B * zThreeSL = zThreeSL * B → longBlock K n k B ∈ A :=
    fun B hB => ⟨B, mem_centralizer_singleton_iff.2 hB, rfl⟩
  refine commutator_mem_of_eq_mul (A := A) ?_ ?_ ?_ ?_
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨B', hB', rfl⟩
    change longBlock K n k B * longBlock K n k B' = longBlock K n k B' * longBlock K n k B
    rw [← map_mul, ← map_mul, commute_of_commute_zThreeSL (mem_centralizer_singleton_iff.1 hB)
      (mem_centralizer_singleton_iff.1 hB')]
  · rintro _ ⟨B, -, rfl⟩ d hd
    exact mem_centralizer_iff.1 (complSp_le_centralizer_longRootSp2 k hd) _ ⟨B, rfl⟩
  · obtain ⟨B, hB, y, hy, rfl⟩ := exists_eq_mul_of_commute_nsElt_of_charTwo hg
    exact ⟨_, hAmem B hB, y, hy, rfl⟩
  · obtain ⟨B, hB, y, hy, rfl⟩ := exists_eq_mul_of_commute_nsElt_of_charTwo hg'
    exact ⟨_, hAmem B hB, y, hy, rfl⟩

theorem mem_centralizer_nsElt_of_mem_complSp {l : Fin n} {y : StatedSp n K}
    (hy : y ∈ complSp K l) : y ∈ centralizer ({nsElt l} : Set (StatedSp n K)) :=
  mem_centralizer_singleton_iff.2
    ((mem_centralizer_iff.1 (complSp_le_centralizer_nsTorusSp l hy) _ (nsElt_mem_nsTorusSp l)).symm)

theorem perfectCore_spBlock_compl_inf_centralizer_nsElt [Finite K] [CharP K 2] (k l : Fin n)
    (hperf : ⁅spBlock K ({k, l}ᶜ : Finset (Fin n)), spBlock K ({k, l}ᶜ : Finset (Fin n))⁆ =
      spBlock K ({k, l}ᶜ : Finset (Fin n))) :
    perfectCore (spBlock K ({k}ᶜ : Finset (Fin n)) ⊓
        centralizer ({nsElt l} : Set (StatedSp n K))) =
      spBlock K ({k, l}ᶜ : Finset (Fin n)) := by
  set H := spBlock K ({k}ᶜ : Finset (Fin n)) ⊓ centralizer ({nsElt l} : Set (StatedSp n K))
    with hH
  have hcomm : ⁅H, H⁆ ≤ spBlock K ({k, l}ᶜ : Finset (Fin n)) := by
    rw [← complSp_inf_complSp, ← spBlock_compl_singleton]
    refine commutator_le.2 fun g hg g' hg' => mem_inf.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg.1 hg'.1) (inv_mem hg.1)) (inv_mem hg'.1)
    · rw [commutatorElement_def]
      exact commutator_mem_complSp_of_commute_nsElt (mem_centralizer_singleton_iff.1 hg.2)
        (mem_centralizer_singleton_iff.1 hg'.2)
  have hle : spBlock K ({k, l}ᶜ : Finset (Fin n)) ≤ H := by
    rw [← complSp_inf_complSp, ← spBlock_compl_singleton]
    exact inf_le_inf_left _ fun y hy => mem_centralizer_nsElt_of_mem_complSp hy
  apply le_antisymm
  · calc perfectCore H = ⁅perfectCore H, perfectCore H⁆ := (perfectCore_perfect H).symm
      _ ≤ ⁅H, H⁆ := commutator_mono (perfectCore_le H) (perfectCore_le H)
      _ ≤ _ := hcomm
  · exact le_perfectCore_of_perfect hle hperf

end Centralizer

section FieldMap

variable {F : Type} [Field F]

theorem spFieldMap_nsElt (ι : K →+* F) (k : Fin n) :
    spFieldMap n ι (nsElt k) = nsElt (K := F) k := by
  apply mat_injective
  rw [mat_spFieldMap, mat_nsElt, mat_nsElt]
  ext a b
  simp only [blockMat, Matrix.map_apply, of_apply]
  split_ifs <;> simp [zThreeMat, Matrix.one_apply, *]

end FieldMap

end CFSG.SeitzReduction.SymplecticPilot
