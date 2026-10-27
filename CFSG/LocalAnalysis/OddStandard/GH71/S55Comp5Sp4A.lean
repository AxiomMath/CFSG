module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Gen
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K]

namespace C5

theorem coords_compl : (coords (0 : Fin 2) : Set (Fin 2 ⊕ Fin 2))ᶜ = coords 1 := by
  ext a
  rw [Set.mem_compl_iff, mem_coords, mem_coords]
  rcases a with a | a <;> fin_cases a <;> simp

theorem longBlock_mem_supp0 (A : SL(2, K)) : longBlock K 2 0 A ∈ suppGroup (coords 0) := by
  rw [← longRootSp2_eq_suppGroup]
  exact ⟨A, rfl⟩

theorem longBlock_mem_supp1 (B : SL(2, K)) :
    longBlock K 2 1 B ∈ suppGroup (coords (0 : Fin 2))ᶜ := by
  rw [coords_compl, ← longRootSp2_eq_suppGroup]
  exact ⟨B, rfl⟩

theorem commute_longBlock (A B : SL(2, K)) :
    Commute (longBlock K 2 0 A) (longBlock K 2 1 B) :=
  commute_suppGroup_compl (longBlock_mem_supp0 A) (longBlock_mem_supp1 B)

@[expose] noncomputable def blockPair : SL(2, K) × SL(2, K) →* StatedSp 2 K :=
  MonoidHom.noncommCoprod (longBlock K 2 0) (longBlock K 2 1) commute_longBlock

theorem blockPair_apply (A B : SL(2, K)) :
    blockPair (A, B) = longBlock K 2 0 A * longBlock K 2 1 B := rfl

theorem blockPair_injective : Function.Injective (blockPair (K := K)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, B⟩ h
  rw [blockPair_apply] at h
  have h1 : longBlock K 2 0 A = (longBlock K 2 1 B)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hA' : longBlock K 2 0 A ∈ suppGroup (coords (0 : Fin 2))ᶜ := by
    rw [h1]
    exact inv_mem (longBlock_mem_supp1 B)
  have hA1 := Subgroup.disjoint_def.mp (disjoint_suppGroup_compl (K := K) (coords (0 : Fin 2)))
    (longBlock_mem_supp0 A) hA'
  have hA : A = 1 := longBlock_injective (K := K) (n := 2) 0 (by rw [hA1, map_one])
  rw [hA1, one_mul] at h
  have hB : B = 1 := longBlock_injective (K := K) (n := 2) 1 (by rw [h, map_one])
  rw [hA, hB]
  rfl

end C5

open C5

theorem index_range_blockPair [Finite K] :
    (blockPair (K := K)).range.index = Nat.card K ^ 2 * (Nat.card K ^ 2 + 1) := by
  have h1 := Subgroup.card_mul_index (blockPair (K := K)).range
  rw [← Nat.card_congr (MonoidHom.ofInjective blockPair_injective).toEquiv, Nat.card_prod,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 2,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)] at h1
  set q := Nat.card K
  have hq : 1 < q := Finite.one_lt_card
  have p1 : ∏ j ∈ Finset.Icc 1 2, (q ^ (2 * j) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) := by
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  have p2 : ∏ j ∈ Finset.Icc 2 2, (q ^ j - 1) = q ^ 2 - 1 := by
    rw [Finset.Icc_self, Finset.prod_singleton]
  rw [p1, p2] at h1
  norm_num at h1
  have e4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    zify [Nat.one_le_pow 4 q (by omega), Nat.one_le_pow 2 q (by omega)]
    ring
  rw [e4] at h1
  have hA : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero hq)
  generalize q ^ 2 - 1 = A at h1 hA
  refine Nat.eq_of_mul_eq_mul_left (n := q ^ 2 * A ^ 2) (by positivity) ?_
  calc q ^ 2 * A ^ 2 * (blockPair (K := K)).range.index =
      q * A * (q * A) * (blockPair (K := K)).range.index := by ring
    _ = q ^ 4 * (A * (A * (q ^ 2 + 1))) := h1
    _ = q ^ 2 * A ^ 2 * (q ^ 2 * (q ^ 2 + 1)) := by ring

theorem range_blockPair_le_normalizer [Finite K] :
    (blockPair (K := K)).range ≤ normalizer (longRootSp2 K 2 0 : Set (StatedSp 2 K)) := by
  have : Fintype K := Fintype.ofFinite K
  rintro _ ⟨⟨A, B⟩, rfl⟩
  apply mem_normalizer_of_conj_mem
  rintro _ ⟨C, rfl⟩
  rw [blockPair_apply]
  refine ⟨A * C * A⁻¹, ?_⟩
  have hc := (commute_longBlock C B).eq
  rw [map_mul, map_mul, map_inv]
  calc longBlock K 2 0 A * longBlock K 2 0 C * (longBlock K 2 0 A)⁻¹ =
      longBlock K 2 0 A * (longBlock K 2 0 C * longBlock K 2 1 B * (longBlock K 2 1 B)⁻¹) *
        (longBlock K 2 0 A)⁻¹ := by group
    _ = _ := by rw [hc]; group

theorem projSp_longBlock_injective :
    Function.Injective
      ((CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K).comp (longBlock K 2 0)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj, Subgroup.mem_subgroupOf] at hA
  obtain ⟨c, hc⟩ := hA
  have hs := isSupp_longBlock (K := K) (n := 2) 0 A (Sum.inl 1) (Sum.inl 1)
    (by simp [mem_coords])
  rw [mat_apply, ← hc, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
    one_apply_eq] at hs
  have hc1 : c = 1 := Units.ext hs
  apply longBlock_injective (K := K) (n := 2) 0
  apply mat_injective
  rw [mat_apply, ← hc, hc1, map_one, map_one, map_one]
  rfl

end CFSG.OddStandard.GH71.S55
