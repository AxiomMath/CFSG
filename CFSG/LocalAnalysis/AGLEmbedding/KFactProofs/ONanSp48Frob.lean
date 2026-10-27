module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Typ

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups Matrix

@[expose] noncomputable def frSL : Sl28 →* Sl28 :=
  Matrix.SpecialLinearGroup.map frobE.toRingHom

theorem coe_frSL (x : Sl28) :
    ((frSL x : Sl28) : Matrix (Fin 2) (Fin 2) GF8) =
      (x : Matrix (Fin 2) (Fin 2) GF8).map frobE := rfl

theorem fr_blk0 (x : Sl28) : fr (blk0 x) = blk0 (frSL x) := by
  apply mat_injective
  show matOf (fr (blk0 x)) = _
  rw [matOf_fr]
  show sqM (mat 2 GF8 (blk0 x)) = _
  rw [mat_longBlock, mat_longBlock]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [sqM, blockMat, coe_frSL, frobE_apply]

theorem fr_blk1 (x : Sl28) : fr (blk1 x) = blk1 (frSL x) := by
  apply mat_injective
  show matOf (fr (blk1 x)) = _
  rw [matOf_fr]
  show sqM (mat 2 GF8 (blk1 x)) = _
  rw [mat_longBlock, mat_longBlock]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [sqM, blockMat, coe_frSL, frobE_apply]

theorem fr_swp : fr swp = swp := by
  apply matOf_injective
  rw [matOf_fr]
  show sqM (decode sc.m) = decode sc.m
  decide +kernel

theorem fr_blk (x y : Sl28) : fr (blk0 x * blk1 y) = blk0 (frSL x) * blk1 (frSL y) := by
  rw [map_mul, fr_blk0, fr_blk1]

theorem frSL_slA : frSL slA = slA ^ 7 := by
  apply Subtype.ext
  rw [coe_frSL, Matrix.SpecialLinearGroup.coe_pow]
  have h7 := slA_pow_val ⟨7, by norm_num⟩
  rw [h7]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobE_apply, slAPow, slA, mk28] <;> decide

theorem frSL_slW : frSL slW = slW := by
  apply Subtype.ext
  rw [coe_frSL]
  decide +kernel

theorem frSL_of_mem_slT {x : Sl28} (hx : x ∈ slT) : frSL x = x ^ 7 := by
  obtain ⟨k, rfl⟩ := (mem_slT_iff x).1 hx
  rw [map_pow, frSL_slA, ← pow_mul, ← pow_mul, mul_comm]

theorem fr_of_mem_spT0 {t : Sp8} (ht : t ∈ spT0) : fr t = t ^ 7 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_spT0_iff t).1 ht
  rw [fr_blk, frSL_of_mem_slT hx, frSL_of_mem_slT hy]
  have : blkHom (x ^ 7, y ^ 7) = blkHom (x, y) ^ 7 := by rw [← map_pow, Prod.pow_mk]
  exact this

theorem fr_mem_spT0 {t : Sp8} (ht : t ∈ spT0) : fr t ∈ spT0 := by
  rw [fr_of_mem_spT0 ht]
  exact spT0.pow_mem ht 7

theorem fr_pow_mem_spT0 (n : ℕ) {t : Sp8} (ht : t ∈ spT0) : (fr ^ n) t ∈ spT0 := by
  induction n with
  | zero => simpa using ht
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact fr_mem_spT0 ih

theorem fr_eq_self_iff {t : Sp8} (ht : t ∈ spT0) : fr t = t ↔ t ^ 3 = 1 := by
  have h9 := exp_spT0 t ht
  rw [fr_of_mem_spT0 ht]
  constructor
  · intro h
    have h6 : t ^ 6 = 1 := by
      calc t ^ 6 = t ^ 7 * t⁻¹ := by group
        _ = 1 := by rw [h]; group
    calc t ^ 3 = t ^ 9 * (t ^ 6)⁻¹ := by group
      _ = 1 := by rw [h9, h6]; group
  · intro h
    calc t ^ 7 = t ^ 3 * t ^ 3 * t := by group
      _ = t := by rw [h]; group

@[expose] noncomputable def spE : Subgroup Sp8 :=
  ((Subgroup.zpowers slZ).prod (Subgroup.zpowers slZ)).map blkHom

theorem card_spE : Nat.card spE = 9 := by
  rw [spE, Subgroup.card_map_of_injective blkHom_injective,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Nat.card_zpowers]
  have : orderOf slZ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime slZ_pow3 slZ_ne_one
  rw [this]

theorem mem_spE_iff (g : Sp8) : g ∈ spE ↔ ∃ x ∈ Subgroup.zpowers slZ, ∃ y ∈ Subgroup.zpowers slZ,
    g = blk0 x * blk1 y := by
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩

theorem spE_le_spT0 : spE ≤ spT0 := by
  intro g hg
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_spE_iff g).1 hg
  have hz : ∀ u ∈ Subgroup.zpowers slZ, u ∈ slT := fun u hu =>
    Subgroup.zpowers_le.2 slZ_mem_slT hu
  exact (mem_spT0_iff _).2 ⟨x, hz x hx, y, hz y hy, rfl⟩

theorem mem_spE_iff_cube (g : Sp8) : g ∈ spE ↔ g ∈ spT0 ∧ g ^ 3 = 1 := by
  constructor
  · intro hg
    refine ⟨spE_le_spT0 hg, ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_spE_iff g).1 hg
    have h3 : ∀ u ∈ Subgroup.zpowers slZ, u ^ 3 = 1 := by
      intro u hu
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, slZ_pow3, one_zpow]
    have : (blk0 x * blk1 y) ^ 3 = blkHom (x, y) ^ 3 := rfl
    rw [this, ← map_pow, Prod.pow_mk, h3 x hx, h3 y hy]
    exact map_one blkHom
  · rintro ⟨hg, hg3⟩
    obtain ⟨x, y, hx, hy, rfl⟩ := spT0_cube hg hg3
    have hz : ∀ u : Sl28, (u = 1 ∨ u = slZ ∨ u = slZ⁻¹) → u ∈ Subgroup.zpowers slZ := by
      rintro u (rfl | rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
      · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    exact (mem_spE_iff _).2 ⟨x, hz x hx, y, hz y hy, rfl⟩

theorem fr_eq_self_iff_mem_spE {t : Sp8} (ht : t ∈ spT0) : fr t = t ↔ t ∈ spE := by
  rw [fr_eq_self_iff ht, mem_spE_iff_cube]
  exact ⟨fun h => ⟨ht, h⟩, fun h => h.2⟩

theorem fr_pow_ne {j : ℕ} (hj : j = 1 ∨ j = 2) {t : Sp8} (ht : t ∈ spT0) (h3 : t ^ 3 ≠ 1) :
    (fr ^ j) t ≠ t := by
  rcases hj with rfl | rfl
  · intro h
    exact h3 ((fr_eq_self_iff ht).1 (by simpa using h))
  · intro h
    have h1 : (fr ^ 2) t = t ^ 49 := by
      rw [pow_two, MulAut.mul_apply, fr_of_mem_spT0 ht, map_pow, fr_of_mem_spT0 ht, ← pow_mul]
    rw [h1] at h
    apply h3
    have h9 := exp_spT0 t ht
    have h48 : t ^ 48 = 1 := by
      calc t ^ 48 = t ^ 49 * t⁻¹ := by group
        _ = 1 := by rw [h]; group
    have h45 : t ^ 48 = (t ^ 9) ^ 5 * t ^ 3 := by rw [← pow_mul, ← pow_add]
    rw [h9, one_pow, one_mul] at h45
    rw [← h45]
    exact h48

theorem slD_frSL {x : Sl28} (hx : x ∈ slD) : x⁻¹ * frSL x ∈ slT := by
  rcases (mem_slD_iff x).1 hx with h | ⟨t, ht, rfl⟩
  · rw [frSL_of_mem_slT h]
    have : x⁻¹ * x ^ 7 = x ^ 6 := by group
    rw [this]
    exact slT.pow_mem h 6
  · rw [map_mul, frSL_of_mem_slT ht, frSL_slW]
    have hw : slW ∈ slD := slW_mem_slD
    have h1 : slW⁻¹ * t ^ 6 * slW ∈ slT := by
      have := (Subgroup.mem_normalizer_iff.1 (slD.inv_mem hw) (t ^ 6)).1 (slT.pow_mem ht 6)
      simpa using this
    have : (t * slW)⁻¹ * (t ^ 7 * slW) = slW⁻¹ * t ^ 6 * slW := by group
    rw [this]
    exact h1

theorem fr_normalizer {n : Sp8} (hn : n ∈ wrp slD) : n⁻¹ * fr n ∈ spT0 := by
  obtain ⟨x, hx, y, hy, rfl | rfl⟩ := hn
  · rw [fr_blk, blk_inv, blk_mul]
    exact (mem_spT0_iff _).2 ⟨_, slD_frSL hx, _, slD_frSL hy, rfl⟩
  · have hsw : swp ∈ Subgroup.normalizer (spT0 : Set Sp8) := wrp_eq_normalizer ▸ swp_mem_wrp slD
    have h1 : (blk0 x * blk1 y * swp)⁻¹ * fr (blk0 x * blk1 y * swp) =
        swp⁻¹ * ((blk0 x⁻¹ * blk1 y⁻¹) * (blk0 (frSL x) * blk1 (frSL y))) * swp := by
      rw [map_mul, fr_swp, fr_blk, mul_inv_rev, blk_inv]
      group
    rw [h1, blk_mul]
    have hu : blk0 (x⁻¹ * frSL x) * blk1 (y⁻¹ * frSL y) ∈ spT0 :=
      (mem_spT0_iff _).2 ⟨_, slD_frSL hx, _, slD_frSL hy, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hsw) _).1 hu
    simpa using this

end CFSG.AGLEmbedding.KFactProofs.Sp48
