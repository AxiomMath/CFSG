module

public import CFSG.CGT.Stroth77.Extension221
public import CFSG.CGT.Stroth77.Extension210Final
public import CFSG.CGT.Stroth77.Extension211Final

public section

namespace CFSG.CGT.Stroth77

section NotCyclic

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S}

theorem not_isCyclic_quotient_of_sq_mem_Idx4R [hN : (B.subgroupOf C).Normal] (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hexp : ∀ x ∈ C, x * x ∈ B) : ¬ IsCyclic (C ⧸ B.subgroupOf C) := by
  intro hcyc
  obtain ⟨q₀, hq₀⟩ := hcyc.exists_generator
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf C) q₀
  have hcard : Nat.card (C ⧸ B.subgroupOf C) = 4 := card_quotient_four hBC hC hrel
  have hgen : Subgroup.zpowers (QuotientGroup.mk' (B.subgroupOf C) z) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact hq₀ y
  have horder : orderOf (QuotientGroup.mk' (B.subgroupOf C) z) = 4 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hgen, hcard]
  have hsq : QuotientGroup.mk' (B.subgroupOf C) z ^ 2 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      sq]
    exact hexp _ z.2
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [horder] at hdvd
  norm_num at hdvd

end NotCyclic

section Coordinates

variable {m : ℕ} (hm : 2 ≤ m)

theorem rho_apply_gens_t210 (i j l : ℤ) :
    (StrothTypeIndex.t210 m hm).action.φρ
        (i • gen (StrothTypeIndex.t210 m hm).k 0 + j • gen (StrothTypeIndex.t210 m hm).k 1 +
          l • gen (StrothTypeIndex.t210 m hm).k 2) =
      (i - l) • gen (StrothTypeIndex.t210 m hm).k 0 +
        (-l) • gen (StrothTypeIndex.t210 m hm).k 1 +
          (j - l) • gen (StrothTypeIndex.t210 m hm).k 2 := by
  rw [matAct_zsmul_gens]
  simp [StrothTypeIndex.action, Type210.action, SigmaFourAction.ofMatEq, Type210.ρM, ofCols_apply,
    sub_eq_add_neg]

theorem rho_apply_gens_t211 (i j l : ℤ) :
    (StrothTypeIndex.t211 m hm).action.φρ
        (i • gen (StrothTypeIndex.t211 m hm).k 0 + j • gen (StrothTypeIndex.t211 m hm).k 1 +
          l • gen (StrothTypeIndex.t211 m hm).k 2) =
      (i - l) • gen (StrothTypeIndex.t211 m hm).k 0 +
        (-l) • gen (StrothTypeIndex.t211 m hm).k 1 +
          (j - l) • gen (StrothTypeIndex.t211 m hm).k 2 := by
  rw [matAct_zsmul_gens]
  simp [StrothTypeIndex.action, Type211.action, SigmaFourAction.ofMatEq, Type211.ρM, ofCols_apply,
    sub_eq_add_neg]

theorem t_apply_gens_t210 (i j l : ℤ) :
    (StrothTypeIndex.t210 m hm).action.φt
        (i • gen (StrothTypeIndex.t210 m hm).k 0 + j • gen (StrothTypeIndex.t210 m hm).k 1 +
          l • gen (StrothTypeIndex.t210 m hm).k 2) =
      (i + 2 * 2 ^ (m - 2) * j + (6 * 2 ^ (m - 2) - 1) * l) •
          gen (StrothTypeIndex.t210 m hm).k 0 +
        (4 * i + (-1 - 4 * 2 ^ (m - 2)) * j + (4 * 2 ^ (m - 2) - 2) * l) •
          gen (StrothTypeIndex.t210 m hm).k 1 +
        (8 * 2 ^ (m - 2) * i + 8 * 2 ^ (m - 2) * j + (12 * 2 ^ (m - 2) - 1) * l) •
          gen (StrothTypeIndex.t210 m hm).k 2 := by
  rw [matAct_zsmul_gens]
  simp only [StrothTypeIndex.action, Type210.action, SigmaFourAction.ofMatEq, Type210.tM,
    Type210.uvA, Type210.ρM, ofCols_apply]
  congr 2
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff] <;> ring
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff] <;> ring
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff] <;> ring

theorem t_apply_gens_t211 (i j l : ℤ) :
    (StrothTypeIndex.t211 m hm).action.φt
        (i • gen (StrothTypeIndex.t211 m hm).k 0 + j • gen (StrothTypeIndex.t211 m hm).k 1 +
          l • gen (StrothTypeIndex.t211 m hm).k 2) =
      (i + 2 * 2 ^ (m - 2) * j + (-2 * 2 ^ (m - 2) - 1) * l) •
          gen (StrothTypeIndex.t211 m hm).k 0 +
        (4 * i + (-1 + 4 * 2 ^ (m - 2)) * j + (-4 * 2 ^ (m - 2) - 2) * l) •
          gen (StrothTypeIndex.t211 m hm).k 1 +
        (8 * 2 ^ (m - 2) * i + 8 * 2 ^ (m - 2) * j + (4 * 2 ^ (m - 2) - 1) * l) •
          gen (StrothTypeIndex.t211 m hm).k 2 := by
  rw [matAct_zsmul_gens]
  simp only [StrothTypeIndex.action, Type211.action, SigmaFourAction.ofMatEq, Type211.tM,
    Type211.uvA, Type211.ρM, ofCols_apply]
  congr 2
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff] <;> ring
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff] <;> ring
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff] <;> ring

theorem parityTorus_rho_t210 (y : Torus (StrothTypeIndex.t210 m hm).k) :
    parityTorus _ (hk_t210 m hm) ((StrothTypeIndex.t210 m hm).action.φρ y) =
      rhoBar230 (parityTorus _ (hk_t210 m hm) y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [rho_apply_gens_t210, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  funext r
  fin_cases r
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parityTorus_rho_t211 (y : Torus (StrothTypeIndex.t211 m hm).k) :
    parityTorus _ (hk_t211 m hm) ((StrothTypeIndex.t211 m hm).action.φρ y) =
      rhoBar230 (parityTorus _ (hk_t211 m hm) y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [rho_apply_gens_t211, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  funext r
  fin_cases r
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parityTorus_t_t210 (y : Torus (StrothTypeIndex.t210 m hm).k) :
    parityTorus _ (hk_t210 m hm) ((StrothTypeIndex.t210 m hm).action.φt y) =
      tBar230 (parityTorus _ (hk_t210 m hm) y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [t_apply_gens_t210, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h6 : (6 : ZMod 2) = 0 := by decide
  have h8 : (8 : ZMod 2) = 0 := by decide
  have h12 : (12 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r
  · simp [tBar230, h2, h4, h6, h8, h12, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, h2, h4, h6, h8, h12, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, h2, h4, h6, h8, h12, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parityTorus_t_t211 (y : Torus (StrothTypeIndex.t211 m hm).k) :
    parityTorus _ (hk_t211 m hm) ((StrothTypeIndex.t211 m hm).action.φt y) =
      tBar230 (parityTorus _ (hk_t211 m hm) y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [t_apply_gens_t211, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h8 : (8 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r
  · simp [tBar230, h2, h4, h8, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, h2, h4, h8, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, h2, h4, h8, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

end Coordinates

section Fixed

variable {S : Type*} [Group S] [Finite S] {B : Subgroup S} {m : ℕ} {hm : 2 ≤ m}

theorem fixed_rho_t_t210 (D : StrothTypeData B (StrothTypeIndex.t210 m hm)) {y : B}
    (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t210 m hm).action.φρ (D.ec y) = D.ec y := by
    have h := D.ρ_conj y
    change D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t210 m hm).action.φρ (D.ec y) at h
    rw [← h, hρ]
  have ht' : (StrothTypeIndex.t210 m hm).action.φt (D.ec y) = D.ec y := by
    have h := D.t_conj y
    change D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t210 m hm).action.φt (D.ec y) at h
    rw [← h, ht]
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens _ (D.ec y)
  rw [hy, rho_apply_gens_t210] at hρ'
  rw [hy, t_apply_gens_t210] at ht'
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hρ'
  obtain ⟨-, ht1, -⟩ := zsmul_gens_dvd_of_eq ht'
  change (2 : ℤ) ^ (m + 2) ∣ _ at hρ1 hρ2 ht1
  have h3 : IsCoprime ((2 : ℤ) ^ (m + 2)) 3 :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
  have hl : (2 : ℤ) ^ (m + 2) ∣ l := by
    refine h3.dvd_of_dvd_mul_left ?_
    have := dvd_add hρ1 hρ2
    convert this using 1
    ring
  have hj : (2 : ℤ) ^ (m + 2) ∣ j := by
    have := dvd_sub hρ1 hl
    convert this using 1
    ring
  have h4i : (2 : ℤ) ^ (m + 2) ∣ 4 * i := by
    have := dvd_sub (dvd_sub (dvd_mul_of_dvd_right hj (1 - (-1 - 4 * 2 ^ (m - 2))))
      (dvd_mul_of_dvd_right hl (4 * 2 ^ (m - 2) - 2))) ht1
    convert this using 1
    ring
  have hi : (2 : ℤ) ^ m ∣ i := by
    have h16 : (2 : ℤ) ^ (m + 2) = 4 * 2 ^ m := by ring
    rw [h16] at h4i
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4i
  apply D.ec_eq_zero_iff.mp
  rw [hy]
  have h0 := zsmul_gens_eq_of_dvd (k := (StrothTypeIndex.t210 m hm).k) (p := i) (q := j) (r := l)
    (p' := 0) (q' := 0) (r' := 0)
    (by change (2 : ℤ) ^ m ∣ 0 - i; rw [zero_sub, dvd_neg]; exact hi)
    (by change (2 : ℤ) ^ (m + 2) ∣ 0 - j; rw [zero_sub, dvd_neg]; exact hj)
    (by change (2 : ℤ) ^ (m + 2) ∣ 0 - l; rw [zero_sub, dvd_neg]; exact hl)
  rw [h0]
  simp

theorem fixed_rho_t_t211 (D : StrothTypeData B (StrothTypeIndex.t211 m hm)) {y : B}
    (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t211 m hm).action.φρ (D.ec y) = D.ec y := by
    have h := D.ρ_conj y
    change D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t211 m hm).action.φρ (D.ec y) at h
    rw [← h, hρ]
  have ht' : (StrothTypeIndex.t211 m hm).action.φt (D.ec y) = D.ec y := by
    have h := D.t_conj y
    change D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t211 m hm).action.φt (D.ec y) at h
    rw [← h, ht]
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens _ (D.ec y)
  rw [hy, rho_apply_gens_t211] at hρ'
  rw [hy, t_apply_gens_t211] at ht'
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hρ'
  obtain ⟨-, ht1, -⟩ := zsmul_gens_dvd_of_eq ht'
  change (2 : ℤ) ^ (m + 2) ∣ _ at hρ1 hρ2 ht1
  have h3 : IsCoprime ((2 : ℤ) ^ (m + 2)) 3 :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
  have hl : (2 : ℤ) ^ (m + 2) ∣ l := by
    refine h3.dvd_of_dvd_mul_left ?_
    have := dvd_add hρ1 hρ2
    convert this using 1
    ring
  have hj : (2 : ℤ) ^ (m + 2) ∣ j := by
    have := dvd_sub hρ1 hl
    convert this using 1
    ring
  have h4i : (2 : ℤ) ^ (m + 2) ∣ 4 * i := by
    have := dvd_sub (dvd_sub (dvd_mul_of_dvd_right hj (1 - (-1 + 4 * 2 ^ (m - 2))))
      (dvd_mul_of_dvd_right hl (-4 * 2 ^ (m - 2) - 2))) ht1
    convert this using 1
    ring
  have hi : (2 : ℤ) ^ m ∣ i := by
    have h16 : (2 : ℤ) ^ (m + 2) = 4 * 2 ^ m := by ring
    rw [h16] at h4i
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4i
  apply D.ec_eq_zero_iff.mp
  rw [hy]
  have h0 := zsmul_gens_eq_of_dvd (k := (StrothTypeIndex.t211 m hm).k) (p := i) (q := j) (r := l)
    (p' := 0) (q' := 0) (r' := 0)
    (by change (2 : ℤ) ^ m ∣ 0 - i; rw [zero_sub, dvd_neg]; exact hi)
    (by change (2 : ℤ) ^ (m + 2) ∣ 0 - j; rw [zero_sub, dvd_neg]; exact hj)
    (by change (2 : ℤ) ^ (m + 2) ∣ 0 - l; rw [zero_sub, dvd_neg]; exact hl)
  rw [h0]
  simp

end Fixed

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem false_of_index_four_t210_of_data {m : ℕ} {hm : 2 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t210 m hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B) (hexp : ∀ x ∈ C, x * x ∈ B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  exact false_of_index_four_of_planes_t230 D (hk_t210 m hm) (parityTorus_rho_t210 hm)
    (parityTorus_t_t210 hm) (fun _ hρ ht => fixed_rho_t_t210 D hρ ht) hBC hC hrel hL hH
    hcS (not_isCyclic_quotient_of_sq_mem_Idx4R hBC hC hrel hexp)

theorem false_of_index_four_t210 {m : ℕ} {hm : 2 ≤ m}
    (hB : HasStrothType B (StrothTypeIndex.t210 m hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B) (hexp : ∀ x ∈ C, x * x ∈ B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_four_t210_of_data hB.data hBC hC hrel hexp hL hH hcS

theorem false_of_index_four_t211_of_data {m : ℕ} {hm : 2 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t211 m hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B) (hexp : ∀ x ∈ C, x * x ∈ B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  exact false_of_index_four_of_planes_t230 D (hk_t211 m hm) (parityTorus_rho_t211 hm)
    (parityTorus_t_t211 hm) (fun _ hρ ht => fixed_rho_t_t211 D hρ ht) hBC hC hrel hL hH
    hcS (not_isCyclic_quotient_of_sq_mem_Idx4R hBC hC hrel hexp)

theorem false_of_index_four_t211 {m : ℕ} {hm : 2 ≤ m}
    (hB : HasStrothType B (StrothTypeIndex.t211 m hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B) (hexp : ∀ x ∈ C, x * x ∈ B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_four_t211_of_data hB.data hBC hC hrel hexp hL hH hcS

end CFSG.CGT.Stroth77
