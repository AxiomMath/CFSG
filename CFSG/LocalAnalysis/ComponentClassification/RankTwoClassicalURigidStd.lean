module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidModule

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

section Spaces

variable {K : Type} [Field K] {ε : ℕ}

variable (K ε) in
@[expose] def V01 : Submodule K (Fin ε → K) where
  carrier := {v | ∀ j : Fin ε, 2 ≤ (j : ℕ) → v j = 0}
  add_mem' hv hw j hj := by
    simp only [Set.mem_ofPred_eq] at hv hw
    simp [hv j hj, hw j hj]
  zero_mem' _ _ := rfl
  smul_mem' c v hv j hj := by
    simp only [Set.mem_ofPred_eq] at hv
    simp [hv j hj]

variable (K ε) in
@[expose] def V2 : Submodule K (Fin ε → K) where
  carrier := {v | ∀ j : Fin ε, (j : ℕ) < 2 → v j = 0}
  add_mem' hv hw j hj := by
    simp only [Set.mem_ofPred_eq] at hv hw
    simp [hv j hj, hw j hj]
  zero_mem' _ _ := rfl
  smul_mem' c v hv j hj := by
    simp only [Set.mem_ofPred_eq] at hv
    simp [hv j hj]

theorem mem_V2 {v : Fin ε → K} : v ∈ V2 K ε ↔ ∀ j : Fin ε, (j : ℕ) < 2 → v j = 0 := Iff.rfl

theorem V01_inf_V2 : V01 K ε ⊓ V2 K ε = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨h1, h2⟩
  rw [Submodule.mem_bot]
  funext j
  by_cases hj : (j : ℕ) < 2
  · exact h2 j hj
  · exact h1 j (by omega)

theorem V01_sup_V2 : V01 K ε ⊔ V2 K ε = ⊤ := by
  rw [eq_top_iff]
  intro v _
  set w : Fin ε → K := fun j => if (j : ℕ) < 2 then v j else 0
  have hw : w ∈ V01 K ε := fun j hj => by
    show (if (j : ℕ) < 2 then v j else 0) = 0
    exact ite_eq_right (by omega)
  have hvw : v - w ∈ V2 K ε := fun j hj => by
    show v j - (if (j : ℕ) < 2 then v j else 0) = 0
    rw [ite_eq_left hj, sub_self]
  have := Submodule.add_mem_sup hw hvw
  rwa [add_sub_cancel] at this

theorem finrank_V2 (hε : 2 ≤ ε) : Module.finrank K (V2 K ε) = ε - 2 := by
  set φ := LinearMap.funLeft K K (Fin.castLE hε : Fin 2 → Fin ε)
  have hker : LinearMap.ker φ = V2 K ε := by
    ext v
    rw [LinearMap.mem_ker, mem_V2]
    constructor
    · intro hv j hj
      have := congrFun hv ⟨j, hj⟩
      simpa [φ, LinearMap.funLeft] using this
    · intro hv
      funext i
      simpa [φ, LinearMap.funLeft] using
        hv (Fin.castLE hε i) (by rw [Fin.val_castLE]; exact i.2)
  have hrange : LinearMap.range φ = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.funLeft_surjective_of_injective _ _ _
      (Fin.castLE_injective hε))
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, finrank_top, hker, Module.finrank_fin_fun, Module.finrank_fin_fun] at h1
  omega

theorem finrank_V01 (hε : 2 ≤ ε) : Module.finrank K (V01 K ε) = 2 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (V01 K ε) (V2 K ε)
  rw [V01_sup_V2, V01_inf_V2, finrank_bot, add_zero, finrank_top, Module.finrank_fin_fun,
    finrank_V2 hε] at h1
  omega

end Spaces

section StdW

variable {K : Type} [Field K] [CharP K 2] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

omit [CharP K 2] in
include h in
theorem mulVec_apply_of_fix {n : ℕ} (C : StatedSU n (2 ^ f) K) {y : Fin n}
    (hC : (C : GL (Fin n) K).val *ᵥ Pi.single y 1 = Pi.single y 1) (v : Fin n → K) :
    ((C : GL (Fin n) K).val *ᵥ v) y = v y := by
  rw [← hform_single_one_left (σ := h.bar) y ((C : GL (Fin n) K).val *ᵥ v), ← hC,
    hform_mulVec_mulVec h C, hform_single_one_left]

theorem rmat_mulVec_of_mem_stdW {g : stabE (ε := ε) h} (hg : g ∈ stdW h) {j : Fin ε}
    (hj : 2 ≤ (j : ℕ)) : rmat h g *ᵥ Pi.single j 1 = Pi.single j 1 := by
  have h1 := congrFun (hg.2 j hj)
  ext i
  have h2 := h1 (.inr (.inl i))
  rw [mulVec_single_one, col_apply] at h2 ⊢
  change smat h g (.inr (.inl i)) (.inr (.inl j)) = _
  rw [h2]
  simp [Pi.single_apply]

theorem rmat_mulVec_apply_of_mem_stdW {g : stabE (ε := ε) h} (hg : g ∈ stdW h) {j : Fin ε}
    (hj : 2 ≤ (j : ℕ)) (v : Fin ε → K) : (rmat h g *ᵥ v) j = v j :=
  mulVec_apply_of_fix h (zBlockHom h g) (rmat_mulVec_of_mem_stdW h hg hj) v

theorem rmat_mulVec_of_mem_V2 {g : stabE (ε := ε) h} (hg : g ∈ stdW h) {v : Fin ε → K}
    (hv : v ∈ V2 K ε) : rmat h g *ᵥ v = v := by
  have h1 : rmat h g *ᵥ v = (1 : Matrix (Fin ε) (Fin ε) K) *ᵥ v := by
    ext i
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : (l : ℕ) < 2
    · rw [hv l hl, mul_zero, mul_zero]
    · have h2 := congrFun (rmat_mulVec_of_mem_stdW h hg (j := l) (by omega)) i
      rw [mulVec_single_one, col_apply] at h2
      rw [h2, Pi.single_apply, one_apply]
  rw [h1, one_mulVec]

theorem smat_of_mem_stdW {g : stabE (ε := ε) h} (hg : g ∈ stdW h) :
    smat h g = blkZM (rmat h g) := by
  have h1 := congrFun hg.1
  have ha : avec h g = 0 := by
    funext k
    have := h1 (.inr (.inl k))
    rw [mulVec_single_one, col_apply] at this
    simpa [avec, Pi.single_apply] using this
  have hc : cval h g = 0 := by
    have := h1 hE
    rw [mulVec_single_one, col_apply] at this
    simpa [cval, Pi.single_apply] using this
  obtain ⟨c, hgc⟩ := exists_eq_eichM_avec h g
  have hc' : c = 0 := by
    have h3 := (eichM_mul_blkZM_apply h.bar (avec h g) c (rmat h g)).2.2.1
    rw [← hgc] at h3
    rw [← h3]
    exact hc
  rw [hgc, ha, hc', eichM_zero, Matrix.one_mul]

end StdW

section Diag

variable {K : Type} [Field K] [CharP K 2] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

theorem exists_diag_stabE {d : Fin ε → K} (hd : ∀ i, d i ^ 2 ^ f * d i = 1)
    (hdet : ∏ i, d i = 1) :
    ∃ g : stabE (ε := ε) h, avec h g = 0 ∧ cval h g = 0 ∧ smat h g = blkZM (diagonal d) ∧
      rmat h g = diagonal d ∧ g ^ (2 ^ f + 1) = 1 := by
  obtain ⟨C, hC⟩ := exists_diagonal_mem (f := f) hd hdet
  have hCn : C ^ (2 ^ f + 1) = 1 := by
    refine Subtype.ext (Units.ext ?_)
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hC, diagonal_pow]
    have h1 : d ^ (2 ^ f + 1) = 1 := by
      funext i
      rw [Pi.pow_apply, pow_succ, hd i, Pi.one_apply]
    rw [h1]
    exact diagonal_one
  refine ⟨⟨blkZHom h C, blkZHom_mem_stabE h C⟩, avec_blkZHom h C, cval_blkZHom h C, ?_, ?_, ?_⟩
  · change ((blkZHom h C : hypSU h 1 ε) : GL (HypIndex 1 ε) K).val = _
    rw [coe_blkZHom, hC]
  · change ((zBlockHom h ⟨blkZHom h C, blkZHom_mem_stabE h C⟩ : StatedSU ε (2 ^ f) K) :
      GL (Fin ε) K).val = _
    rw [zBlockHom_blkZHom, hC]
  · refine Subtype.ext ?_
    rw [SubgroupClass.coe_pow]
    change blkZHom h C ^ (2 ^ f + 1) = 1
    rw [← map_pow, hCn, map_one]

theorem exists_stdW_diag (hε : 2 ≤ ε) {l : K} (hl : l ^ 2 ^ f * l = 1) (hl1 : l ≠ 1) :
    ∃ g ∈ stdW (ε := ε) h, ∃ d : Fin ε → K, rmat h g = diagonal d ∧
      ∀ j : Fin ε, (j : ℕ) < 2 → d j ≠ 1 := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hl
    exact zero_ne_one hl
  set i₀ : Fin ε := ⟨0, by omega⟩
  set i₁ : Fin ε := ⟨1, by omega⟩
  have h01 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  set d : Fin ε → K := Function.update (Function.update 1 i₁ l⁻¹) i₀ l with hd_def
  have hli : l⁻¹ ^ 2 ^ f * l⁻¹ = 1 := by rw [inv_pow, ← mul_inv, hl, inv_one]
  have hd : ∀ i, d i ^ 2 ^ f * d i = 1 := by
    intro i
    by_cases hi0 : i = i₀
    · rw [hi0, hd_def, Function.update_self]
      exact hl
    · by_cases hi1 : i = i₁
      · rw [hi1, hd_def, Function.update_of_ne h01, Function.update_self]
        exact hli
      · rw [hd_def, Function.update_of_ne hi0, Function.update_of_ne hi1, Pi.one_apply, one_pow,
          one_mul]
  have hdet : ∏ i, d i = 1 := by
    rw [hd_def, Finset.prod_update_of_mem (Finset.mem_univ i₀),
      Finset.prod_update_of_mem (by simp [h01] : i₁ ∈ Finset.univ \ {i₀})]
    simp [hl0]
  obtain ⟨g, ha, hc, -, hρ, -⟩ := exists_diag_stabE h hd hdet
  refine ⟨g, mem_stdW_of h ha hc fun j hj => ?_, d, hρ, fun j hj => ?_⟩
  · have hj0 : j ≠ i₀ := by
      intro e
      rw [e] at hj
      simp [i₀] at hj
    have hj1 : j ≠ i₁ := by
      intro e
      rw [e] at hj
      simp [i₁] at hj
    have hdj : d j = 1 := by
      rw [hd_def, Function.update_of_ne hj0, Function.update_of_ne hj1, Pi.one_apply]
    rw [hρ]
    funext i
    rw [mulVec_diagonal]
    by_cases hij : i = j
    · rw [hij, hdj, one_mul]
    · rw [Pi.single_eq_of_ne hij, mul_zero]
  · rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 by omega) with h0 | h1
    · rw [show j = i₀ from Fin.ext h0, hd_def, Function.update_self]
      exact hl1
    · rw [show j = i₁ from Fin.ext h1, hd_def, Function.update_of_ne h01, Function.update_self]
      exact fun e => hl1 (inv_eq_one.mp e)

end Diag

section Inv

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

theorem commSub_stdW (hε : 2 ≤ ε) : commSub h (stdW (ε := ε) h) = V01 K ε := by
  obtain ⟨l, hl, hl1⟩ := exists_norm_one_ne_one h.card_eq_sq
  obtain ⟨g₀, hg₀, d, hd, hd1⟩ := exists_stdW_diag h hε hl hl1
  ext v
  rw [mem_commSub]
  constructor
  · intro hv
    refine (AddSubgroup.closure_le (V01 K ε).toAddSubgroup).mpr ?_ hv
    rintro _ ⟨g, hg, w, rfl⟩
    intro j hj
    rw [Pi.sub_apply, rmat_mulVec_apply_of_mem_stdW h hg hj, sub_self]
  · intro hv
    refine AddSubgroup.subset_closure ⟨g₀, hg₀,
      fun j => if (j : ℕ) < 2 then (1 - d j)⁻¹ * v j else 0, ?_⟩
    rw [hd]
    funext j
    rw [Pi.sub_apply, mulVec_diagonal]
    by_cases hj : (j : ℕ) < 2
    · simp only [ite_eq_left hj]
      have h1 : 1 - d j ≠ 0 := sub_ne_zero.mpr (hd1 j hj).symm
      field_simp
    · simp only [ite_eq_right hj, mul_zero, sub_zero]
      exact hv j (by omega)

theorem fixSub_stdW (hε : 2 ≤ ε) : fixSub h (stdW (ε := ε) h) = V2 K ε := by
  obtain ⟨l, hl, hl1⟩ := exists_norm_one_ne_one h.card_eq_sq
  obtain ⟨g₀, hg₀, d, hd, hd1⟩ := exists_stdW_diag h hε hl hl1
  ext v
  rw [mem_fixSub]
  constructor
  · intro hv j hj
    have h1 := congrFun (hv g₀ hg₀) j
    rw [hd, mulVec_diagonal] at h1
    have h2 : (d j - 1) * v j = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (hd1 j hj))
  · intro hv g hg
    exact rmat_mulVec_of_mem_V2 h hg hv

theorem finrank_commSub_stdW (hε : 2 ≤ ε) :
    Module.finrank K (commSub h (stdW (ε := ε) h)) = 2 := by
  rw [commSub_stdW h hε, finrank_V01 hε]

theorem finrank_fixSub_stdW (hε : 2 ≤ ε) :
    Module.finrank K (fixSub h (stdW (ε := ε) h)) = ε - 2 := by
  rw [fixSub_stdW h hε, finrank_V2 hε]

theorem commSub_inf_fixSub_stdW (hε : 2 ≤ ε) :
    commSub h (stdW (ε := ε) h) ⊓ fixSub h (stdW h) = ⊥ := by
  rw [commSub_stdW h hε, fixSub_stdW h hε, V01_inf_V2]

end Inv

section Zt

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

theorem exists_zt (hε : 3 ≤ ε) :
    ∃ z : stabE (ε := ε) h, z ^ (2 ^ f + 1) = 1 ∧ (∀ g ∈ stdW h, z * g = g * z) ∧
      commSub h (stdW h) ⊓ fixOneSub h z = ⊥ := by
  obtain ⟨l, hl, hl1⟩ := exists_norm_one_ne_one h.card_eq_sq
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hl
    exact zero_ne_one hl
  set i₀ : Fin ε := ⟨0, by omega⟩
  set i₁ : Fin ε := ⟨1, by omega⟩
  set i₂ : Fin ε := ⟨2, by omega⟩
  have h01 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₂ ≠ i₀ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₂ ≠ i₁ := by simp [i₁, i₂, Fin.ext_iff]
  set d : Fin ε → K :=
    Function.update (Function.update (Function.update 1 i₂ (l⁻¹ ^ 2)) i₁ l) i₀ l with hd_def
  have hli : l⁻¹ ^ 2 ^ f * l⁻¹ = 1 := by rw [inv_pow, ← mul_inv, hl, inv_one]
  have hd01 : ∀ i : Fin ε, (i : ℕ) < 2 → d i = l := by
    intro i hi
    rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with h0 | h1
    · rw [show i = i₀ from Fin.ext h0, hd_def, Function.update_self]
    · rw [show i = i₁ from Fin.ext h1, hd_def, Function.update_of_ne h01, Function.update_self]
  have hd : ∀ i, d i ^ 2 ^ f * d i = 1 := by
    intro i
    by_cases hi : (i : ℕ) < 2
    · rw [hd01 i hi]
      exact hl
    · have hi0 : i ≠ i₀ := fun e => hi (by rw [e]; simp [i₀])
      have hi1 : i ≠ i₁ := fun e => hi (by rw [e]; simp [i₁])
      by_cases hi2 : i = i₂
      · rw [hi2, hd_def, Function.update_of_ne h02, Function.update_of_ne h12,
          Function.update_self]
        calc (l⁻¹ ^ 2) ^ 2 ^ f * l⁻¹ ^ 2 = (l⁻¹ ^ 2 ^ f * l⁻¹) ^ 2 := by ring
          _ = 1 := by rw [hli, one_pow]
      · rw [hd_def, Function.update_of_ne hi0, Function.update_of_ne hi1,
          Function.update_of_ne hi2, Pi.one_apply, one_pow, one_mul]
  have hdet : ∏ i, d i = 1 := by
    rw [hd_def, Finset.prod_update_of_mem (Finset.mem_univ i₀),
      Finset.prod_update_of_mem (by simp [h01] : i₁ ∈ Finset.univ \ {i₀}),
      Finset.prod_update_of_mem (by simp [h02, h12] : i₂ ∈ (Finset.univ \ {i₀}) \ {i₁})]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
    field_simp
  obtain ⟨z, -, -, hzs, hzρ, hzn⟩ := exists_diag_stabE h hd hdet
  refine ⟨z, hzn, fun g hg => ?_, ?_⟩
  ·
    have hcomm : diagonal d * rmat h g = rmat h g * diagonal d := by
      ext i j
      rw [diagonal_mul, mul_diagonal]
      by_cases hj : 2 ≤ (j : ℕ)
      · have h1 := congrFun (rmat_mulVec_of_mem_stdW h hg hj) i
        rw [mulVec_single_one, col_apply] at h1
        rw [h1, Pi.single_apply]
        split_ifs with hij
        · rw [hij, mul_one, one_mul]
        · rw [mul_zero, zero_mul]
      · by_cases hi : 2 ≤ (i : ℕ)
        · have hij : i ≠ j := fun e => hj (e ▸ hi)
          have h1 := rmat_mulVec_apply_of_mem_stdW h hg hi (Pi.single j 1)
          rw [mulVec_single_one, col_apply, Pi.single_eq_of_ne hij] at h1
          rw [h1, mul_zero, zero_mul]
        · rw [hd01 i (by omega), hd01 j (by omega), mul_comm]
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    change smat h z * smat h g = smat h g * smat h z
    rw [hzs, smat_of_mem_stdW h hg, blkZM_mul, blkZM_mul, hcomm]
  · rw [commSub_stdW h (by omega), eq_bot_iff]
    rintro v ⟨hv, hvz⟩
    rw [Submodule.mem_bot]
    funext j
    by_cases hj : (j : ℕ) < 2
    · have h1 := congrFun (hvz : rmat h z *ᵥ v = v) j
      rw [hzρ, mulVec_diagonal, hd01 j hj] at h1
      have h2 : (l - 1) * v j = 0 := by rw [sub_mul, h1, one_mul, sub_self]
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hl1)
    · exact hv j (by omega)

end Zt

end CFSG.ComponentClassification.RankTwoClassical.URigid
