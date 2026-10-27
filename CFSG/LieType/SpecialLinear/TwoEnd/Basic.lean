module

public import CFSG.LieType.SpecialLinear.EndNode.Blocks
public import CFSG.Quasithin.Background.SmithCurtisBasic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.SpecialLinear

noncomputable section

section EmbedMid

variable (m : ℕ) (F : Type) [Field F]

@[expose] def embedMid : SpecialLinearGroup (Fin (m+1)) F →* SpecialLinearGroup (Fin (m+3)) F :=
  (embedSucc (m+1) F).comp (embedCastSucc m F)

theorem coe_embedMid (g : SpecialLinearGroup (Fin (m+1)) F) :
    ((embedMid m F g : SpecialLinearGroup (Fin (m+3)) F) :
        Matrix (Fin (m+3)) (Fin (m+3)) F) =
      embedSuccMat (m+1) F
        (embedCastSuccMat m F (g : Matrix (Fin (m+1)) (Fin (m+1)) F)) := by
  simp [embedMid, coe_embedSucc, coe_embedCastSucc]

theorem coe_embedMid_succ_succ (g : SpecialLinearGroup (Fin (m+1)) F)
    (i j : Fin (m+1)) :
    ((embedMid m F g : SpecialLinearGroup (Fin (m+3)) F) :
        Matrix (Fin (m+3)) (Fin (m+3)) F) i.castSucc.succ j.castSucc.succ =
      (g : Matrix (Fin (m+1)) (Fin (m+1)) F) i j := by
  rw [coe_embedMid, embedSuccMat_apply_succ_succ, embedCastSuccMat,
    Matrix.blockSucc_castSucc_castSucc]

theorem embedMid_apply_zero (g : SpecialLinearGroup (Fin (m+1)) F) (i : Fin (m+3)) :
    ((embedMid m F g : SpecialLinearGroup (Fin (m+3)) F) :
        Matrix (Fin (m+3)) (Fin (m+3)) F) i 0 = if i = 0 then 1 else 0 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rw [coe_embedMid]
    simp [embedSuccMat, fromBlocksFirst_apply_zero_zero]
  · rw [coe_embedMid, embedSuccMat_apply_succ_zero]
    simp

theorem embedMid_apply_last (g : SpecialLinearGroup (Fin (m+1)) F) (i : Fin (m+3)) :
    ((embedMid m F g : SpecialLinearGroup (Fin (m+3)) F) :
        Matrix (Fin (m+3)) (Fin (m+3)) F) i (Fin.last (m+2)) =
      if i = Fin.last (m+2) then 1 else 0 := by
  have hlast : (Fin.last (m+2) : Fin (m+3)) = (Fin.last (m+1)).succ := rfl
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rw [coe_embedMid, hlast, embedSuccMat_apply_zero_succ]
    simp
  · rw [coe_embedMid, hlast, embedSuccMat_apply_succ_succ]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rw [embedCastSuccMat, Matrix.blockSucc_castSucc_last]
      simp [Fin.castSucc_ne_last]
    · rw [embedCastSuccMat, Matrix.blockSucc_last_last]
      simp

theorem embedMid_zero_apply (g : SpecialLinearGroup (Fin (m+1)) F) (j : Fin (m+3)) :
    ((embedMid m F g : SpecialLinearGroup (Fin (m+3)) F) :
        Matrix (Fin (m+3)) (Fin (m+3)) F) 0 j = if j = 0 then 1 else 0 := by
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rw [coe_embedMid]
    simp [embedSuccMat, fromBlocksFirst_apply_zero_zero]
  · rw [coe_embedMid, embedSuccMat_apply_zero_succ]
    simp

theorem embedMid_last_apply (g : SpecialLinearGroup (Fin (m+1)) F) (j : Fin (m+3)) :
    ((embedMid m F g : SpecialLinearGroup (Fin (m+3)) F) :
        Matrix (Fin (m+3)) (Fin (m+3)) F) (Fin.last (m+2)) j =
      if j = Fin.last (m+2) then 1 else 0 := by
  have hlast : (Fin.last (m+2) : Fin (m+3)) = (Fin.last (m+1)).succ := rfl
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rw [coe_embedMid, hlast, embedSuccMat_apply_succ_zero]
    simp
  · rw [coe_embedMid, hlast, embedSuccMat_apply_succ_succ]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · rw [embedCastSuccMat, Matrix.blockSucc_last_castSucc]
      simp [Fin.castSucc_ne_last]
    · rw [embedCastSuccMat, Matrix.blockSucc_last_last]
      simp

end EmbedMid

section Shape

variable {m : ℕ} {F : Type} [Field F]

@[expose] def IsTwoEndZero (N : Matrix (Fin (m+3)) (Fin (m+3)) F) : Prop :=
  (∀ i, N i i = 0) ∧ ∀ i j, i ≠ 0 → j ≠ Fin.last (m+2) → N i j = 0

theorem isTwoEndZero_zero : IsTwoEndZero (m := m) (F := F) 0 := by
  refine ⟨fun i => by simp, fun i j _ _ => by simp⟩

theorem IsTwoEndZero.add {N M : Matrix (Fin (m+3)) (Fin (m+3)) F}
    (hN : IsTwoEndZero N) (hM : IsTwoEndZero M) : IsTwoEndZero (N + M) := by
  refine ⟨fun i => by rw [Matrix.add_apply, hN.1 i, hM.1 i, add_zero], ?_⟩
  intro i j hi hj
  rw [Matrix.add_apply, hN.2 i j hi hj, hM.2 i j hi hj, add_zero]

theorem IsTwoEndZero.neg {N : Matrix (Fin (m+3)) (Fin (m+3)) F}
    (hN : IsTwoEndZero N) : IsTwoEndZero (-N) := by
  refine ⟨fun i => by rw [Matrix.neg_apply, hN.1 i, neg_zero], ?_⟩
  intro i j hi hj
  rw [Matrix.neg_apply, hN.2 i j hi hj, neg_zero]

theorem IsTwoEndZero.map {N : Matrix (Fin (m+3)) (Fin (m+3)) F}
    (hN : IsTwoEndZero N) (σ : F →+* F) : IsTwoEndZero (N.map σ) := by
  refine ⟨fun i => by rw [Matrix.map_apply, hN.1 i, map_zero], ?_⟩
  intro i j hi hj
  rw [Matrix.map_apply, hN.2 i j hi hj, map_zero]

theorem IsTwoEndZero.mul {N M : Matrix (Fin (m+3)) (Fin (m+3)) F}
    (hN : IsTwoEndZero N) (hM : IsTwoEndZero M) : IsTwoEndZero (N * M) := by
  constructor
  · intro i
    rw [Matrix.mul_apply]
    by_cases hi0 : i = 0
    · rw [hi0]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = 0
      · rw [hk, hN.1, zero_mul]
      · rw [hM.2 k 0 hk (by simp), mul_zero]
    · by_cases hil : i = Fin.last (m+2)
      · rw [hil]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k = Fin.last (m+2)
        · rw [hk, hN.1, zero_mul]
        · rw [hN.2 _ _ (by simp) hk, zero_mul]
      · refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : k = Fin.last (m+2)
        · rw [hk, hM.2 _ _ (by simp) hil, mul_zero]
        · rw [hN.2 i k hi0 hk, zero_mul]
  · intro i j hi hj
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = Fin.last (m+2)
    · rw [hk, hM.2 _ _ (by simp) hj, mul_zero]
    · rw [hN.2 i k hi hk, zero_mul]

theorem IsTwoEndZero.sq_eq_zero {N : Matrix (Fin (m+3)) (Fin (m+3)) F}
    (hN : IsTwoEndZero N) {i j : Fin (m+3)}
    (h : ¬ (i = 0 ∧ j = Fin.last (m+2))) : (N * N) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk0 : k = 0
  · rw [hk0]
    by_cases hi0 : i = 0
    · rw [hi0, hN.1, zero_mul]
    · rw [hN.2 i 0 hi0 (by simp), zero_mul]
  · by_cases hk : k = Fin.last (m+2)
    · rw [hk]
      by_cases hj : j = Fin.last (m+2)
      · rw [hj, hN.1, mul_zero]
      · rw [hN.2 _ j (by simp) hj, mul_zero]
    · by_cases hj : j = Fin.last (m+2)
      · rw [hj]
        have hi0 : i ≠ 0 := fun h0 => h ⟨h0, hj⟩
        rw [hN.2 i k hi0 hk, zero_mul]
      · rw [hN.2 k j hk0 hj, mul_zero]

theorem IsTwoEndZero.mul_self_mul {N : Matrix (Fin (m+3)) (Fin (m+3)) F}
    (hN : IsTwoEndZero N) : N * N * N = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = Fin.last (m+2)
  · rw [hk]
    by_cases hj : j = Fin.last (m+2)
    · rw [hj, hN.1, mul_zero]
    · rw [hN.2 _ j (by simp) hj, mul_zero]
  · by_cases hi : i = 0
    · rw [hi, hN.sq_eq_zero (by intro h; exact hk h.2), zero_mul]
    · rw [hN.sq_eq_zero (by intro h; exact hi h.1), zero_mul]

end Shape

section Radical

variable (m : ℕ) (F : Type) [Field F]

@[expose] def twoEndRadical : Subgroup (SpecialLinearGroup (Fin (m+3)) F) where
  carrier := {g : SpecialLinearGroup (Fin (m+3)) F |
    IsTwoEndZero ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1)}
  one_mem' := by
    show IsTwoEndZero (((1 : SpecialLinearGroup (Fin (m+3)) F) :
      Matrix (Fin (m+3)) (Fin (m+3)) F) - 1)
    rw [Matrix.SpecialLinearGroup.coe_one, sub_self]
    exact isTwoEndZero_zero
  mul_mem' := by
    intro g h hg hh
    show IsTwoEndZero (((g * h : SpecialLinearGroup (Fin (m+3)) F) :
      Matrix (Fin (m+3)) (Fin (m+3)) F) - 1)
    have hgh : ((g * h : SpecialLinearGroup (Fin (m+3)) F) :
        Matrix (Fin (m+3)) (Fin (m+3)) F) - 1 =
        ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) +
          ((h : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) +
          ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) *
            ((h : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      noncomm_ring
    rw [hgh]
    exact (hg.add hh).add (hg.mul hh)
  inv_mem' := by
    intro g hg
    show IsTwoEndZero (((g⁻¹ : SpecialLinearGroup (Fin (m+3)) F) :
      Matrix (Fin (m+3)) (Fin (m+3)) F) - 1)
    have hgN : IsTwoEndZero ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) := hg
    have hcoe : ((g⁻¹ : SpecialLinearGroup (Fin (m+3)) F) :
        Matrix (Fin (m+3)) (Fin (m+3)) F) =
        ((g : Matrix (Fin (m+3)) (Fin (m+3)) F))⁻¹ := by
      have hmul : (g : Matrix (Fin (m+3)) (Fin (m+3)) F) *
          ((g⁻¹ : SpecialLinearGroup (Fin (m+3)) F) :
            Matrix (Fin (m+3)) (Fin (m+3)) F) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one]
      exact (Matrix.inv_eq_right_inv hmul).symm
    have hgg : (g : Matrix (Fin (m+3)) (Fin (m+3)) F) =
        1 + ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) := by abel
    have h3 : ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) *
        ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) *
        ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) = 0 := hgN.mul_self_mul
    have hinv : ((g : Matrix (Fin (m+3)) (Fin (m+3)) F))⁻¹ =
        1 - ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) +
          ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) *
            ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) := by
      apply Matrix.inv_eq_right_inv
      nth_rewrite 1 [hgg]
      calc (1 + ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1)) *
            (1 - ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) +
              ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) *
                ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1))
          = 1 + ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) *
              ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) *
              ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) := by noncomm_ring
        _ = 1 := by rw [h3, add_zero]
    rw [hcoe, hinv]
    have hsub : (1 : Matrix (Fin (m+3)) (Fin (m+3)) F) -
        ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) +
          ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) *
            ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) - 1 =
        -((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) +
          ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) *
            ((g : Matrix (Fin (m+3)) (Fin (m+3)) F) - 1) := by abel
    rw [hsub]
    exact hgN.neg.add (hgN.mul hgN)

theorem mem_twoEndRadical {g : SpecialLinearGroup (Fin (m+3)) F} :
    g ∈ twoEndRadical m F ↔
      (∀ i, (g : Matrix (Fin (m+3)) (Fin (m+3)) F) i i = 1) ∧
        ∀ i j, i ≠ 0 → j ≠ Fin.last (m+2) →
          (g : Matrix (Fin (m+3)) (Fin (m+3)) F) i j =
            (1 : Matrix (Fin (m+3)) (Fin (m+3)) F) i j := by
  constructor
  · intro hg
    refine ⟨fun i => ?_, fun i j hi hj => ?_⟩
    · exact sub_eq_zero.mp (by simpa [Matrix.sub_apply, Matrix.one_apply_eq] using hg.1 i)
    · exact sub_eq_zero.mp (by simpa [Matrix.sub_apply] using hg.2 i j hi hj)
  · rintro ⟨hdiag, hoff⟩
    refine ⟨fun i => ?_, fun i j hi hj => ?_⟩
    · simp [Matrix.sub_apply, hdiag i, Matrix.one_apply_eq]
    · simp [Matrix.sub_apply, hoff i j hi hj]

end Radical

end

end CFSG.LieType.SpecialLinear
