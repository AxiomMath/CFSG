module

public import CFSG.LocalAnalysis.EvenBN.U5.Model

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

@[expose] def pN₂ : HypIndex 2 1 → Option (HypIndex 1 1)
  | .inl i => if i = 0 then none else some (.inl 0)
  | .inr (.inl _) => some (.inr (.inl 0))
  | .inr (.inr j) => if j = 0 then none else some (.inr (.inr 0))

@[expose] def embN₂ (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) :
    Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
  Matrix.of fun a b => match pN₂ a, pN₂ b with
    | some i, some j => M i j
    | _, _ => if a = b then 1 else 0

abbrev jE : HypIndex 1 1 := .inl 0
abbrev jZ : HypIndex 1 1 := .inr (.inl 0)
abbrev jF : HypIndex 1 1 := .inr (.inr 0)

theorem sum_hypIndex_one (g : HypIndex 1 1 → K) : ∑ i, g i = g jE + g jZ + g jF := by
  simp [Fintype.sum_sum_type, add_assoc]

theorem sum_hypIndex_two (g : HypIndex 2 1 → K) :
    ∑ a, g a = g ιe₁ + g ιe₂ + g ιz + g ιf₁ + g ιf₂ := by
  simp [Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem embN₂_entries (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) :
    (embN₂ M ιe₁ ιe₁ = 1 ∧ embN₂ M ιe₁ ιe₂ = 0 ∧ embN₂ M ιe₁ ιz = 0 ∧ embN₂ M ιe₁ ιf₁ = 0 ∧
      embN₂ M ιe₁ ιf₂ = 0) ∧
    (embN₂ M ιe₂ ιe₁ = 0 ∧ embN₂ M ιe₂ ιe₂ = M jE jE ∧ embN₂ M ιe₂ ιz = M jE jZ ∧
      embN₂ M ιe₂ ιf₁ = 0 ∧ embN₂ M ιe₂ ιf₂ = M jE jF) ∧
    (embN₂ M ιz ιe₁ = 0 ∧ embN₂ M ιz ιe₂ = M jZ jE ∧ embN₂ M ιz ιz = M jZ jZ ∧
      embN₂ M ιz ιf₁ = 0 ∧ embN₂ M ιz ιf₂ = M jZ jF) ∧
    (embN₂ M ιf₁ ιe₁ = 0 ∧ embN₂ M ιf₁ ιe₂ = 0 ∧ embN₂ M ιf₁ ιz = 0 ∧ embN₂ M ιf₁ ιf₁ = 1 ∧
      embN₂ M ιf₁ ιf₂ = 0) ∧
    (embN₂ M ιf₂ ιe₁ = 0 ∧ embN₂ M ιf₂ ιe₂ = M jF jE ∧ embN₂ M ιf₂ ιz = M jF jZ ∧
      embN₂ M ιf₂ ιf₁ = 0 ∧ embN₂ M ιf₂ ιf₂ = M jF jF) := by
  simp [embN₂, pN₂]

theorem embN₂_mul (M N : Matrix (HypIndex 1 1) (HypIndex 1 1) K) :
    embN₂ (M * N) = embN₂ M * embN₂ N := by
  ext a b
  rw [Matrix.mul_apply, sum_hypIndex_two]
  obtain ⟨⟨a11, a12, a13, a14, a15⟩, ⟨a21, a22, a23, a24, a25⟩, ⟨a31, a32, a33, a34, a35⟩,
    ⟨a41, a42, a43, a44, a45⟩, ⟨a51, a52, a53, a54, a55⟩⟩ := embN₂_entries M
  obtain ⟨⟨b11, b12, b13, b14, b15⟩, ⟨b21, b22, b23, b24, b25⟩, ⟨b31, b32, b33, b34, b35⟩,
    ⟨b41, b42, b43, b44, b45⟩, ⟨b51, b52, b53, b54, b55⟩⟩ := embN₂_entries N
  obtain ⟨⟨c11, c12, c13, c14, c15⟩, ⟨c21, c22, c23, c24, c25⟩, ⟨c31, c32, c33, c34, c35⟩,
    ⟨c41, c42, c43, c44, c45⟩, ⟨c51, c52, c53, c54, c55⟩⟩ := embN₂_entries (M * N)
  rcases a with i | k | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
    (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at * <;>
    simp only [*, Matrix.mul_apply, sum_hypIndex_one] <;> ring

theorem embN₂_one : embN₂ (1 : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = 1 := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
    (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [embN₂, pN₂, one_apply]

@[expose] def eN₂ : HypIndex 1 1 ⊕ Fin 2 ≃ HypIndex 2 1 where
  toFun
    | .inl (.inl _) => ιe₂
    | .inl (.inr (.inl _)) => ιz
    | .inl (.inr (.inr _)) => ιf₂
    | .inr i => if i = 0 then ιe₁ else ιf₁
  invFun
    | .inl i => if i = 0 then .inr 0 else .inl jE
    | .inr (.inl _) => .inl jZ
    | .inr (.inr j) => if j = 0 then .inr 1 else .inl jF
  left_inv := by decide
  right_inv := by decide

theorem embN₂_eq_submatrix (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) :
    embN₂ M = (fromBlocks M 0 0 (1 : Matrix (Fin 2) (Fin 2) K)).submatrix eN₂.symm eN₂.symm := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
    (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [embN₂, pN₂, eN₂, one_apply]

theorem det_embN₂ (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) : (embN₂ M).det = M.det := by
  rw [embN₂_eq_submatrix, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem embN₂_gram_apply (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (i j : HypIndex 1 1) :
    (((embN₂ M).map h.bar)ᵀ * hypGram 2 1 K * embN₂ M) (eN₂ (.inl i)) (eN₂ (.inl j)) =
      ((M.map h.bar)ᵀ * hypGram 1 1 K * M) i j := by
  rw [conjTranspose_hypGram_mul_apply, conjTranspose_hypGram_mul_apply, sum_hypIndex_two,
    sum_hypIndex_one]
  obtain ⟨⟨a11, a12, a13, a14, a15⟩, ⟨a21, a22, a23, a24, a25⟩, ⟨a31, a32, a33, a34, a35⟩,
    ⟨a41, a42, a43, a44, a45⟩, ⟨a51, a52, a53, a54, a55⟩⟩ := embN₂_entries M
  rcases i with i | k | i <;> rcases j with j | l | j <;> (try fin_cases i) <;>
    (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [eN₂, *]

theorem embN₂_gram_apply_ef (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (a : HypIndex 2 1) :
    (((embN₂ M).map h.bar)ᵀ * hypGram 2 1 K * embN₂ M) ιe₁ a = hypGram 2 1 K ιe₁ a ∧
    (((embN₂ M).map h.bar)ᵀ * hypGram 2 1 K * embN₂ M) ιf₁ a = hypGram 2 1 K ιf₁ a ∧
    (((embN₂ M).map h.bar)ᵀ * hypGram 2 1 K * embN₂ M) a ιe₁ = hypGram 2 1 K a ιe₁ ∧
    (((embN₂ M).map h.bar)ᵀ * hypGram 2 1 K * embN₂ M) a ιf₁ = hypGram 2 1 K a ιf₁ := by
  rw [conjTranspose_hypGram_mul_apply, conjTranspose_hypGram_mul_apply,
    conjTranspose_hypGram_mul_apply, conjTranspose_hypGram_mul_apply, sum_hypIndex_two,
    sum_hypIndex_two, sum_hypIndex_two, sum_hypIndex_two]
  obtain ⟨⟨a11, a12, a13, a14, a15⟩, ⟨a21, a22, a23, a24, a25⟩, ⟨a31, a32, a33, a34, a35⟩,
    ⟨a41, a42, a43, a44, a45⟩, ⟨a51, a52, a53, a54, a55⟩⟩ := embN₂_entries M
  rcases a with i | k | i <;> (try fin_cases i) <;> (try fin_cases k) <;>
    simp [*, hypGram_apply]

theorem embN₂_gram_iff (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) :
    ((embN₂ M).map h.bar)ᵀ * hypGram 2 1 K * embN₂ M = hypGram 2 1 K ↔
      (M.map h.bar)ᵀ * hypGram 1 1 K * M = hypGram 1 1 K := by
  constructor
  · intro hG
    ext i j
    rw [← embN₂_gram_apply, hG]
    rcases i with i | k | i <;> rcases j with j | l | j <;> (try fin_cases i) <;>
      (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
      simp [eN₂, hypGram_apply]
  · intro hG
    ext a b
    have hab : ∀ a b, (a = ιe₁ ∨ a = ιf₁ ∨ b = ιe₁ ∨ b = ιf₁) →
        (((embN₂ M).map h.bar)ᵀ * hypGram 2 1 K * embN₂ M) a b = hypGram 2 1 K a b := by
      rintro a b (rfl | rfl | rfl | rfl)
      · exact (embN₂_gram_apply_ef M b).1
      · exact (embN₂_gram_apply_ef M b).2.1
      · exact (embN₂_gram_apply_ef M a).2.2.1
      · exact (embN₂_gram_apply_ef M a).2.2.2
    have hin : ∀ i j, (((embN₂ M).map h.bar)ᵀ * hypGram 2 1 K * embN₂ M) (eN₂ (.inl i))
        (eN₂ (.inl j)) = hypGram 2 1 K (eN₂ (.inl i)) (eN₂ (.inl j)) := by
      intro i j
      rw [embN₂_gram_apply, hG]
      rcases i with i | k | i <;> rcases j with j | l | j <;> (try fin_cases i) <;>
        (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
        simp [eN₂, hypGram_apply]
    rcases a with i | k | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
      (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
      first
      | (apply hab; decide)
      | exact hin jE jE | exact hin jE jZ | exact hin jE jF | exact hin jZ jE | exact hin jZ jZ
      | exact hin jZ jF | exact hin jF jE | exact hin jF jZ | exact hin jF jF

abbrev mat₃ (g : hypSU h 1 1) : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)

@[expose] def embSU (h : UnitaryFieldData 2 f K) : hypSU h 1 1 →* hypSU h 2 1 where
  toFun g := mkHypSU h (embN₂ (mat₃ g)) ((embN₂_gram_iff (mat₃ g)).2 (mem_hypSU.1 g.2).1)
    (by rw [det_embN₂]; exact (mem_hypSU.1 g.2).2)
  map_one' := by
    apply mat_injective
    rw [mat, coe_mkHypSU, mat_one]
    exact embN₂_one
  map_mul' g g' := by
    apply mat_injective
    rw [mat_mul, mat, mat, mat, coe_mkHypSU, coe_mkHypSU, coe_mkHypSU, ← embN₂_mul]
    rfl

theorem mat_embSU (g : hypSU h 1 1) : mat (embSU h g) = embN₂ (mat₃ g) := rfl

theorem embSU_injective : Function.Injective (embSU h) := by
  intro g g' e
  have e' := congrArg mat e
  rw [mat_embSU, mat_embSU] at e'
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrFun (congrFun e' (eN₂ (.inl i))) (eN₂ (.inl j))
  rcases i with i | k | i <;> rcases j with j | l | j <;> (try fin_cases i) <;>
    (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simpa [embN₂, pN₂, eN₂] using this

theorem N₂sub_rows {g : hypSU h 2 1} (hg : g ∈ N₂sub h) (b : HypIndex 2 1) :
    mat g ιe₁ b = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) ιe₁ b ∧
      mat g ιf₁ b = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) ιf₁ b := by
  obtain ⟨hc1, hc2⟩ := mem_N₂sub.1 (inv_mem hg)
  have e1 := mat_inv_apply g⁻¹ ιe₁ b
  have e2 := mat_inv_apply g⁻¹ ιf₁ b
  rw [inv_inv] at e1 e2
  rw [e1, e2]
  simp only [hypPartner_inl, hypPartner_inr_inr]
  rw [hc2, hc1, one_apply, one_apply, one_apply, one_apply]
  have k1 : (hypPartner b = ιf₁) ↔ (ιe₁ = b) := by
    rw [hypPartner_eq_iff, eq_comm]; rfl
  have k2 : (hypPartner b = ιe₁) ↔ (ιf₁ = b) := by
    rw [hypPartner_eq_iff, eq_comm]; rfl
  constructor
  · by_cases hb : ιe₁ = b
    · rw [ite_eq_left (k1.2 hb), ite_eq_left hb, map_one]
    · rw [ite_eq_right (fun e => hb (k1.1 e)), ite_eq_right hb, map_zero]
  · by_cases hb : ιf₁ = b
    · rw [ite_eq_left (k2.2 hb), ite_eq_left hb, map_one]
    · rw [ite_eq_right (fun e => hb (k2.1 e)), ite_eq_right hb, map_zero]

theorem range_embSU : (embSU h).range = N₂sub h := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    rw [mem_N₂sub, mat_embSU]
    obtain ⟨⟨a11, a12, a13, a14, a15⟩, ⟨a21, a22, a23, a24, a25⟩, ⟨a31, a32, a33, a34, a35⟩,
      ⟨a41, a42, a43, a44, a45⟩, ⟨a51, a52, a53, a54, a55⟩⟩ := embN₂_entries (mat₃ g)
    refine ⟨fun a => ?_, fun a => ?_⟩ <;> rcases a with i | k | i <;> (try fin_cases i) <;>
      (try fin_cases k) <;> simp [*, one_apply]
  · intro g hg
    set M : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
      Matrix.of fun i j => mat g (eN₂ (.inl i)) (eN₂ (.inl j)) with hM
    obtain ⟨hc1, hc2⟩ := mem_N₂sub.1 hg
    have hrows := N₂sub_rows hg
    have hemb : embN₂ M = mat g := by
      ext a b
      by_cases ha : a = ιe₁ ∨ a = ιf₁
      · rcases ha with rfl | rfl
        · rw [(hrows b).1]
          rcases b with i | k | i <;> (try fin_cases i) <;> (try fin_cases k) <;>
            simp [embN₂, pN₂, one_apply]
        · rw [(hrows b).2]
          rcases b with i | k | i <;> (try fin_cases i) <;> (try fin_cases k) <;>
            simp [embN₂, pN₂, one_apply]
      by_cases hb : b = ιe₁ ∨ b = ιf₁
      · rcases hb with rfl | rfl
        · rw [hc1 a]
          rcases a with i | k | i <;> (try fin_cases i) <;> (try fin_cases k) <;>
            simp [embN₂, pN₂, one_apply]
        · rw [hc2 a]
          rcases a with i | k | i <;> (try fin_cases i) <;> (try fin_cases k) <;>
            simp [embN₂, pN₂, one_apply]
      rcases a with i | k | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
        (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
        first
        | exact absurd (Or.inl rfl) ha
        | exact absurd (Or.inr rfl) ha
        | exact absurd (Or.inl rfl) hb
        | exact absurd (Or.inr rfl) hb
        | simp [embN₂, pN₂, eN₂, M]
    have hgram : (M.map h.bar)ᵀ * hypGram 1 1 K * M = hypGram 1 1 K :=
      (embN₂_gram_iff M).1 (by rw [hemb]; exact (mem_hypSU.1 g.2).1)
    have hdet : M.det = 1 := by rw [← det_embN₂, hemb]; exact (mem_hypSU.1 g.2).2
    refine ⟨mkHypSU h M hgram hdet, mat_injective ?_⟩
    rw [mat_embSU, mat₃, coe_mkHypSU, hemb]

noncomputable def N₂equiv (h : UnitaryFieldData 2 f K) : hypSU h 1 1 ≃* N₂sub h :=
  (MonoidHom.ofInjective embSU_injective).trans (MulEquiv.subgroupCongr range_embSU)

theorem N₂sub_inf_hypScalars : N₂sub h ⊓ hypScalars h 2 1 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z ⟨hzN, hzZ⟩ => ?_
  obtain ⟨c, -, hcm⟩ := exists_scalar_of_mem_hypScalars hzZ
  have h1 := (mem_N₂sub.1 hzN).1 ιe₁
  rw [hcm, ite_eq_left rfl, one_apply_eq] at h1
  apply mat_injective
  ext a b
  rw [hcm, h1, mat_one, one_apply]

theorem N₁sub_inf_hypScalars : N₁sub h ⊓ hypScalars h 2 1 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z ⟨⟨A, hA⟩, hzZ⟩ => ?_
  obtain ⟨c, -, hcm⟩ := exists_scalar_of_mem_hypScalars hzZ
  have h1 := hcm ιz ιz
  rw [← hA, mat_leviSU, ite_eq_left rfl] at h1
  simp only [blk3_inr_inl_inr_inl, one_apply_eq] at h1
  apply mat_injective
  ext a b
  rw [hcm, ← h1, mat_one, one_apply]

namespace Data

variable {G : Type} [Group G] (d : Data G h)

noncomputable def pullEquiv {M : Subgroup (hypSU h 2 1)} (hM : M ⊓ hypScalars h 2 1 = ⊥) :
    M ≃* d.pull M := by
  refine (MonoidHom.ofInjective (f := d.η.comp M.subtype) ?_).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype]; rfl))
  intro x y e
  have e' : d.η x = d.η y := e
  have hk : (x : hypSU h 2 1)⁻¹ * y ∈ M ⊓ hypScalars h 2 1 :=
    Subgroup.mem_inf.2 ⟨M.mul_mem (M.inv_mem x.2) y.2,
      (d.η_eq_one_iff _).1 (by rw [map_mul, map_inv, e', inv_mul_cancel])⟩
  rw [hM, mem_bot] at hk
  exact Subtype.ext (inv_mul_eq_one.1 hk)

noncomputable def N₁equiv : SpecialLinearGroup (Fin 2) K ≃* d.N₁ :=
  (U5.N₁equiv h).trans (d.pullEquiv N₁sub_inf_hypScalars)

noncomputable def N₂equiv : hypSU h 1 1 ≃* d.N₂ :=
  (U5.N₂equiv h).trans (d.pullEquiv N₂sub_inf_hypScalars)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
