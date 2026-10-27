module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {ε : ℕ}

abbrev hE : HypIndex 1 ε := .inl 0

abbrev hF : HypIndex 1 ε := .inr (.inr 0)

@[expose] def eichM (σ : K →+* K) (a : Fin ε → K) (c : K) :
    Matrix (HypIndex 1 ε) (HypIndex 1 ε) K :=
  Matrix.of fun i j => match i, j with
    | .inl _, .inl _ => 1
    | .inl _, .inr (.inl l) => σ (a l)
    | .inl _, .inr (.inr _) => c
    | .inr (.inl k), .inr (.inl l) => if k = l then 1 else 0
    | .inr (.inl k), .inr (.inr _) => a k
    | .inr (.inr _), .inr (.inr _) => 1
    | _, _ => 0

theorem eichM_mul (σ : K →+* K) (a a' : Fin ε → K) (c c' : K) :
    eichM σ a c * eichM σ a' c' = eichM σ (a + a') (c + c' + ∑ k, σ (a k) * a' k) := by
  ext i j
  rcases i with i | k | i <;> rcases j with j | l | j <;>
    simp [eichM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero, ite_mul, Finset.sum_ite_eq,
      Finset.sum_ite_eq', add_comm, add_left_comm, add_assoc]

theorem eichM_zero (σ : K →+* K) : eichM (ε := ε) σ 0 0 = 1 := by
  ext i j
  rcases i with i | k | i <;> rcases j with j | l | j <;>
    simp [eichM, one_apply, Fin.eq_zero]

theorem eichM_isometry [CharP K 2] (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (a : Fin ε → K)
    {c : K} (hc : c + σ c = ∑ k, σ (a k) * a k) :
    ((eichM σ a c).map σ)ᵀ * hypGram 1 ε K * eichM σ a c = hypGram 1 ε K := by
  ext i j
  rcases i with i | k | i <;> rcases j with j | l | j <;>
    simp [eichM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero, hσ, hypGram_apply, hypPartner,
      CharTwo.add_self_eq_zero]
  rw [add_left_comm, hc, CharTwo.add_self_eq_zero]

theorem eichM_det (σ : K →+* K) (a : Fin ε → K) (c : K) : (eichM σ a c).det = 1 := by
  let α : HypIndex 1 ε → K := fun i => match i with
    | .inl _ => c
    | .inr (.inl k) => a k
    | .inr (.inr _) => 0
  let δe : HypIndex 1 ε → K := fun i => match i with
    | .inl _ => 1
    | _ => 0
  let δf : HypIndex 1 ε → K := fun i => match i with
    | .inr (.inr _) => 1
    | _ => 0
  let β : HypIndex 1 ε → K := fun i => match i with
    | .inr (.inl l) => σ (a l)
    | _ => 0
  let U : Matrix (HypIndex 1 ε) (Fin 2) K := Matrix.of fun i => ![α i, δe i]
  let V : Matrix (Fin 2) (HypIndex 1 ε) K := Matrix.of ![δf, β]
  have hE : eichM σ a c = 1 + U * V := by
    ext i j
    rcases i with i | k | i <;> rcases j with j | l | j <;>
      simp [eichM, U, V, α, δe, δf, β, mul_apply, Fin.sum_univ_two, one_apply, Fin.eq_zero]
  have hVU : V * U = !![0, 0; ∑ k, σ (a k) * a k, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, V, α, δe, δf, β, mul_apply, Fintype.sum_sum_type]
  rw [hE, det_one_add_mul_comm, hVU, det_fin_two]
  simp

theorem eichM_mul_eichM_inv [CharP K 2] (σ : K →+* K) (a : Fin ε → K) (c : K) :
    eichM σ a c * eichM σ a (c + ∑ k, σ (a k) * a k) = 1 := by
  have h0 : a + a = 0 := funext fun k => CharTwo.add_self_eq_zero (a k)
  have h1 : c + (c + ∑ k, σ (a k) * a k) + ∑ k, σ (a k) * a k = 0 := by
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]
  rw [eichM_mul, h0, h1, eichM_zero]

theorem eichM_inv_mul_eichM [CharP K 2] (σ : K →+* K) (a : Fin ε → K) (c : K) :
    eichM σ a (c + ∑ k, σ (a k) * a k) * eichM σ a c = 1 := by
  have h0 : a + a = 0 := funext fun k => CharTwo.add_self_eq_zero (a k)
  have h1 : c + ∑ k, σ (a k) * a k + c + ∑ k, σ (a k) * a k = 0 := by
    rw [add_right_comm c _ c, CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]
  rw [eichM_mul, h0, h1, eichM_zero]

@[expose] def blkZM (C : Matrix (Fin ε) (Fin ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K :=
  fromBlocks 1 0 0 (fromBlocks C 0 0 1)

theorem blkZM_mul (C D : Matrix (Fin ε) (Fin ε) K) : blkZM C * blkZM D = blkZM (C * D) := by
  simp [blkZM, fromBlocks_multiply]

theorem blkZM_one : blkZM (1 : Matrix (Fin ε) (Fin ε) K) = 1 := by
  simp [blkZM, fromBlocks_one]

theorem blkZM_det (C : Matrix (Fin ε) (Fin ε) K) : (blkZM C).det = C.det := by
  rw [blkZM, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]
  simp

theorem blkZM_isometry (σ : K →+* K) {C : Matrix (Fin ε) (Fin ε) K}
    (hC : (C.map σ)ᵀ * C = 1) :
    ((blkZM C).map σ)ᵀ * hypGram 1 ε K * blkZM C = hypGram 1 ε K := by
  ext i j
  rcases i with i | k | i <;> rcases j with j | l | j <;>
    simp [blkZM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero, hypGram_apply, hypPartner]
  have := congrFun (congrFun hC k) l
  simp only [mul_apply, transpose_apply, map_apply, one_apply] at this
  rw [this]
  simp only [eq_comm]

theorem blkZM_mul_eichM (σ : K →+* K) {C : Matrix (Fin ε) (Fin ε) K}
    (hC : (C.map σ)ᵀ * C = 1) (a : Fin ε → K) (c : K) :
    blkZM C * eichM σ a c = eichM σ (C *ᵥ a) c * blkZM C := by
  ext i j
  rcases i with i | k | i <;> rcases j with j | l | j <;>
    simp [blkZM, eichM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero, mulVec, dotProduct]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h2 : ∀ x, ∑ m, σ (C m x) * σ (a x) * C m l = σ (a x) * if x = l then 1 else 0 := by
    intro x
    have := congrFun (congrFun hC x) l
    simp only [mul_apply, transpose_apply, map_apply, one_apply] at this
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  simp [h2]

section Group

variable {f : ℕ} (h : UnitaryFieldData 2 f K)

section Eich

variable [CharP K 2]

@[expose] noncomputable def eichGL (a : Fin ε → K) (c : K) : GL (HypIndex 1 ε) K :=
  ⟨eichM h.bar a c, eichM h.bar a (c + ∑ k, h.bar (a k) * a k), eichM_mul_eichM_inv _ a c,
    eichM_inv_mul_eichM _ a c⟩

theorem eichGL_mem {a : Fin ε → K} {c : K} (hc : c + h.bar c = ∑ k, h.bar (a k) * a k) :
    eichGL h a c ∈ hypSU h 1 ε :=
  mem_hypSU.mpr ⟨eichM_isometry h.bar h.bar_bar a hc, eichM_det _ a c⟩

@[expose] noncomputable def eich {a : Fin ε → K} {c : K}
    (hc : c + h.bar c = ∑ k, h.bar (a k) * a k) : hypSU h 1 ε :=
  ⟨eichGL h a c, eichGL_mem h hc⟩

theorem coe_eich {a : Fin ε → K} {c : K} (hc : c + h.bar c = ∑ k, h.bar (a k) * a k) :
    (((eich h hc : hypSU h 1 ε) : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) =
      eichM h.bar a c := rfl

end Eich

@[expose] def blkZGL (C : GL (Fin ε) K) : GL (HypIndex 1 ε) K :=
  ⟨blkZM C, blkZM (C⁻¹ : GL (Fin ε) K), by
    rw [blkZM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blkZM_one], by
    rw [blkZM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, blkZM_one]⟩

theorem coe_blkZGL (C : GL (Fin ε) K) :
    ((blkZGL C : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) =
      blkZM C := rfl

theorem blkZGL_mem {C : GL (Fin ε) K} (hC : C ∈ StatedSU ε (2 ^ f) K) :
    blkZGL C ∈ hypSU h 1 ε := by
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).mp hC
  exact mem_hypSU.mpr ⟨blkZM_isometry h.bar hu, by rw [coe_blkZGL, blkZM_det, hdet]⟩

@[expose] noncomputable def blkZHom : StatedSU ε (2 ^ f) K →* hypSU h 1 ε where
  toFun C := ⟨blkZGL C, blkZGL_mem h C.2⟩
  map_one' := Subtype.ext (Units.ext (by
    simp only [OneMemClass.coe_one, Units.val_one, coe_blkZGL, blkZM_one]))
  map_mul' C D := Subtype.ext (Units.ext (by
    simp only [Subgroup.coe_mul, Units.val_mul, coe_blkZGL, blkZM_mul]))

theorem coe_blkZHom (C : StatedSU ε (2 ^ f) K) :
    (((blkZHom h C : hypSU h 1 ε) : GL (HypIndex 1 ε) K) :
      Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) = blkZM ((C : GL (Fin ε) K) : Matrix _ _ K) := rfl

abbrev stabE : Subgroup (hypSU h 1 ε) :=
  MulAction.stabilizer (hypSU h 1 ε) (Pi.single hE (1 : K) : HypIndex 1 ε → K)

theorem mem_stabE {g : hypSU h 1 ε} :
    g ∈ stabE h ↔ ((g : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) *ᵥ
      (Pi.single hE 1 : HypIndex 1 ε → K) = Pi.single hE 1 :=
  MulAction.mem_stabilizer_iff

theorem eich_mem_stabE [CharP K 2] {a : Fin ε → K} {c : K}
    (hc : c + h.bar c = ∑ k, h.bar (a k) * a k) :
    eich h hc ∈ stabE h := by
  rw [mem_stabE, coe_eich]
  ext i
  rcases i with i | k | i <;> simp [eichM, mulVec, dotProduct, Fintype.sum_sum_type, Fin.eq_zero]

theorem blkZHom_mem_stabE (C : StatedSU ε (2 ^ f) K) : blkZHom h C ∈ stabE h := by
  rw [mem_stabE, coe_blkZHom]
  ext i
  rcases i with i | k | i <;> simp [blkZM, mulVec, dotProduct, Fintype.sum_sum_type, Fin.eq_zero]

end Group

section Stab

variable {f : ℕ} (h : UnitaryFieldData 2 f K)

omit [Field K] in
theorem isom_entry [Field K] {σ : K →+* K} {G : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K}
    (hG : (G.map σ)ᵀ * hypGram 1 ε K * G = hypGram 1 ε K) (i j : HypIndex 1 ε) :
    ∑ k, σ (G k i) * G (hypPartner k) j = hypGram 1 ε K i j := by
  rw [← hG, Matrix.mul_assoc, mul_apply]
  simp only [hypGram_mul_apply, transpose_apply, map_apply]

omit [Field K] in
theorem eq_of_add_eq_zero_two [Field K] [CharP K 2] {x y : K} (hxy : x + y = 0) : x = y :=
  (add_eq_zero_iff_eq_neg.mp hxy).trans (CharTwo.neg_eq y)

theorem exists_eq_eich_mul_blkZHom [CharP K 2] {g : hypSU h 1 ε} (hg : g ∈ stabE h) :
    ∃ (a : Fin ε → K) (c : K) (hc : c + h.bar c = ∑ k, h.bar (a k) * a k)
      (C : StatedSU ε (2 ^ f) K), g = eich h hc * blkZHom h C := by
  have hG := (mem_hypSU.mp g.2).1
  have hdet := (mem_hypSU.mp g.2).2
  have hcol := (mem_stabE h).mp hg
  suffices key : ∃ (a : Fin ε → K) (c : K) (hc : c + h.bar c = ∑ k, h.bar (a k) * a k)
      (C : StatedSU ε (2 ^ f) K), ((g : GL (HypIndex 1 ε) K) : Matrix _ _ K) =
        eichM h.bar a c * blkZM ((C : GL (Fin ε) K) : Matrix _ _ K) by
    obtain ⟨a, c, hc, C, hM⟩ := key
    exact ⟨a, c, hc, C, Subtype.ext (Units.ext hM)⟩
  generalize ((g : GL (HypIndex 1 ε) K) : Matrix (HypIndex 1 ε) (HypIndex 1 ε) K) = G
    at hG hdet hcol ⊢
  have hGe : ∀ k, G k hE = (Pi.single hE 1 : HypIndex 1 ε → K) k := fun k => by
    have := congrFun hcol k
    rwa [mulVec_single_one, col_apply] at this
  have E := isom_entry hG
  have hff : G hF hF = 1 := by
    have := E hE hF
    simpa [Fintype.sum_sum_type, hGe, Fin.eq_zero, hypGram_apply] using this
  have hfz : ∀ l, G hF (.inr (.inl l)) = 0 := fun l => by
    have := E hE (.inr (.inl l))
    simpa [Fintype.sum_sum_type, hGe, Fin.eq_zero, hypGram_apply] using this
  have hc : G hE hF + h.bar (G hE hF) =
      ∑ k, h.bar (G (.inr (.inl k)) hF) * G (.inr (.inl k)) hF := by
    have := E hF hF
    simp [Fintype.sum_sum_type, Fin.eq_zero, hypGram_apply, hff] at this
    refine eq_of_add_eq_zero_two ?_
    rw [show ∀ x y z : K, x + y + z = y + (z + x) from fun x y z => by ring]
    exact this
  have hez : ∀ l, G hE (.inr (.inl l)) =
      ∑ k, h.bar (G (.inr (.inl k)) hF) * G (.inr (.inl k)) (.inr (.inl l)) := fun l => by
    have := E hF (.inr (.inl l))
    simp [Fintype.sum_sum_type, Fin.eq_zero, hypGram_apply, hff, hfz] at this
    refine eq_of_add_eq_zero_two ?_
    rw [add_comm]
    exact this
  have hCu : ∀ k l, ∑ m, h.bar (G (.inr (.inl m)) (.inr (.inl k))) *
      G (.inr (.inl m)) (.inr (.inl l)) = if k = l then 1 else 0 := fun k l => by
    have := E (.inr (.inl k)) (.inr (.inl l))
    simp [Fintype.sum_sum_type, Fin.eq_zero, hypGram_apply, hfz] at this
    rw [this]
    simp only [eq_comm]
  let C : Matrix (Fin ε) (Fin ε) K := Matrix.of fun k l => G (.inr (.inl k)) (.inr (.inl l))
  have hCapp : ∀ k l, C k l = G (.inr (.inl k)) (.inr (.inl l)) := fun _ _ => rfl
  have hCu' : (C.map h.bar)ᵀ * C = 1 := by
    ext k l
    simp only [mul_apply, transpose_apply, map_apply, one_apply, hCapp]
    exact hCu k l
  have hM : G = eichM h.bar (fun k => G (.inr (.inl k)) hF) (G hE hF) * blkZM C := by
    ext i j
    rcases i with i | k | i <;> rcases j with j | l | j <;>
      simp [eichM, blkZM, mul_apply, Fintype.sum_sum_type, Fin.eq_zero, hGe, hff, hfz, hez,
        hCapp]
  have hdetC : C.det = 1 := by
    rw [← hdet, hM, det_mul, eichM_det, blkZM_det, one_mul]
  let CG : GL (Fin ε) K := ⟨C, (C.map h.bar)ᵀ, mul_eq_one_comm.mp hCu', hCu'⟩
  have hCG : CG ∈ StatedSU ε (2 ^ f) K := (mem_unitarySU_iff h).mpr ⟨hdetC, hCu'⟩
  exact ⟨_, _, hc, ⟨CG, hCG⟩, hM⟩

end Stab

section Comm

variable {σ : K →+* K} [CharP K 2]

theorem eichM_valid {a : Fin ε → K} {c : K}
    (hE : ((eichM σ a c).map σ)ᵀ * hypGram 1 ε K * eichM σ a c = hypGram 1 ε K) :
    c + σ c = ∑ k, σ (a k) * a k := by
  have := isom_entry hE hF hF
  simp [eichM, Fintype.sum_sum_type, Fin.eq_zero, hypGram_apply] at this
  refine eq_of_add_eq_zero_two ?_
  rw [show ∀ x y z : K, x + y + z = y + (z + x) from fun x y z => by ring]
  exact this

theorem eichM_commutator (a a' : Fin ε → K) (c c' : K) :
    eichM σ a c * eichM σ a' c' * eichM σ a (c + ∑ k, σ (a k) * a k) *
        eichM σ a' (c' + ∑ k, σ (a' k) * a' k) =
      eichM σ 0 ((∑ k, σ (a k) * a' k) + ∑ k, σ (a' k) * a k) := by
  rw [eichM_mul, eichM_mul, eichM_mul]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  congr 1
  · funext k
    simp only [Pi.add_apply, Pi.zero_apply]
    linear_combination (a k + a' k) * h2
  · simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    linear_combination (c + c' + (∑ k, σ (a k) * a' k) + (∑ k, σ (a k) * a k) +
      ∑ k, σ (a' k) * a' k) * h2

theorem blkZM_eichM_commutator {C : Matrix (Fin ε) (Fin ε) K} (hC : (C.map σ)ᵀ * C = 1)
    (a : Fin ε → K) (c : K) :
    blkZM C * eichM σ a c * blkZM (C.map σ)ᵀ * eichM σ a (c + ∑ k, σ (a k) * a k) =
      eichM σ (C *ᵥ a + a) ((∑ k, σ (a k) * a k) + ∑ k, σ ((C *ᵥ a) k) * a k) := by
  have hC' : C * (C.map σ)ᵀ = 1 := mul_eq_one_comm.mp hC
  rw [blkZM_mul_eichM σ hC, Matrix.mul_assoc (eichM σ (C *ᵥ a) c), blkZM_mul, hC', blkZM_one,
    Matrix.mul_one, eichM_mul]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  congr 1
  linear_combination c * h2

end Comm

end CFSG.ComponentClassification.RankTwoClassical.URigid
