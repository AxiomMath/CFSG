module

public import CFSG.Open.StatedAPI
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM10

open CFSG.Open CFSG.Open.StatedAPI Matrix

variable {K : Type} [Field K]

theorem three_eq_zero_of_natCard_eq_27 [Finite K] (hK : Nat.card K = 27) : (3 : K) = 0 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h
  have h3 : (3 : K) ^ 3 = 0 := by
    rw [show (3 : K) ^ 3 = ((27 : ℕ) : K) by norm_num]
    exact h
  exact (pow_eq_zero_iff (by norm_num)).1 h3

def uMat (a b : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 1 (Matrix.diagonal ![a, b]) 0 1

def tMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks (Matrix.diagonal ![-1, 1]) 0 0 (Matrix.diagonal ![-1, 1])

abbrev jMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := Matrix.fromBlocks 0 1 (-1) 0

theorem diag_neg_one_one_mul_self :
    Matrix.diagonal (![-1, 1] : Fin 2 → K) * Matrix.diagonal ![-1, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_mul_diagonal]

theorem uMat_mul_uMat (a b a' b' : K) : uMat a b * uMat a' b' = uMat (a + a') (b + b') := by
  have hS : Matrix.diagonal ![a', b'] + Matrix.diagonal ![a, b] =
      Matrix.diagonal ![a + a', b + b'] := by
    rw [Matrix.diagonal_add]
    congr 1
    ext i
    fin_cases i <;> simp [add_comm]
  unfold uMat
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [hS]

theorem uMat_zero_zero : uMat (0 : K) 0 = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [uMat]

theorem uMat_mul_uMat_neg (a b : K) : uMat a b * uMat (-a) (-b) = 1 := by
  rw [uMat_mul_uMat, add_neg_cancel, add_neg_cancel, uMat_zero_zero]

theorem uMat_neg_mul_uMat (a b : K) : uMat (-a) (-b) * uMat a b = 1 := by
  rw [uMat_mul_uMat, neg_add_cancel, neg_add_cancel, uMat_zero_zero]

theorem tMat_mul_tMat : tMat (K := K) * tMat = 1 := by
  unfold tMat
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [diag_neg_one_one_mul_self, Matrix.fromBlocks_one]

def uGL (a b : K) : GL (Fin 2 ⊕ Fin 2) K :=
  ⟨uMat a b, uMat (-a) (-b), uMat_mul_uMat_neg a b, uMat_neg_mul_uMat a b⟩

def tGL : GL (Fin 2 ⊕ Fin 2) K :=
  ⟨tMat, tMat, tMat_mul_tMat, tMat_mul_tMat⟩

theorem transpose_uMat (a b : K) :
    (uMat a b)ᵀ = Matrix.fromBlocks 1 0 (Matrix.diagonal ![a, b]) 1 := by
  unfold uMat
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.diagonal_transpose]

theorem uMat_mem_sp (a b : K) : (uMat a b)ᵀ * jMat * uMat a b = jMat := by
  rw [transpose_uMat]
  unfold uMat jMat
  simp [Matrix.fromBlocks_multiply]

theorem tMat_mem_sp : (tMat (K := K))ᵀ * jMat * tMat = jMat := by
  have hT : (tMat (K := K))ᵀ = tMat := by
    unfold tMat
    rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.diagonal_transpose]
  rw [hT]
  unfold tMat jMat
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, zero_add, add_zero, neg_zero]
  rw [diag_neg_one_one_mul_self]

theorem uGL_mem_sp (a b : K) : uGL a b ∈ StatedSp 2 K :=
  mem_statedSp_iff.2 (uMat_mem_sp a b)

theorem tGL_mem_sp : (tGL (K := K)) ∈ StatedSp 2 K :=
  mem_statedSp_iff.2 tMat_mem_sp

def tS : StatedSp 2 K := ⟨tGL, tGL_mem_sp⟩

def uS (a b : K) : StatedSp 2 K := ⟨uGL a b, uGL_mem_sp a b⟩

theorem tS_mul_tS : tS (K := K) * tS = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one]
  exact Units.ext tMat_mul_tMat

theorem uMat_mul_tMat (a b : K) : uMat a b * tMat = tMat * uMat a b := by
  have hc : Matrix.diagonal (![a, b] : Fin 2 → K) * Matrix.diagonal ![-1, 1] =
      Matrix.diagonal ![-1, 1] * Matrix.diagonal ![a, b] := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm]
  unfold uMat tMat
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [hc]

noncomputable def proj : StatedSp 2 K →* StatedProj (StatedSp 2 K) := QuotientGroup.mk' _

noncomputable def eU (a b : K) : StatedProj (StatedSp 2 K) := proj (uS a b)

theorem eU_mul (a b a' b' : K) : eU (a + a') (b + b') = eU a b * eU a' b' := by
  unfold eU
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  exact (uMat_mul_uMat a b a' b').symm

noncomputable def ev : Multiplicative (K × K) →* StatedProj (StatedSp 2 K) :=
  MonoidHom.mk' (fun x => eU (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2) (fun x y => by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    exact eU_mul _ _ _ _)

theorem eU_eq_one {a b : K} (h : eU a b = 1) : a = 0 ∧ b = 0 := by
  unfold eU at h
  have hmem := (QuotientGroup.eq_one_iff _).1 h
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hmem
  have e1 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inr 0)) hc
  have e2 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 1) (Sum.inr 1)) hc
  simp [uGL, uMat, Matrix.GeneralLinearGroup.coe_scalar] at e1 e2
  exact ⟨e1.symm, e2.symm⟩

theorem ev_injective : Function.Injective (ev (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : eU (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 = 1 := hx
  obtain ⟨h1, h2⟩ := eU_eq_one hx'
  exact toAdd_eq_zero.1 (Prod.ext h1 h2)

theorem card_ev_range [Finite K] (hK : Nat.card K = 27) :
    Nat.card (ev (K := K)).range = 3 ^ 6 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (ev_injective (K := K))).toEquiv]
  have h1 : Nat.card (Multiplicative (K × K)) = Nat.card (K × K) :=
    (Nat.card_congr Multiplicative.ofAdd).symm
  rw [h1, Nat.card_prod, hK]
  norm_num

theorem exists_involution_and_elemAbelian [Finite K] (hK : Nat.card K = 27) :
    ∃ (t : StatedProj (StatedSp 2 K)) (E : Subgroup (StatedProj (StatedSp 2 K))),
      t ^ 2 = 1 ∧ t ≠ 1 ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 ∧
        ∀ e ∈ E, e * t = t * e := by
  have h3 := three_eq_zero_of_natCard_eq_27 hK
  refine ⟨proj tS, ev.range, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sq, ← map_mul, tS_mul_tS, map_one]
  · intro h
    have hmem := (QuotientGroup.eq_one_iff _).1 h
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hmem
    have e1 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inl 0)) hc
    have e2 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 1) (Sum.inl 1)) hc
    have e1' : ((c : Kˣ) : K) = -1 := by simpa [tS, tGL, tMat] using e1
    have e2' : ((c : Kˣ) : K) = 1 := by simpa [tS, tGL, tMat] using e2
    have h2 : (2 : K) = 0 := by
      have h : (-1 : K) = 1 := e1'.symm.trans e2'
      linear_combination -h
    have h1 : (1 : K) = 0 := by linear_combination h3 - h2
    exact one_ne_zero h1
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨u, hu⟩ := a.2
      obtain ⟨v, hv⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hv, ← map_mul, ← map_mul, mul_comm u v]
    · intro x hx
      obtain ⟨u, rfl⟩ := hx
      rw [← map_pow]
      have hu : u ^ 3 = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one]
        ext <;> simp [h3]
      rw [hu, map_one]
  · rw [card_ev_range hK]
  · rintro _ ⟨x, rfl⟩
    show eU (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 * proj tS =
      proj tS * eU (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2
    unfold eU
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    exact uMat_mul_tMat _ _

end CFSG.LocalAnalysis.GLTheoremA.SFM10

end
