module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

@[expose] def eBlk (n : ℕ) (hn : 4 ≤ n) : Fin n ≃ (Fin 2 × Fin 2) ⊕ Fin (n - 4) :=
  (finCongr (by omega : n = 4 + (n - 4))).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr ((finCongr (by norm_num : 4 = 2 * 2)).trans finProdFinEquiv.symm)
        (Equiv.refl _)))

@[expose] def blkMat (n : ℕ) (hn : 4 ≤ n) (g : Fin 2 → Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n) (Fin n) K :=
  (fromBlocks (blockDiagonal g) 0 0 1 : Matrix ((Fin 2 × Fin 2) ⊕ Fin (n - 4))
    ((Fin 2 × Fin 2) ⊕ Fin (n - 4)) K).submatrix (eBlk n hn) (eBlk n hn)

theorem blkMat_mul (n : ℕ) (hn : 4 ≤ n) (g g' : Fin 2 → Matrix (Fin 2) (Fin 2) K) :
    blkMat n hn g * blkMat n hn g' = blkMat n hn (g * g') := by
  unfold blkMat
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
  rw [← blockDiagonal_mul]
  rfl

theorem blkMat_one (n : ℕ) (hn : 4 ≤ n) :
    blkMat n hn (1 : Fin 2 → Matrix (Fin 2) (Fin 2) K) = 1 := by
  unfold blkMat
  rw [blockDiagonal_one, fromBlocks_one, Matrix.submatrix_one_equiv]

theorem det_blkMat (n : ℕ) (hn : 4 ≤ n) (g : Fin 2 → Matrix (Fin 2) (Fin 2) K) :
    (blkMat n hn g).det = ∏ k, (g k).det := by
  unfold blkMat
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, det_blockDiagonal,
    Matrix.det_one, mul_one]

theorem blkMat_map_transpose (n : ℕ) (hn : 4 ≤ n) (φ : K → K) (hφ : φ 0 = 0) (hφ1 : φ 1 = 1)
    (g : Fin 2 → Matrix (Fin 2) (Fin 2) K) :
    ((blkMat n hn g).map φ)ᵀ = blkMat n hn (fun k => ((g k).map φ)ᵀ) := by
  unfold blkMat
  rw [← Matrix.submatrix_map, Matrix.transpose_submatrix, Matrix.fromBlocks_map,
    Matrix.fromBlocks_transpose, blockDiagonal_map _ _ hφ, blockDiagonal_transpose]
  simp [Matrix.map_one _ hφ hφ1, Matrix.map_zero _ hφ]

@[expose] def idx (n : ℕ) (hn : 4 ≤ n) (a k : Fin 2) : Fin n := (eBlk n hn).symm (Sum.inl (a, k))

theorem idx_injective (n : ℕ) (hn : 4 ≤ n) (k : Fin 2) :
    Function.Injective fun a : Fin 2 => idx n hn a k := by
  intro a b h
  have := (eBlk n hn).symm.injective h
  simpa using this

theorem blkMat_idx (n : ℕ) (hn : 4 ≤ n) (g : Fin 2 → Matrix (Fin 2) (Fin 2) K) (a b k k' : Fin 2) :
    blkMat n hn g (idx n hn a k) (idx n hn b k') = if k = k' then g k a b else 0 := by
  simp [blkMat, idx, blockDiagonal_apply]

@[expose] def blkMonoidHom (n : ℕ) (hn : 4 ≤ n) :
    (Fin 2 → Matrix (Fin 2) (Fin 2) K) →* Matrix (Fin n) (Fin n) K where
  toFun := blkMat n hn
  map_one' := blkMat_one n hn
  map_mul' g g' := (blkMat_mul n hn g g').symm

theorem blkMat_eq_scalar (n : ℕ) (hn : 4 ≤ n) (g : Fin 2 → Matrix (Fin 2) (Fin 2) K) (c : K)
    (h : blkMat n hn g = Matrix.scalar (Fin n) c) (k : Fin 2) : g k = Matrix.scalar (Fin 2) c := by
  ext a b
  have := congrFun (congrFun h (idx n hn a k)) (idx n hn b k)
  rw [blkMat_idx] at this
  simp only [ite_true] at this
  rw [this]
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, (idx_injective n hn k).eq_iff]

@[expose] def blkHom (n : ℕ) (hn : 4 ≤ n) : (Fin 2 → GL (Fin 2) K) →* GL (Fin n) K :=
  (Units.map (blkMonoidHom (K := K) n hn)).comp (MulEquiv.piUnits.symm).toMonoidHom

theorem coe_blkHom (n : ℕ) (hn : 4 ≤ n) (g : Fin 2 → GL (Fin 2) K) :
    ((blkHom n hn g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      blkMat n hn (fun k => (g k : Matrix (Fin 2) (Fin 2) K)) := rfl

section SU2

variable {p f : ℕ}

theorem exists_su2_pair (h : UnitaryFieldData p f K) :
    ∃ a b : K, a + h.bar a = -1 ∧ b * h.bar b = 1 - a * h.bar a := by
  have hm1 : (-1 : K) ∈ h.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, map_neg, map_one]
  obtain ⟨a, ha⟩ := h.traceLin_surjective ⟨-1, hm1⟩
  have ha' : a + h.bar a = -1 := by
    have := congrArg Subtype.val ha
    simpa [UnitaryFieldData.trace] using this
  have hd : (1 - a * h.bar a : K) ∈ h.fixedField :=
    Subfield.sub_mem _ (Subfield.one_mem _) (h.norm_mem_fixedField a)
  obtain ⟨b, hb⟩ := h.normHom_surjective ⟨1 - a * h.bar a, hd⟩
  refine ⟨a, b, ha', ?_⟩
  have := congrArg Subtype.val hb
  simpa [UnitaryFieldData.norm] using this

@[expose] noncomputable def su2Mat (h : UnitaryFieldData p f K) (a b : K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![a, -h.bar b; b, h.bar a]

theorem su2Mat_det (h : UnitaryFieldData p f K) {a b : K} (hb : b * h.bar b = 1 - a * h.bar a) :
    (su2Mat h a b).det = 1 := by
  rw [su2Mat, Matrix.det_fin_two_of]
  linear_combination hb

theorem su2Mat_unitary (h : UnitaryFieldData p f K) {a b : K}
    (hb : b * h.bar b = 1 - a * h.bar a) :
    ((su2Mat h a b).map (· ^ (p ^ f)))ᵀ * su2Mat h a b = 1 := by
  have hbar : ∀ x : K, x ^ (p ^ f) = h.bar x := fun x => (h.bar_apply x).symm
  have e : (su2Mat h a b).map (· ^ (p ^ f)) = (su2Mat h a b).map h.bar := by
    ext i j
    simp [hbar]
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Mat, Matrix.mul_apply, Fin.sum_univ_two, h.bar_bar]
  · linear_combination hb
  · ring
  · ring
  · linear_combination hb

theorem su2Mat_sq (h : UnitaryFieldData p f K) {a b : K} (hab : a + h.bar a = -1)
    (hb : b * h.bar b = 1 - a * h.bar a) :
    su2Mat h a b * su2Mat h a b + su2Mat h a b + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Mat, Matrix.add_apply]
  · linear_combination (-1 : K) * hb + a * hab
  · linear_combination (-(h.bar b)) * hab
  · linear_combination b * hab
  · linear_combination (-1 : K) * hb + h.bar a * hab

theorem su2Mat_cube (h : UnitaryFieldData p f K) {a b : K} (hab : a + h.bar a = -1)
    (hb : b * h.bar b = 1 - a * h.bar a) :
    su2Mat h a b * su2Mat h a b * su2Mat h a b = 1 := by
  have h1 := su2Mat_sq h hab hb
  have h2 : su2Mat h a b * su2Mat h a b = -(su2Mat h a b + 1) := by
    have : su2Mat h a b * su2Mat h a b + (su2Mat h a b + 1) = 0 := by rw [← add_assoc]; exact h1
    exact eq_neg_of_add_eq_zero_left this
  rw [h2, neg_mul, add_mul, one_mul, h2]
  abel

@[expose] noncomputable def su2GL (h : UnitaryFieldData p f K) {a b : K} (hab : a + h.bar a = -1)
    (hb : b * h.bar b = 1 - a * h.bar a) : GL (Fin 2) K :=
  ⟨su2Mat h a b, su2Mat h a b * su2Mat h a b, by
    rw [← mul_assoc]; exact su2Mat_cube h hab hb, su2Mat_cube h hab hb⟩

theorem coe_su2GL (h : UnitaryFieldData p f K) {a b : K} (hab : a + h.bar a = -1)
    (hb : b * h.bar b = 1 - a * h.bar a) :
    ((su2GL h hab hb : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = su2Mat h a b := rfl

theorem su2GL_pow_three (h : UnitaryFieldData p f K) {a b : K} (hab : a + h.bar a = -1)
    (hb : b * h.bar b = 1 - a * h.bar a) : su2GL h hab hb ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_su2GL, pow_succ, pow_two, Units.val_one]
  exact su2Mat_cube h hab hb

theorem su2GL_ne_scalar (h : UnitaryFieldData p f K) (hp3 : p ≠ 3) {a b : K}
    (hab : a + h.bar a = -1) (hb : b * h.bar b = 1 - a * h.bar a) (c : Kˣ) :
    su2GL h hab hb ≠ GeneralLinearGroup.scalar (Fin 2) c := by
  intro hc
  have hm := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hc
  simp only [coe_su2GL, GeneralLinearGroup.coe_scalar] at hm
  have e10 := congrFun (congrFun hm 1) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e00 := congrFun (congrFun hm 0) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp [su2Mat, Matrix.scalar_apply] at e10 e01 e00 e11
  have hb0 : b = 0 := e10
  have hba : h.bar a = a := by rw [e11, ← e00]
  rw [hb0, map_zero, zero_mul, hba] at hb
  rw [hba] at hab
  have h3 : (3 : K) = 0 := by
    have e1 : (a + a) * (a + a) = 1 := by rw [hab]; norm_num
    linear_combination e1 - 4 * hb
  have := h.charP
  have hd : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).1 (by exact_mod_cast h3)
  exact hp3 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1 hd)

end SU2

section Main

variable {p f : ℕ}

@[expose] def IsSU2 (q : ℕ) (R : Matrix (Fin 2) (Fin 2) K) : Prop :=
  (R.map (· ^ q))ᵀ * R = 1 ∧ R.det = 1

theorem isSU2_one (q : ℕ) (hq : q ≠ 0) : IsSU2 q (1 : Matrix (Fin 2) (Fin 2) K) := by
  refine ⟨?_, Matrix.det_one⟩
  rw [Matrix.map_one (fun x : K => x ^ q) (zero_pow hq) (one_pow q), Matrix.transpose_one,
    Matrix.one_mul]

theorem blkHom_mem_statedSU (n : ℕ) (hn : 4 ≤ n) {q : ℕ} (hq : q ≠ 0)
    (g : Fin 2 → GL (Fin 2) K)
    (hg : ∀ k, IsSU2 q ((g k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) :
    blkHom n hn g ∈ StatedSU n q K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [coe_blkHom, det_blkMat]
    exact Finset.prod_eq_one fun k _ => (hg k).2
  · rw [coe_blkHom, blkMat_map_transpose n hn (· ^ q) (zero_pow hq) (one_pow q), blkMat_mul]
    have : (fun k => (((g k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (· ^ q))ᵀ) *
        (fun k => ((g k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 :=
      funext fun k => (hg k).1
    rw [this, blkMat_one]

omit [Field K] in
theorem pi_mulSingle_apply_su2 {G : Type*} [Monoid G] (j k : Fin 2) (x : G) :
    (Pi.mulSingle j x : Fin 2 → G) k = if k = j then x else 1 := by
  by_cases h : k = j
  · subst h; simp
  · simp [h]

theorem two_le_pRank_three_psu_four {X : Type} [Group X] [Finite X] {n p f : ℕ} (hn : 4 ≤ n)
    (hp3 : p ≠ 3) (hC : StatedClassicalModel X .PSU n p f) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hC
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, hab, hb⟩ := exists_su2_pair h
  set r := su2GL h hab hb with hr
  have hq : p ^ f ≠ 0 := (pow_pos hp.pos f).ne'
  have hrS : IsSU2 (p ^ f) ((r : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    ⟨su2Mat_unitary h hb, su2Mat_det h hb⟩
  have hS : ∀ j k : Fin 2, IsSU2 (p ^ f)
      (((Pi.mulSingle j r : Fin 2 → GL (Fin 2) K) k : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := by
    intro j k
    rw [pi_mulSingle_apply_su2]
    split_ifs
    · exact hrS
    · rw [Units.val_one]; exact isSU2_one _ hq
  set A := blkHom n hn (Pi.mulSingle 0 r) with hA
  set B := blkHom n hn (Pi.mulSingle 1 r) with hB
  have hAS : A ∈ StatedSU n (p ^ f) K := blkHom_mem_statedSU n hn hq _ (hS 0)
  have hBS : B ∈ StatedSU n (p ^ f) K := blkHom_mem_statedSU n hn hq _ (hS 1)
  have hpow3 : ∀ j : Fin 2, (Pi.mulSingle j r : Fin 2 → GL (Fin 2) K) ^ 3 = 1 := by
    intro j
    rw [← Pi.mulSingle_pow, su2GL_pow_three, Pi.mulSingle_one]
  have hA3 : A ^ 3 = 1 := by
    rw [hA, ← map_pow, hpow3, map_one]
  have hB3 : B ^ 3 = 1 := by
    rw [hB, ← map_pow, hpow3, map_one]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hcP : (Pi.mulSingle (0 : Fin 2) r : Fin 2 → GL (Fin 2) K) *
      (Pi.mulSingle (1 : Fin 2) r : Fin 2 → GL (Fin 2) K) =
      (Pi.mulSingle (1 : Fin 2) r : Fin 2 → GL (Fin 2) K) *
      (Pi.mulSingle (0 : Fin 2) r : Fin 2 → GL (Fin 2) K) := by
    funext k
    fin_cases k <;> simp [Pi.mul_apply]
  have hcomm : A * B = B * A := by
    rw [hA, hB, ← map_mul, ← map_mul, hcP]
  have hns : ∀ c : Kˣ, ¬ (((r : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.scalar (Fin 2) (c : K)) := fun c hc =>
    su2GL_ne_scalar h hp3 hab hb c (Units.ext (by rw [GeneralLinearGroup.coe_scalar]; exact hc))
  have hxA : A ∉ StatedScalars (Fin n) K := by
    rintro ⟨c, hc⟩
    have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
    simp only [GeneralLinearGroup.coe_scalar, hA, coe_blkHom] at h1
    have h2 := blkMat_eq_scalar n hn _ (c : K) h1.symm 0
    exact hns c (by simpa [pi_mulSingle_apply_su2] using h2)
  have hyB : ∀ (m : ℕ), ∀ c ∈ StatedScalars (Fin n) K, A ^ m * c ≠ B := by
    rintro m _ ⟨c, rfl⟩ hmc
    have hAm : A ^ m = blkHom n hn (Pi.mulSingle 0 (r ^ m)) := by
      rw [hA, ← map_pow, ← Pi.mulSingle_pow]
    have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hmc
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hAm, hB, coe_blkHom] at h1
    apply hns c
    ext a' b'
    have h2 := congrFun (congrFun h1 (idx n hn a' 1)) (idx n hn b' 1)
    rw [Matrix.scalar_apply, Matrix.mul_diagonal, blkMat_idx, blkMat_idx] at h2
    simp only [pi_mulSingle_apply_su2] at h2
    simp at h2
    rw [← h2]
    by_cases hab' : a' = b'
    · subst hab'; simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, Matrix.one_apply, hab']
  have key := CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_statedProj
    (H := StatedSU n (p ^ f) K) (p := 3) hAS hBS hA3 hB3 ⟨1, one_mem _, by
      rw [one_mul]; exact hcomm⟩ hxA hyB
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact key

end Main

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
