module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenSu2
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutNF

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup Matrix CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan

namespace GenLocU4Out

open GenLocU4Basic

variable {K : Type} [Field K] {p f : ℕ}

theorem diag_conj_eq (e : Fin 2 → K) (he : e 0 = e 1) (h0 : e 0 ≠ 0) (X : Matrix (Fin 2) (Fin 2) K) :
    Matrix.diagonal e * X * Matrix.diagonal (fun x => (e x)⁻¹) = X := by
  have hall : ∀ i : Fin 2, e i = e 0 := by
    intro i
    fin_cases i
    · rfl
    · exact he.symm
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hall i, hall j]
  field_simp

theorem diag_conj_ne (e : Fin 2 → K) (he : e 0 = 1 ∨ e 0 = -1) (hb : e 1 = -e 0) (X : Matrix (Fin 2) (Fin 2) K) :
    Matrix.diagonal e * X * Matrix.diagonal (fun x => (e x)⁻¹) = Y2 * X * Y2 := by
  rw [Matrix.eta_fin_two X, Y2_eq]
  ext i j
  rcases he with h | h <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, h, hb]

section Blocks

variable [Finite K] [Fact p.Prime] [CharP K p]

theorem map_blockMat_pow (i : ℕ) (A : Matrix (Fin 2) (Fin 2) K) :
    (blockMat 4 i A).map (· ^ (p ^ f)) = blockMat 4 i (A.map (· ^ (p ^ f))) := by
  have hσ : (⇑(unitaryInvolution K p f) : K → K) = fun x => x ^ (p ^ f) :=
    funext (unitaryInvolution_apply K p f)
  have := GenLocU3Blk.map_blockMat (unitaryInvolution K p f) (m := 4) i A
  rwa [hσ] at this

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem fixIn_block {q : ℕ} (d : Fin 4 → K) (hd : ∀ k, d k = 1 ∨ d k = -1) (i : Fin 3)
    (g : ↥(StatedSU 4 q K)) (X : Matrix (Fin 2) (Fin 2) K)
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = blockMat 4 i.val X)
    (hX : d (GenLocU4Gen.idx4 i 0) = d (GenLocU4Gen.idx4 i 1) ∨
      (d (GenLocU4Gen.idx4 i 1) = -d (GenLocU4Gen.idx4 i 0) ∧ Y2 * X = X * Y2)) :
    FixIn (Matrix.diagonal d) g := by
  have hd0 : ∀ k, d k ≠ 0 := by
    intro k
    rcases hd k with h | h <;> simp [h]
  have key := GenLocU4Gen.diag_mul_blockMat4 d hd0 i X
  have hconj : Matrix.diagonal (fun x => d (GenLocU4Gen.idx4 i x)) * X *
      Matrix.diagonal (fun x => (d (GenLocU4Gen.idx4 i x))⁻¹) = X := by
    rcases hX with he | ⟨hb, hc⟩
    · exact diag_conj_eq (fun x => d (GenLocU4Gen.idx4 i x)) he (hd0 _) X
    · rw [diag_conj_ne (fun x => d (GenLocU4Gen.idx4 i x)) (hd _) hb X, hc, Matrix.mul_assoc, Y2_mul,
        Matrix.mul_one]
  unfold FixIn
  rw [hg, key, hconj]

theorem fixOut_block (D : Fin 4 → K) (hD : ∀ k, D k = 1 ∨ D k = -1) (i : Fin 3)
    (g : ↥(StatedSU 4 (p ^ f) K)) (X : Matrix (Fin 2) (Fin 2) K)
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = blockMat 4 i.val X)
    (hX : (D (GenLocU4Gen.idx4 i 0) = D (GenLocU4Gen.idx4 i 1) ∧ X.map (· ^ (p ^ f)) = X) ∨
      (D (GenLocU4Gen.idx4 i 1) = -D (GenLocU4Gen.idx4 i 0) ∧ Y2 * X.map (· ^ (p ^ f)) * Y2 = X)) :
    FixOut (p ^ f) (Matrix.diagonal D) g := by
  have hD0 : ∀ k, D k ≠ 0 := by
    intro k
    rcases hD k with h | h <;> simp [h]
  have key := GenLocU4Gen.diag_mul_blockMat4 D hD0 i (X.map (· ^ (p ^ f)))
  have hconj : Matrix.diagonal (fun x => D (GenLocU4Gen.idx4 i x)) * X.map (· ^ (p ^ f)) *
      Matrix.diagonal (fun x => (D (GenLocU4Gen.idx4 i x))⁻¹) = X := by
    rcases hX with ⟨he, hc⟩ | ⟨hb, hc⟩
    · rw [diag_conj_eq (fun x => D (GenLocU4Gen.idx4 i x)) he (hD0 _) _]
      exact hc
    · rw [diag_conj_ne (fun x => D (GenLocU4Gen.idx4 i x)) (hD _) hb _]
      exact hc
  unfold FixOut
  rw [hg, map_blockMat_pow, key, hconj]

theorem coe_frameBlock_one (hK : Nat.card K = (p ^ f) ^ 2)
    (hP : (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1) (i : Fin 3) (x : Su K p f 2) :
    (((GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP i x : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = blockMat 4 i.val ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  rw [GenLocU4Gen.coe_frameBlock]
  simp only [inv_one, mul_one, one_mul]
  exact coe_coe_blockEmb2 3 i x

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem tT_mul_tS : (tT : Matrix (Fin 4) (Fin 4) K) * tS = Matrix.diagonal ![1, -1, -1, 1] := by
  unfold tT tS
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  fin_cases k <;> simp

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem mD_mul_tT : (mD : Matrix (Fin 4) (Fin 4) K) * tT = Matrix.diagonal ![1, 1, -1, 1] := by
  unfold mD tT
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  fin_cases k <;> simp

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem mD_mul_tS : (mD : Matrix (Fin 4) (Fin 4) K) * tS = Matrix.diagonal ![1, -1, 1, 1] := by
  unfold mD tS
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  fin_cases k <;> simp

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem pm_of_entries (v : Fin 4 → K) (h0 : v 0 = 1 ∨ v 0 = -1) (h1 : v 1 = 1 ∨ v 1 = -1)
    (h2 : v 2 = 1 ∨ v 2 = -1) (h3 : v 3 = 1 ∨ v 3 = -1) : ∀ k, v k = 1 ∨ v k = -1 := by
  intro k
  fin_cases k <;> assumption

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem pmT : ∀ k, (![1, 1, -1, -1] : Fin 4 → K) k = 1 ∨ (![1, 1, -1, -1] : Fin 4 → K) k = -1 :=
  pm_of_entries _ (by simp) (by simp) (by simp) (by simp)

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem pmS : ∀ k, (![1, -1, 1, -1] : Fin 4 → K) k = 1 ∨ (![1, -1, 1, -1] : Fin 4 → K) k = -1 :=
  pm_of_entries _ (by simp) (by simp) (by simp) (by simp)

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem pmM : ∀ k, (![1, 1, 1, -1] : Fin 4 → K) k = 1 ∨ (![1, 1, 1, -1] : Fin 4 → K) k = -1 :=
  pm_of_entries _ (by simp) (by simp) (by simp) (by simp)

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem pmTS : ∀ k, (![1, -1, -1, 1] : Fin 4 → K) k = 1 ∨ (![1, -1, -1, 1] : Fin 4 → K) k = -1 :=
  pm_of_entries _ (by simp) (by simp) (by simp) (by simp)

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem pmMT : ∀ k, (![1, 1, -1, 1] : Fin 4 → K) k = 1 ∨ (![1, 1, -1, 1] : Fin 4 → K) k = -1 :=
  pm_of_entries _ (by simp) (by simp) (by simp) (by simp)

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem pmMS : ∀ k, (![1, -1, 1, 1] : Fin 4 → K) k = 1 ∨ (![1, -1, 1, 1] : Fin 4 → K) k = -1 :=
  pm_of_entries _ (by simp) (by simp) (by simp) (by simp)

theorem db_block0
    (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq4 : p ^ f % 4 = 1)
    (hP : (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1) (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K))
    (H1 : ∀ g, FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → FixIn (tS : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (H2 : ∀ g, FixOut (p ^ f) (mD : Matrix (Fin 4) (Fin 4) K) g → FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (H6 : ∀ g, FixOut (p ^ f) ((mD : Matrix (Fin 4) (Fin 4) K) * tS) g →
      FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) :
    ∀ x : Su K p f 2, GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 0 x ∈ Γ := by
  have hT0 : ∀ x : Su K p f 2, FixIn (tT : Matrix (Fin 4) (Fin 4) K)
      (GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 0 x) := fun x =>
    fixIn_block _ pmT 0 _ _ (coe_frameBlock_one hK hP 0 x) (Or.inl (by simp [GenLocU4Gen.idx4]))
  refine su2_gen_of_three hp2 hK hq4 (GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 0) Γ ?_ ?_ ?_
  · intro x hc
    exact H1 _ (hT0 x) (fixIn_block _ pmS 0 _ _ (coe_frameBlock_one hK hP 0 x)
      (Or.inr ⟨by simp [GenLocU4Gen.idx4], hc⟩))
  · intro x hc
    exact H2 _ (fixOut_block _ pmM 0 _ _ (coe_frameBlock_one hK hP 0 x)
      (Or.inl ⟨by simp [GenLocU4Gen.idx4], hc⟩)) (hT0 x)
  · intro x hc
    refine H6 _ ?_ (hT0 x)
    rw [mD_mul_tS]
    exact fixOut_block _ pmMS 0 _ _ (coe_frameBlock_one hK hP 0 x) (Or.inr ⟨by simp [GenLocU4Gen.idx4], hc⟩)

theorem db_block1
    (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq4 : p ^ f % 4 = 1)
    (hP : (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1) (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K))
    (H1 : ∀ g, FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → FixIn (tS : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (H4 : ∀ g, FixOut (p ^ f) (mD : Matrix (Fin 4) (Fin 4) K) g →
      FixIn ((tT : Matrix (Fin 4) (Fin 4) K) * tS) g → g ∈ Γ)
    (H7 : ∀ g, FixOut (p ^ f) ((mD : Matrix (Fin 4) (Fin 4) K) * tT) g →
      FixOut (p ^ f) ((mD : Matrix (Fin 4) (Fin 4) K) * tS) g → g ∈ Γ) :
    ∀ x : Su K p f 2, GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 1 x ∈ Γ := by
  refine su2_gen_of_three hp2 hK hq4 (GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 1) Γ ?_ ?_ ?_
  · intro x hc
    exact H1 _ (fixIn_block _ pmT 1 _ _ (coe_frameBlock_one hK hP 1 x)
      (Or.inr ⟨by simp [GenLocU4Gen.idx4], hc⟩)) (fixIn_block _ pmS 1 _ _ (coe_frameBlock_one hK hP 1 x)
      (Or.inr ⟨by simp [GenLocU4Gen.idx4], hc⟩))
  · intro x hc
    refine H4 _ (fixOut_block _ pmM 1 _ _ (coe_frameBlock_one hK hP 1 x)
      (Or.inl ⟨by simp [GenLocU4Gen.idx4], hc⟩)) ?_
    rw [tT_mul_tS]
    exact fixIn_block _ pmTS 1 _ _ (coe_frameBlock_one hK hP 1 x) (Or.inl (by simp [GenLocU4Gen.idx4]))
  · intro x hc
    refine H7 _ ?_ ?_
    · rw [mD_mul_tT]
      exact fixOut_block _ pmMT 1 _ _ (coe_frameBlock_one hK hP 1 x) (Or.inr ⟨by simp [GenLocU4Gen.idx4], hc⟩)
    · rw [mD_mul_tS]
      exact fixOut_block _ pmMS 1 _ _ (coe_frameBlock_one hK hP 1 x) (Or.inr ⟨by simp [GenLocU4Gen.idx4], hc⟩)

theorem db_block2
    (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq4 : p ^ f % 4 = 1)
    (hP : (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1) (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K))
    (H1 : ∀ g, FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → FixIn (tS : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (H2 : ∀ g, FixOut (p ^ f) (mD : Matrix (Fin 4) (Fin 4) K) g → FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (H6 : ∀ g, FixOut (p ^ f) ((mD : Matrix (Fin 4) (Fin 4) K) * tS) g →
      FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ) :
    ∀ x : Su K p f 2, GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 2 x ∈ Γ := by
  have hT2 : ∀ x : Su K p f 2, FixIn (tT : Matrix (Fin 4) (Fin 4) K)
      (GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 2 x) := fun x =>
    fixIn_block _ pmT 2 _ _ (coe_frameBlock_one hK hP 2 x) (Or.inl (by simp [GenLocU4Gen.idx4]))
  refine su2_gen_of_three hp2 hK hq4 (GenLocU4Gen.frameBlock hK (1 : GL (Fin 4) K) hP 2) Γ ?_ ?_ ?_
  · intro x hc
    exact H1 _ (hT2 x) (fixIn_block _ pmS 2 _ _ (coe_frameBlock_one hK hP 2 x)
      (Or.inr ⟨by simp [GenLocU4Gen.idx4], hc⟩))
  · intro x hc
    refine H6 _ ?_ (hT2 x)
    rw [mD_mul_tS]
    exact fixOut_block _ pmMS 2 _ _ (coe_frameBlock_one hK hP 2 x) (Or.inl ⟨by simp [GenLocU4Gen.idx4], hc⟩)
  · intro x hc
    exact H2 _ (fixOut_block _ pmM 2 _ _ (coe_frameBlock_one hK hP 2 x)
      (Or.inr ⟨by simp [GenLocU4Gen.idx4], hc⟩)) (hT2 x)

end Blocks

theorem outDbGen
    (K : Type) [Field K] [Finite K] (p f : ℕ) : OutDbGen K p f := by
  intro hp hp2 hK hq4 Γ H1 H2 _ H4 _ H6 H7
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  have hP : (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    simp [Matrix.map_one, zero_pow hq0]
  have b0 := db_block0 hp2 hK hq4 hP Γ H1 H2 H6
  have b1 := db_block1 hp2 hK hq4 hP Γ H1 H4 H7
  have b2 := db_block2 hp2 hK hq4 hP Γ H1 H2 H6
  have hall := GenLocU4Gen.iSup_range_frameBlock hK (1 : GL (Fin 4) K) hP hp2
  refine eq_top_iff.2 ?_
  rw [← hall]
  refine iSup_le fun i => ?_
  rintro _ ⟨x, rfl⟩
  fin_cases i
  · exact b0 x
  · exact b1 x
  · exact b2 x

end GenLocU4Out

end CFSG.GH74.Generic.BProg.B2
