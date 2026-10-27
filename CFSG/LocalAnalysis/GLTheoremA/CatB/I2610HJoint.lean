module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Big
import CFSG.ClassicalInvolution.Asc77.AscSCH19
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer

theorem eq_one_of_skew_commute {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    {d : ι → K} {c t : K} (hc : c ≠ 0) (ht : t ≠ 1) {M : Matrix ι ι K} (hM : IsUnit M)
    (hMD : M * Matrix.diagonal d = t • (Matrix.diagonal d * M)) {g : Matrix ι ι K}
    (hg : ∀ i j, ¬ (d i = c ∧ d j = c) → g i j = (1 : Matrix ι ι K) i j)
    (hgM : g * M = M * g) : g = 1 := by
  have hzero : ∀ i j, d i = c → d j = c → M i j = 0 := by
    intro i j hi hj
    have h := congrFun (congrFun hMD i) j
    rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul] at h
    rw [hi, hj] at h
    have h1 : (1 - t) * (c * M i j) = 0 := by
      rw [sub_mul, one_mul]
      have h' : c * M i j = t * (c * M i j) := by
        rw [mul_comm (M i j) c] at h
        exact h
      exact sub_eq_zero.2 h'
    have h1t : (1 - t) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    have hcM : c * M i j = 0 := (mul_eq_zero.mp h1).resolve_left h1t
    exact (mul_eq_zero.mp hcM).resolve_left hc
  have hgm : ∀ i j, d j = c → (g * M) i j = M i j := by
    intro i j hj
    have h1M : ∀ i j, (∑ k, (1 : Matrix ι ι K) i k * M k j) = M i j := by
      intro i j
      rw [← Matrix.mul_apply, Matrix.one_mul]
    calc (g * M) i j = ∑ k, g i k * M k j := rfl
      _ = ∑ k, (1 : Matrix ι ι K) i k * M k j := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : d k = c
        · simp [hzero k j hk hj]
        · rw [hg i k (fun h => hk h.2)]
      _ = M i j := h1M i j
  have hMg : M * g = M := by
    ext i j
    by_cases hj : d j = c
    · rw [← congrFun (congrFun hgM i) j, hgm i j hj]
    · have hM1 : ∀ i j, (∑ k, M i k * (1 : Matrix ι ι K) k j) = M i j := by
        intro i j
        rw [← Matrix.mul_apply, Matrix.mul_one]
      calc (M * g) i j = ∑ k, M i k * g k j := rfl
        _ = ∑ k, M i k * (1 : Matrix ι ι K) k j := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hg k j (fun h => hj h.2)]
        _ = M i j := hM1 i j
  have h1 : M * g = M * 1 := by rw [hMg, Matrix.mul_one]
  exact IsUnit.mul_left_cancel hM h1

theorem eq_one_of_cube_of_commute_diagonal {n : ℕ} {d : Fin n → F4} {c : F4}
    (ha : ¬ 3 ∣ Fintype.card (Blk d c)) {M : Matrix (Fin n) (Fin n) F4}
    (hMD : M * Matrix.diagonal d = Matrix.diagonal d * M) {μ : F4} (hμ : μ ≠ 0)
    (hM3 : M ^ 3 = μ • (1 : Matrix (Fin n) (Fin n) F4)) : μ = 1 := by
  have hx3 : ∀ x : F4, x ≠ 0 → x ^ 3 = 1 := by decide
  have hzero : ∀ i j, d i ≠ d j → M i j = 0 := fun i j => zero_of_commute_diag hMD
  have hmul : ∀ A B : Matrix (Fin n) (Fin n) F4,
      (∀ i j, d i ≠ d j → A i j = 0) → (∀ i j, d i ≠ d j → B i j = 0) →
      ∀ i j, d i ≠ d j → (A * B) i j = 0 := by
    intro A B hA hB i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : d i = d k
    · have hkj : d k ≠ d j := fun h => hij (hik.trans h)
      rw [hB k j hkj, mul_zero]
    · exact mul_eq_zero_of_left (hA i k hik) _
  have hblk3 : blkM d c (M ^ 3) = blkM d c M ^ 3 := by
    rw [show M ^ 3 = M * M * M by rw [pow_succ, pow_succ, pow_one],
      blkM_mul d c (hmul M M hzero hzero) hzero, blkM_mul d c hzero hzero]
    rw [pow_succ, pow_succ, pow_one]
  have hblkM3 : blkM d c M ^ 3 = μ • (1 : Matrix (Blk d c) (Blk d c) F4) := by
    rw [← hblk3, hM3]
    ext i j
    simp [blkM, Matrix.smul_apply, Matrix.one_apply, Subtype.ext_iff]
  have hdet : (blkM d c M).det ^ 3 = μ ^ Fintype.card (Blk d c) := by
    have h := congrArg Matrix.det hblkM3
    rwa [Matrix.det_pow, Matrix.det_smul, Matrix.det_one, mul_one] at h
  have hdetB : (blkM d c M).det ≠ 0 := by
    intro h0
    have : μ ^ Fintype.card (Blk d c) = 0 := by
      rw [← hdet, h0]
      simp
    exact pow_ne_zero _ hμ this
  have hμa : μ ^ Fintype.card (Blk d c) = 1 := by
    rw [← hdet, hx3 _ hdetB]
  have hμ3 : μ ^ 3 = 1 := hx3 μ hμ
  have hcop : Nat.Coprime (Fintype.card (Blk d c)) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ha).symm
  exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hμa, hμ3⟩

private theorem card_statedSU_four : Nat.card ↥(StatedSU 4 (2 ^ 1) F4) = 25920 := by
  have h := CFSG.ClassicalInvolution.Asc77.SCH.card_statedSU_four (K := F4) (ℓ := 2) (f := 1)
    hF4
  norm_num at h
  exact h

private theorem omega_ne_zero : (F4.ω : F4) ≠ 0 := by decide

private theorem omega_ne_one : (F4.ω : F4) ≠ 1 := by decide

private theorem one_ne_omega : (1 : F4) ≠ F4.ω := fun h => omega_ne_one h.symm

private abbrev indPair (d₁ d₂ : Fin 6 → F4) (a b : F4) (i : Fin 6) : F4 :=
  if (d₁ i, d₂ i) = (a, b) then 1 else F4.ω

private theorem indPair_eq_one_iff (d₁ d₂ : Fin 6 → F4) (a b : F4) (i : Fin 6) :
    indPair d₁ d₂ a b i = 1 ↔ d₁ i = a ∧ d₂ i = b := by
  by_cases h : (d₁ i, d₂ i) = (a, b)
  · have hp : d₁ i = a ∧ d₂ i = b := by simpa using h
    simp [indPair, h, hp]
  · have hp : ¬ (d₁ i = a ∧ d₂ i = b) := fun hp => h (by simpa using hp)
    simp [indPair, h, hp, omega_ne_one]

private theorem indPair_eq_omega_iff (d₁ d₂ : Fin 6 → F4) (a b : F4) (i : Fin 6) :
    indPair d₁ d₂ a b i = F4.ω ↔ ¬ (d₁ i = a ∧ d₂ i = b) := by
  by_cases h : (d₁ i, d₂ i) = (a, b)
  · have hp : d₁ i = a ∧ d₂ i = b := by simpa using h
    simp [indPair, h, hp, one_ne_omega]
  · have hp : ¬ (d₁ i = a ∧ d₂ i = b) := fun hp => h (by simpa using hp)
    simp [indPair, h, hp]

private theorem indPair_ne_zero (d₁ d₂ : Fin 6 → F4) (a b : F4) (i : Fin 6) :
    indPair d₁ d₂ a b i ≠ 0 := by
  by_cases h : (d₁ i, d₂ i) = (a, b) <;> simp [indPair, h, omega_ne_zero]

private theorem card_indPair_one (d₁ d₂ : Fin 6 → F4) (a b : F4) :
    Fintype.card (Blk (indPair d₁ d₂ a b) 1) =
      Fintype.card {i : Fin 6 // d₁ i = a ∧ d₂ i = b} := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun i => indPair_eq_one_iff d₁ d₂ a b i

private theorem det_diagonal_indPair_ne_zero (d₁ d₂ : Fin 6 → F4) (a b : F4) :
    (Matrix.diagonal (indPair d₁ d₂ a b)).det ≠ 0 := by
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => indPair_ne_zero d₁ d₂ a b i

private def indGL (d₁ d₂ : Fin 6 → F4) (a b : F4) : GL (Fin 6) F4 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal (indPair d₁ d₂ a b))
    (det_diagonal_indPair_ne_zero d₁ d₂ a b)

private theorem indGL_val (d₁ d₂ : Fin 6 → F4) (a b : F4) :
    (indGL d₁ d₂ a b : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal (indPair d₁ d₂ a b) :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private theorem commute_diagonal_of_commute_diag_pair {d₁ d₂ : Fin 6 → F4}
    {M : Matrix (Fin 6) (Fin 6) F4}
    (hM₁ : M * Matrix.diagonal d₁ = Matrix.diagonal d₁ * M)
    (hM₂ : M * Matrix.diagonal d₂ = Matrix.diagonal d₂ * M) (φ : F4 × F4 → F4) :
    M * Matrix.diagonal (fun i => φ (d₁ i, d₂ i)) =
      Matrix.diagonal (fun i => φ (d₁ i, d₂ i)) * M := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : (d₁ i, d₂ i) = (d₁ j, d₂ j)
  · rw [h]
    exact mul_comm _ _
  · have hMij : M i j = 0 := by
      by_cases h1 : d₁ i = d₁ j
      · have h2 : d₂ i ≠ d₂ j := fun h2 => h (Prod.ext h1 h2)
        exact zero_of_commute_diag hM₂ h2
      · exact zero_of_commute_diag hM₁ h1
    rw [hMij, zero_mul, mul_zero]

private theorem le_CenD_indGL {D₁ D₂ : GL (Fin 6) F4} {d₁ d₂ : Fin 6 → F4}
    (hD₁ : (D₁ : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d₁)
    (hD₂ : (D₂ : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d₂) (a b : F4) :
    CenD D₁ ⊓ CenD D₂ ≤ CenD (indGL d₁ d₂ a b) := by
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  rw [mem_CenD]
  apply Units.ext
  change mM6 (x : M6) * (indGL d₁ d₂ a b : Matrix (Fin 6) (Fin 6) F4) =
    (indGL d₁ d₂ a b : Matrix (Fin 6) (Fin 6) F4) * mM6 (x : M6)
  rw [indGL_val]
  change mM6 (x : M6) *
      Matrix.diagonal (fun i => if (d₁ i, d₂ i) = (a, b) then 1 else F4.ω) =
    Matrix.diagonal (fun i => if (d₁ i, d₂ i) = (a, b) then 1 else F4.ω) * mM6 (x : M6)
  have hx₁mat : mM6 (x : M6) * Matrix.diagonal d₁ = Matrix.diagonal d₁ * mM6 (x : M6) := by
    have h := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4))
      (mem_CenD.1 hx₁)
    simpa [hD₁, mM6] using h
  have hx₂mat : mM6 (x : M6) * Matrix.diagonal d₂ = Matrix.diagonal d₂ * mM6 (x : M6) := by
    have h := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4))
      (mem_CenD.1 hx₂)
    simpa [hD₂, mM6] using h
  have hcomm := commute_diagonal_of_commute_diag_pair hx₁mat hx₂mat
    (fun p : F4 × F4 => if p = (a, b) then 1 else F4.ω)
  simpa [mM6] using hcomm

private theorem embSU_mem_CenD_of_const_on_block {d e : Fin 6 → F4} {c : F4}
    {D : GL (Fin 6) F4} (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    (hconst : ∀ i j, e i = c → e j = c → d i = d j)
    (A : ↥(StatedSU (Fintype.card (Blk e c)) (2 ^ 1) F4)) : embSU e c A ∈ CenD D := by
  rw [mem_CenD]
  apply Units.ext
  show mM6 (embSU e c A) * (D : Matrix (Fin 6) (Fin 6) F4) =
    (D : Matrix (Fin 6) (Fin 6) F4) * mM6 (embSU e c A)
  rw [hD]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mM6_embSU, extMat_apply]
  by_cases h : e i = c ∧ e j = c
  · rw [dif_pos h]
    have hd : d i = d j := hconst i j h.1 h.2
    rw [hd, mul_comm]
  · rw [dif_neg h]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private theorem exists_c_of_pair_of_ne :
    ∀ a b a' b' : F4, a ^ 3 = 1 → b ^ 3 = 1 → a' ^ 3 = 1 → b' ^ 3 = 1 → a' ≠ a →
      ∃ k : Fin 3, ∃ c : F4, b = c * a ^ (k : ℕ) ∧ b' = c * a' ^ (k : ℕ) := by
  decide

private theorem eq_bot_of_joint_small {D₁ D₂ : GL (Fin 6) F4} {d₁ d₂ : Fin 6 → F4}
    (hD₁ : (D₁ : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d₁)
    (hD₂ : (D₂ : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d₂)
    (hsmall : ∀ a b : F4, Fintype.card {i : Fin 6 // d₁ i = a ∧ d₂ i = b} ≤ 3)
    {J : Subgroup M6} (hJ : J ≤ CenD D₁ ⊓ CenD D₂) (hperf : ⁅J, J⁆ = J) : J = ⊥ := by
  classical
  refine (Subgroup.eq_bot_iff_forall J).2 fun u hu => ?_
  apply Subtype.ext
  apply Units.ext
  ext i j
  change mM6 u i j = (1 : Matrix (Fin 6) (Fin 6) F4) i j
  by_cases hpair : (d₁ i, d₂ i) = (d₁ j, d₂ j)
  · let a := d₁ i
    let b := d₂ i
    have hi1 : indPair d₁ d₂ a b i = 1 :=
      (indPair_eq_one_iff d₁ d₂ a b i).2 (by simp [a, b])
    have hj1 : indPair d₁ d₂ a b j = 1 :=
      (indPair_eq_one_iff d₁ d₂ a b j).2 (by simpa [a, b] using hpair.symm)
    have hJab : J ≤ CenD (indGL d₁ d₂ a b) :=
      hJ.trans (le_CenD_indGL hD₁ hD₂ a b)
    have hcard : Fintype.card (Blk (indPair d₁ d₂ a b) 1) ≤ 3 := by
      rw [card_indPair_one]
      exact hsmall a b
    have h1 := blk_eq_one_of_small (indGL_val d₁ d₂ a b) hJab hperf 1 hcard hu
    have h2 : mM6 u i j =
        (1 : Matrix (Blk (indPair d₁ d₂ a b) 1) (Blk (indPair d₁ d₂ a b) 1) F4)
          ⟨i, hi1⟩ ⟨j, hj1⟩ := by
      have h := congrArg (fun g : GL (Blk (indPair d₁ d₂ a b) 1) F4 =>
          (g : Matrix (Blk (indPair d₁ d₂ a b) 1) (Blk (indPair d₁ d₂ a b) 1) F4)) h1
      have h := congrFun (congrFun h ⟨i, hi1⟩) ⟨j, hj1⟩
      simpa [blkHom_val, blkM] using h
    rw [h2]
    by_cases hij : i = j
    · subst hij
      simp
    · have hsub : (⟨i, hi1⟩ : Blk (indPair d₁ d₂ a b) 1) ≠ ⟨j, hj1⟩ :=
        fun h => hij (congrArg Subtype.val h)
      simp [Matrix.one_apply, hij, hsub]
  · let a := d₁ i
    let b := d₂ i
    have hi1 : indPair d₁ d₂ a b i = 1 :=
      (indPair_eq_one_iff d₁ d₂ a b i).2 (by simp [a, b])
    have hjω : indPair d₁ d₂ a b j = F4.ω := by
      apply (indPair_eq_omega_iff d₁ d₂ a b j).2
      intro hp
      exact hpair (Prod.ext (by simpa [a] using hp.1.symm)
        (by simpa [b] using hp.2.symm))
    have hJab : J ≤ CenD (indGL d₁ d₂ a b) :=
      hJ.trans (le_CenD_indGL hD₁ hD₂ a b)
    have huDab : u ∈ CenD (indGL d₁ d₂ a b) := hJab hu
    have heij : indPair d₁ d₂ a b i ≠ indPair d₁ d₂ a b j := by
      rw [hi1, hjω]
      exact fun h => omega_ne_one h.symm
    have hMij : mM6 u i j = 0 := CenD_zero (indGL_val d₁ d₂ a b) ⟨u, huDab⟩ heij
    have hij : i ≠ j := fun h => hpair (by rw [h])
    rw [hMij, Matrix.one_apply, if_neg hij]

theorem card_pSimple_of_diag_pair {D₁ D₂ : GL (Fin 6) F4} {d₁ d₂ : Fin 6 → F4}
    (hD₁ : (D₁ : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d₁)
    (hD₂ : (D₂ : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d₂)
    (h₁ : ∀ i, d₁ i ^ 3 = 1) (h₂ : ∀ i, d₂ i ^ 3 = 1) (hns : ¬ ∀ i, d₁ i = d₁ 0)
    (hindep : ∀ (k : ℕ) (c : F4), ¬ ∀ i, d₂ i = c * d₁ i ^ k)
    {J : Subgroup M6} (hJ : GLAPComponent 3 (CenD D₁ ⊓ CenD D₂) J) :
    Nat.card (PSimple 3 J) = 25920 := by
  classical
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hJne : J ≠ ⊥ := glaPComponent_ne_bot' hJ
  have hsmall_case :
      (∀ a b : F4, Fintype.card {i : Fin 6 // d₁ i = a ∧ d₂ i = b} ≤ 3) → J = ⊥ :=
    fun hsmall => eq_bot_of_joint_small hD₁ hD₂ hsmall hJ.1 hperf
  have hex : ∃ a b : F4, 4 ≤ Fintype.card {i : Fin 6 // d₁ i = a ∧ d₂ i = b} := by
    by_contra h
    push Not at h
    have hsmall : ∀ a b : F4, Fintype.card {i : Fin 6 // d₁ i = a ∧ d₂ i = b} ≤ 3 :=
      fun a b => by
        have := h a b
        omega
    exact hJne (hsmall_case hsmall)
  obtain ⟨a, b, h4⟩ := hex
  have hle6 : Fintype.card {i : Fin 6 // d₁ i = a ∧ d₂ i = b} ≤ 6 := by
    have h := Fintype.card_le_of_injective
      (fun x : {i : Fin 6 // d₁ i = a ∧ d₂ i = b} => x.1)
      (fun x y hxy => Subtype.ext hxy)
    simpa using h
  have hnot6 : Fintype.card {i : Fin 6 // d₁ i = a ∧ d₂ i = b} ≠ 6 := by
    intro h6
    let Sf : Finset (Fin 6) := Finset.univ.filter fun i => d₁ i = a ∧ d₂ i = b
    have hSf6 : Sf.card = 6 := by
      have h := h6
      rw [Fintype.card_subtype] at h
      simpa [Sf] using h
    have huniv : Sf = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using hSf6
    have hall : ∀ i, d₁ i = a := by
      intro i
      have hi : i ∈ Sf := by rw [huniv]; exact Finset.mem_univ i
      exact (Finset.mem_filter.1 hi).2.1
    exact hns (fun i => (hall i).trans (hall 0).symm)
  have hnot5 : Fintype.card {i : Fin 6 // d₁ i = a ∧ d₂ i = b} ≠ 5 := by
    intro h5
    let Sf : Finset (Fin 6) := Finset.univ.filter fun i => d₁ i = a ∧ d₂ i = b
    let T : Finset (Fin 6) := Finset.univ.filter fun i => ¬ (d₁ i = a ∧ d₂ i = b)
    have hSf5 : Sf.card = 5 := by
      have h := h5
      rw [Fintype.card_subtype] at h
      simpa [Sf] using h
    have hTcard : T.card = 1 := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 6)))
        (p := fun i => d₁ i = a ∧ d₂ i = b)
      have h' : Sf.card + T.card = 6 := by simpa [Sf, T] using h
      omega
    obtain ⟨j, hTj⟩ := Finset.card_eq_one.1 hTcard
    have hjT : j ∈ T := by rw [hTj]; exact Finset.mem_singleton_self j
    have hjnot : ¬ (d₁ j = a ∧ d₂ j = b) := (Finset.mem_filter.1 hjT).2
    have hpos : 0 < Sf.card := by omega
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.1 hpos
    have hi₀' : d₁ i₀ = a ∧ d₂ i₀ = b := (Finset.mem_filter.1 hi₀).2
    have ha : a ^ 3 = 1 := by rw [← hi₀'.1]; exact h₁ i₀
    have hb : b ^ 3 = 1 := by rw [← hi₀'.2]; exact h₂ i₀
    have hane : d₁ j ≠ a := by
      intro hja
      have hall : ∀ i, d₁ i = a := by
        intro i
        by_cases hi : i ∈ Sf
        · exact (Finset.mem_filter.1 hi).2.1
        · have hpi : ¬ (d₁ i = a ∧ d₂ i = b) := fun hp => hi (by simp [Sf, hp])
          have hiT : i ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ i, hpi⟩
          have hij : i = j := by
            rw [hTj] at hiT
            simpa using hiT
          rw [hij, hja]
      exact hns (fun i => (hall i).trans (hall 0).symm)
    obtain ⟨k, c, hkc, hkc'⟩ := exists_c_of_pair_of_ne a b (d₁ j) (d₂ j)
      ha hb (h₁ j) (h₂ j) hane
    refine hindep (k : ℕ) c ?_
    intro i
    by_cases hi : i ∈ Sf
    · have hi' : d₁ i = a ∧ d₂ i = b := (Finset.mem_filter.1 hi).2
      rw [hi'.1, hi'.2, hkc]
    · have hpi : ¬ (d₁ i = a ∧ d₂ i = b) := fun hp => hi (by simp [Sf, hp])
      have hiT : i ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ i, hpi⟩
      have hij : i = j := by
        rw [hTj] at hiT
        simpa using hiT
      rw [hij, hkc']
  have hlt6 : Fintype.card {i : Fin 6 // d₁ i = a ∧ d₂ i = b} < 6 :=
    lt_of_le_of_ne hle6 hnot6
  have hle5 : Fintype.card {i : Fin 6 // d₁ i = a ∧ d₂ i = b} ≤ 5 := by omega
  have hlt5 : Fintype.card {i : Fin 6 // d₁ i = a ∧ d₂ i = b} < 5 :=
    lt_of_le_of_ne hle5 hnot5
  have hcardS : Fintype.card {i : Fin 6 // d₁ i = a ∧ d₂ i = b} = 4 := by omega
  have hDab := indGL_val d₁ d₂ a b
  have hJab : J ≤ CenD (indGL d₁ d₂ a b) :=
    hJ.1.trans (le_CenD_indGL hD₁ hD₂ a b)
  have hcompl : Fintype.card {i : Fin 6 // ¬ (d₁ i = a ∧ d₂ i = b)} = 2 := by
    rw [Fintype.card_subtype_compl, hcardS]
    norm_num
  have hsmall_e : ∀ c' : F4, c' ≠ 1 →
      Fintype.card (Blk (indPair d₁ d₂ a b) c') ≤ 3 := by
    intro c' hc'
    let f : Blk (indPair d₁ d₂ a b) c' →
        {i : Fin 6 // ¬ (d₁ i = a ∧ d₂ i = b)} := fun x =>
      ⟨x.1, by
        intro hp
        have hx1 : indPair d₁ d₂ a b x.1 = 1 :=
          (indPair_eq_one_iff d₁ d₂ a b x.1).2 hp
        exact hc' (x.2.symm.trans hx1)⟩
    have hinj : Function.Injective f := fun x y hxy =>
      Subtype.ext (congrArg (fun z : {i : Fin 6 // ¬ (d₁ i = a ∧ d₂ i = b)} => z.1) hxy)
    have hle := Fintype.card_le_of_injective f hinj
    omega
  have hJK : J ≤ (embSU (indPair d₁ d₂ a b) 1).range :=
    le_range_embSU (indPair d₁ d₂ a b) 1 hDab hsmall_e hJab hperf
  have hconst₁ : ∀ i j, indPair d₁ d₂ a b i = 1 → indPair d₁ d₂ a b j = 1 →
      d₁ i = d₁ j := by
    intro i j hi hj
    have hi' : d₁ i = a ∧ d₂ i = b := by
      simpa using (indPair_eq_one_iff d₁ d₂ a b i).1 hi
    have hj' : d₁ j = a ∧ d₂ j = b := by
      simpa using (indPair_eq_one_iff d₁ d₂ a b j).1 hj
    exact hi'.1.trans hj'.1.symm
  have hconst₂ : ∀ i j, indPair d₁ d₂ a b i = 1 → indPair d₁ d₂ a b j = 1 →
      d₂ i = d₂ j := by
    intro i j hi hj
    have hi' : d₁ i = a ∧ d₂ i = b := by
      simpa using (indPair_eq_one_iff d₁ d₂ a b i).1 hi
    have hj' : d₁ j = a ∧ d₂ j = b := by
      simpa using (indPair_eq_one_iff d₁ d₂ a b j).1 hj
    exact hi'.2.trans hj'.2.symm
  have hRangeC : (embSU (indPair d₁ d₂ a b) 1).range ≤ CenD D₁ ⊓ CenD D₂ := by
    rintro x ⟨A, rfl⟩
    exact Subgroup.mem_inf.2
      ⟨embSU_mem_CenD_of_const_on_block hD₁ hconst₁ A,
        embSU_mem_CenD_of_const_on_block hD₂ hconst₂ A⟩
  have hsub : CFSG.Open.IsSubnormal J (embSU (indPair d₁ d₂ a b) 1).range := by
    have h := hJ.2.1.inf_of_le hRangeC
    rwa [inf_eq_left.2 hJK] at h
  have hcardBlk4 : Fintype.card (Blk (indPair d₁ d₂ a b) 1) = 4 := by
    rw [card_indPair_one, hcardS]
  let eK := MonoidHom.ofInjective (embSU_injective (indPair d₁ d₂ a b) 1)
  haveI : IsSimpleGroup ↥(StatedSU (Fintype.card (Blk (indPair d₁ d₂ a b) 1)) (2 ^ 1) F4) :=
    isSimple_statedSU _ (Or.inl hcardBlk4)
  haveI hs : IsSimpleGroup ↥(embSU (indPair d₁ d₂ a b) 1).range := eK.symm.isSimpleGroup
  have hJrange : J = (embSU (indPair d₁ d₂ a b) 1).range := by
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub hs with h | h
    · exact absurd h hJne
    · exact h
  have hJsimple : IsSimpleGroup J := by
    rw [hJrange]
    exact hs
  haveI : IsSimpleGroup J := hJsimple
  obtain ⟨ePS⟩ := nonempty_pSimple_equiv_of_simple hJ
  calc
    Nat.card (PSimple 3 J) = Nat.card ↥J := Nat.card_congr ePS.toEquiv
    _ = Nat.card ↥(embSU (indPair d₁ d₂ a b) 1).range := by rw [hJrange]
    _ = Nat.card ↥(StatedSU (Fintype.card (Blk (indPair d₁ d₂ a b) 1)) (2 ^ 1) F4) :=
      (Nat.card_congr eK.toEquiv).symm
    _ = Nat.card ↥(StatedSU 4 (2 ^ 1) F4) := by rw [hcardBlk4]
    _ = 25920 := card_statedSU_four

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610
