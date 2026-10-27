module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue

public section

namespace CFSG.QuasithinUnique.A5.G3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.X7a
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section TwoByTwo

variable {K : Type} [Field K] [CharP K 2]

theorem sl2_eq_one_of_trace_zero (A : SpecialLinearGroup (Fin 2) K) (h3 : A ^ 3 = 1)
    (htr : (A : Matrix (Fin 2) (Fin 2) K) 0 0 + (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) :
    A = 1 := by
  have hA := A.2
  rw [Matrix.det_fin_two] at hA
  set p := (A : Matrix (Fin 2) (Fin 2) K) 0 0 with hp
  set q := (A : Matrix (Fin 2) (Fin 2) K) 0 1 with hq
  set r := (A : Matrix (Fin 2) (Fin 2) K) 1 0 with hr
  set s := (A : Matrix (Fin 2) (Fin 2) K) 1 1 with hs
  have hmat : (A : Matrix (Fin 2) (Fin 2) K) = !![p, q; r, s] := Matrix.eta_fin_two _
  have hA2 : A ^ 2 = 1 := by
    apply Subtype.ext
    show (A : Matrix (Fin 2) (Fin 2) K) ^ 2 = 1
    rw [pow_two, hmat, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination p * htr - hA - (CharTwo.two_eq_zero : (2 : K) = 0)
    · linear_combination q * htr
    · linear_combination r * htr
    · linear_combination s * htr - hA - (CharTwo.two_eq_zero : (2 : K) = 0)
  have h : A ^ 3 = A := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hA2, one_mul]
  rw [← h]
  exact h3

theorem sl2_eq_one_of_fixed (A : SpecialLinearGroup (Fin 2) K) (h3 : A ^ 3 = 1)
    (hfix : ∃ w : Fin 2 → K, w ≠ 0 ∧ ((w ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) = w ∨
      ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = w)) : A = 1 := by
  refine sl2_eq_one_of_trace_zero A h3 ?_
  have hdet : ((A : Matrix (Fin 2) (Fin 2) K) - 1).det = 0 := by
    obtain ⟨w, hw, h | h⟩ := hfix
    · exact Matrix.exists_vecMul_eq_zero_iff.mp
        ⟨w, hw, by rw [Matrix.vecMul_sub, h, Matrix.vecMul_one, sub_self]⟩
    · exact Matrix.exists_mulVec_eq_zero_iff.mp
        ⟨w, hw, by rw [Matrix.sub_mulVec, h, Matrix.one_mulVec, sub_self]⟩
  have hA := A.2
  rw [Matrix.det_fin_two] at hA
  have hsub : (A : Matrix (Fin 2) (Fin 2) K) - 1 = !![(A : Matrix (Fin 2) (Fin 2) K) 0 0 - 1,
      (A : Matrix (Fin 2) (Fin 2) K) 0 1; (A : Matrix (Fin 2) (Fin 2) K) 1 0,
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 - 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hsub, Matrix.det_fin_two] at hdet
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hdet
  linear_combination hA - hdet + (CharTwo.two_eq_zero : (2 : K) = 0)

theorem sl2_twisted_fixed (A : SpecialLinearGroup (Fin 2) K) (h3 : A ^ 3 = 1) (hA1 : A ≠ 1)
    (p r : K) (h1 : p = (A : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 * p +
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 ^ 2 * r)
    (h2 : r = (A : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2 * p +
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 ^ 2 * r) : p = 0 ∧ r = 0 := by
  have hA := A.2
  rw [Matrix.det_fin_two] at hA
  set a := (A : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  set b := (A : Matrix (Fin 2) (Fin 2) K) 0 1 with hb
  set c := (A : Matrix (Fin 2) (Fin 2) K) 1 0 with hc
  set d := (A : Matrix (Fin 2) (Fin 2) K) 1 1 with hd
  by_contra hne
  have hdet : (a ^ 2 + 1) * (d ^ 2 + 1) - b ^ 2 * c ^ 2 = 0 := by
    by_contra hdet
    apply hne
    have e1 : ((a ^ 2 + 1) * (d ^ 2 + 1) - b ^ 2 * c ^ 2) * p = 0 := by
      linear_combination (-(d ^ 2 + 1)) * h1 + b ^ 2 * h2 +
        ((d ^ 2 + 1) * p - b ^ 2 * r) * (CharTwo.two_eq_zero : (2 : K) = 0)
    have e2 : ((a ^ 2 + 1) * (d ^ 2 + 1) - b ^ 2 * c ^ 2) * r = 0 := by
      linear_combination (-(a ^ 2 + 1)) * h2 + c ^ 2 * h1 +
        ((a ^ 2 + 1) * r - c ^ 2 * p) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact ⟨(mul_eq_zero.mp e1).resolve_left hdet, (mul_eq_zero.mp e2).resolve_left hdet⟩
  have hsq : (a + d) ^ 2 = 0 := by
    linear_combination hdet - (a * d + b * c - 1) * hA
  have hsum : a + d = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
  exact hA1 (sl2_eq_one_of_trace_zero A h3 hsum)

end TwoByTwo

section Three

variable {K : Type} [Field K] [Finite K]

theorem Q3_fixed_zero (x u : ↥(perfectCore (Q3 K 0))) (hu : blk3 0 u = 1) (hu1 : u ≠ 1)
    (hxu : x * u = u * x) :
    ∃ w : Fin 2 → K, w ≠ 0 ∧
      (w ᵥ* ((blk3 0 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = w := by
  have hxQ : (x : SpecialLinearGroup (Fin 3) K) ∈ stabilizer (flagSpace 3 K 1) :=
    perfectCore_le _ x.2
  have x10 := stabilizer_entries (k := 1) (l := 0) hxQ (by norm_num) (by norm_num)
  have x20 := stabilizer_entries (k := 2) (l := 0) hxQ (by norm_num) (by norm_num)
  obtain ⟨hlow, hdiag⟩ := blk3_ker 0 u hu
  have u10 := hlow 1 0 (by decide)
  have u20 := hlow 2 0 (by decide)
  have u21 := hlow 2 1 (by decide)
  have u00 := hdiag 0
  have u11 := hdiag 1
  have u22 := hdiag 2
  have hb : (blk3 0 u : SpecialLinearGroup (Fin 2) K) = 1 := hu
  have hb01 : ((blk3 0 u : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    rw [hb]
    simp
  have u12 : ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    simpa [blk3_coe, blkAt] using hb01
  have hm : ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun z : ↥(perfectCore (Q3 K 0)) =>
      (((z : SpecialLinearGroup (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) hxu
    simpa using this
  have e01 := congrFun (congrFun hm 0) 1
  have e02 := congrFun (congrFun hm 0) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at e01 e02
  have hdetX := (x : SpecialLinearGroup (Fin 3) K).2
  rw [Matrix.det_fin_three] at hdetX
  have A00 : ((blk3 0 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 := rfl
  have A01 : ((blk3 0 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 := rfl
  have A10 : ((blk3 0 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 := rfl
  have A11 : ((blk3 0 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 := rfl
  have hdetA := (blk3 0 x).2
  rw [Matrix.det_fin_two, A00, A01, A10, A11] at hdetA
  have hx00 : ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    rw [x10, x20] at hdetX
    linear_combination hdetX - ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 *
      hdetA
  rw [hx00, u11, u21, u00] at e01
  rw [hx00, u12, u22, u00] at e02
  refine ⟨![((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1,
      ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2], ?_, ?_⟩
  · intro hw
    apply hu1
    have h01 : ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 :=
      congrFun hw 0
    have h02 : ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 :=
      congrFun hw 1
    refine Subtype.ext (Subtype.ext ?_)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, u00, u10, u20, u11, u21, u12, u22]
  · funext k
    fin_cases k
    · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, A00, A10]
      linear_combination -e01
    · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, A01, A11]
      linear_combination -e02

theorem Q3_fixed_one (x u : ↥(perfectCore (Q3 K 1))) (hu : blk3 1 u = 1) (hu1 : u ≠ 1)
    (hxu : x * u = u * x) :
    ∃ w : Fin 2 → K, w ≠ 0 ∧
      (((blk3 1 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = w := by
  have hxQ : (x : SpecialLinearGroup (Fin 3) K) ∈ stabilizer (flagSpace 3 K 2) :=
    perfectCore_le _ x.2
  have x20 := stabilizer_entries (k := 2) (l := 0) hxQ (by norm_num) (by norm_num)
  have x21 := stabilizer_entries (k := 2) (l := 1) hxQ (by norm_num) (by norm_num)
  obtain ⟨hlow, hdiag⟩ := blk3_ker 1 u hu
  have u10 := hlow 1 0 (by decide)
  have u20 := hlow 2 0 (by decide)
  have u21 := hlow 2 1 (by decide)
  have u00 := hdiag 0
  have u11 := hdiag 1
  have u22 := hdiag 2
  have hb : (blk3 1 u : SpecialLinearGroup (Fin 2) K) = 1 := hu
  have hb01 : ((blk3 1 u : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    rw [hb]
    simp
  have u01 : ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
    simpa [blk3_coe, blkAt] using hb01
  have hm : ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun z : ↥(perfectCore (Q3 K 1)) =>
      (((z : SpecialLinearGroup (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) hxu
    simpa using this
  have e02 := congrFun (congrFun hm 0) 2
  have e12 := congrFun (congrFun hm 1) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at e02 e12
  have hdetX := (x : SpecialLinearGroup (Fin 3) K).2
  rw [Matrix.det_fin_three] at hdetX
  have A00 : ((blk3 1 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 := rfl
  have A01 : ((blk3 1 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 := rfl
  have A10 : ((blk3 1 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 := rfl
  have A11 : ((blk3 1 x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 := rfl
  have hdetA := (blk3 1 x).2
  rw [Matrix.det_fin_two, A00, A01, A10, A11] at hdetA
  have hx22 : ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    rw [x20, x21] at hdetX
    linear_combination hdetX - ((x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 *
      hdetA
  rw [hx22, u01, u22, u00] at e02
  rw [hx22, u10, u22, u11] at e12
  refine ⟨![((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2,
      ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2], ?_, ?_⟩
  · intro hw
    apply hu1
    have h02 : ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 :=
      congrFun hw 0
    have h12 : ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 :=
      congrFun hw 1
    refine Subtype.ext (Subtype.ext ?_)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h02, h12, u00, u10, u20, u11, u21, u01, u22]
  · funext k
    fin_cases k
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, A00, A01]
      linear_combination e02
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, A10, A11]
      linear_combination e12

theorem not_isDelta5_perfectCore_Q3_four [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    ¬ IsDelta5Group ↥(perfectCore (Q3 K j)) := by
  intro hD
  have := sl2_isSimple hK4
  obtain ⟨x, u, hx3, hu2, hu1, hxu⟩ := hD.exists_three_comm
  have hpc : CFSG.pCore 2 ↥(perfectCore (Q3 K j)) = (blk3 j).ker :=
    pCore_two_eq_ker (sl2_nonabelian hK4) (blk3 j) (blk3_surjective hK4 j)
      (blk3_ker_isPGroup hK j)
  have hu : blk3 j u = 1 := MonoidHom.mem_ker.mp (hpc ▸ hu2)
  have hx : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3] at this
  have hxk : blk3 j x ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := blk3_ker_isPGroup hK j ⟨x, MonoidHom.mem_ker.mpr h1⟩
    have h2 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  have hA3 : (blk3 j x) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  have hfix : ∃ w : Fin 2 → K, w ≠ 0 ∧
      ((w ᵥ* ((blk3 j x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = w ∨
        (((blk3 j x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = w) := by
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) j with rfl | rfl
    · obtain ⟨w, hw, h⟩ := Q3_fixed_zero x u hu hu1 hxu
      exact ⟨w, hw, Or.inl h⟩
    · obtain ⟨w, hw, h⟩ := Q3_fixed_one x u hu hu1 hxu
      exact ⟨w, hw, Or.inr h⟩
  exact hxk (sl2_eq_one_of_fixed _ hA3 hfix)

theorem perfectCore_Q3_eq_bot_of_card_two (hK2 : Nat.card K = 2) (j : Fin 2) :
    perfectCore (Q3 K j) = ⊥ := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨1, by rw [hK2]; norm_num⟩
  have hSL : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := by
    refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK2]
    norm_num
  have hkerS : Group.IsSolvable (blk3 (K := K) j).ker := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (blk3_ker_isPGroup hK j).isNilpotent
    infer_instance
  have hN : Group.IsSolvable ↥(perfectCore (Q3 K j)) :=
    Group.isSolvable_of_ker_le_range (blk3 (K := K) j).ker.subtype (blk3 j)
      (by rw [Subgroup.range_subtype])
  have := (isSolvable_iff_perfectCore_eq_bot (perfectCore (Q3 K j))).mp hN
  rwa [perfectCore_eq_self_of_perfect (perfectCore_perfect _)] at this

theorem not_isDelta5_perfectCore_Q3 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hf1 : 1 ≤ f) (j : Fin 2) : ¬ IsDelta5Group ↥(perfectCore (Q3 K j)) := by
  by_cases h4 : 4 ≤ Nat.card K
  · exact not_isDelta5_perfectCore_Q3_four ⟨f, hf⟩ (exists_finset_card_four h4) j
  · have hf1' : f = 1 := by
      by_contra hne
      apply h4
      rw [hf]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    subst hf1'
    have hK2 : Nat.card K = 2 := by rw [hf]; norm_num
    rw [perfectCore_Q3_eq_bot_of_card_two hK2 j]
    exact not_isDelta5_bot

theorem not_isDelta5_perfectCore_of_cover [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hf1 : 1 ≤ f) {S : Type} [Group S] [Finite S] (π : SpecialLinearGroup (Fin 3) K →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ scalars 3 K)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf ((unitriangular 3 K).map π) ⊤) {Pa : Subgroup S}
    (hpar : IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) :
    ¬ IsDelta5Group ↥(perfectCore Pa) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hres := linear_three_residual_of_cover hK π hπ hker
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q3 K j), ∀ y ∈ perfectCore (Q3 K j),
      π x = π y → x = y := by
    intro j x hx y hy hxy
    have hz : x⁻¹ * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have hzN : x⁻¹ * y ∈ perfectCore (Q3 K j) := mul_mem (inv_mem hx) hy
    have h1 := blk3_scalars j ⟨x⁻¹ * y, hzN⟩ (hker hz)
    exact inv_mul_eq_one.mp (congrArg Subtype.val h1)
  refine not_isDelta5_perfectCore_parabolic hSyl hres (fun j h => ?_) hpar hne
  exact not_isDelta5_perfectCore_Q3 hf hf1 j
    (h.of_equiv (perfectCoreMapEquiv π (Q3 K j) (hinj j)).symm)

end Three

theorem not_isDelta5_perfectCore_l3 {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 1 ≤ f) (hL : IsPSL 3 2 f ↥L ∨ IsSL3 (2 ^ f) ↥L) (hP : IsMaxParabolic2 L P) :
    ¬ IsDelta5Group ↥(perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine not_isDelta5_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  rcases hL with hX | hX
  · have hX' := hX
    obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    let e' : ↥L ≃* projectiveSL 3 K := e.trans (statedSLEquivProjectiveSL 3 K)
    obtain ⟨P₀, hP₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
    have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf (projUnitriangular 3 K) ⊤ :=
      hP₀ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine not_isDelta5_perfectCore_of_equiv e' ?_
    exact not_isDelta5_perfectCore_of_cover hcard hf (proj 3 K) (proj_surjective 3 K)
      (ker_proj 3 K).le hT₀ (isParabolic2_top_map_equiv e' hpa)
      (fun h => hna (by
        have := congrArg (Subgroup.map e'.symm.toMonoidHom) h
        rw [Subgroup.map_map] at this
        have h' : e'.symm.toMonoidHom.comp e'.toMonoidHom = MonoidHom.id _ := by
          ext x
          simp
        rw [h', Subgroup.map_id, Subgroup.map_top_of_surjective _ e'.symm.surjective] at this
        exact this))
  · have hX' := hX
    obtain ⟨K, hF, hFin, hcard, ⟨φ⟩⟩ := hX
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    let e' : ↥L ≃* SpecialLinearGroup (Fin 3) K :=
      φ.trans (specialLinearGroupEquivStatedSL 3 K).symm
    obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
    have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular 3 K) ⊤ :=
      hP₀ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
    refine not_isDelta5_perfectCore_of_equiv e' ?_
    refine not_isDelta5_perfectCore_of_cover hcard hf (MonoidHom.id _) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact bot_le) (by rw [Subgroup.map_id]; exact hT₀)
      (isParabolic2_top_map_equiv e' hpa) (fun h => hna (by
        have := congrArg (Subgroup.map e'.symm.toMonoidHom) h
        rw [Subgroup.map_map] at this
        have h' : e'.symm.toMonoidHom.comp e'.toMonoidHom = MonoidHom.id _ := by
          ext x
          simp
        rw [h', Subgroup.map_id, Subgroup.map_top_of_surjective _ e'.symm.surjective] at this
        exact this))


end CFSG.QuasithinUnique.A5.G3
