module

public import CFSG.LieType.SeitzGeneration.ExcTorusEigen
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.RootCharHom
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.KA5L.Chain
public import CFSG.RankThree.PartOne.KE.E7ThreeTorus
public import CFSG.RankThree.PartOne.KLR.A1Swap
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix Polynomial CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.Classical2 CFSG.Open
  CFSG.RankThree.PartOne.KLR CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7 CFSG.LieType.SeitzGeneration
open scoped Matrix MatrixGroups Pointwise


theorem charpoly_neg_e7T3W :
    (-e7T3W).charpoly = (X + 1) * (X ^ 2 - X + 1) ^ 3 := by
  have hnat : (((X + 1) * (X ^ 2 - X + 1) ^ 3 : ℤ[X])).natDegree ≤ 7 := by compute_degree
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq
    ((Finset.range 8).image (fun n : ℕ => (n : ℤ))) ?_ ?_ ?_
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range,
      Matrix.charpoly_degree_eq_dim]
    change ((7 : ℕ) : WithBot ℕ) < ((8 : ℕ) : WithBot ℕ)
    exact WithBot.coe_lt_coe.2 (by norm_num)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hnat)
      (WithBot.coe_lt_coe.2 (by norm_num))
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
    rw [Matrix.eval_charpoly]
    have hdet : Matrix.scalar (Fin Tag.E7.rank) (n : ℤ) - (-e7T3W) =
        -(Matrix.scalar (Fin Tag.E7.rank) (-(n : ℤ)) - e7T3W) := by
      ext i j
      simp only [Matrix.scalar_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.diagonal_apply]
      by_cases h : i = j <;> simp [h] <;> ring
    have h := congrArg (Polynomial.eval (-(n : ℤ))) charpoly_e7T3W
    rw [Matrix.eval_charpoly] at h
    rw [hdet, Matrix.det_neg, Fintype.card_fin, h, show Tag.E7.rank = 7 from rfl]
    norm_num
    ring

private theorem one_smul_e7T3W : (1 : ℤ) • e7T3W = e7T3W := one_smul _ _

private theorem neg_one_smul_e7T3W : (-1 : ℤ) • e7T3W = -e7T3W := by
  rw [neg_smul, one_smul]

theorem e7T3W_pow_six : e7T3W ^ 6 = 1 := by
  decide +kernel

theorem natCard_e7T3_solutions {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ℕ}
    (hq : (q : ZMod p) ^ 2 + (ε : ZMod p) * (q : ZMod p) + 1 = 0) :
    Nat.card {z : Fin Tag.E7.rank → ZMod p //
      (modMat p (ε • e7T3W))ᵀ *ᵥ z = (q : ZMod p) • z} = p ^ 3 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpq : ¬ p ∣ q := by
    intro h
    have h0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 h
    rw [h0] at hq
    have h1 : (1 : ZMod p) = 0 := by simpa using hq
    have hdvd : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).1 (by simpa using h1)
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hqne1 : (q : ZMod p) ≠ 1 := by
    intro h1
    rcases hε with rfl | rfl
    · rw [h1] at hq
      have h3 : (3 : ZMod p) = 0 := by linear_combination hq
      have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 (by simpa using h3)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    · rw [h1] at hq
      have h3 : (1 : ZMod p) = 0 := by linear_combination hq
      have hdvd : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).1 (by simpa using h3)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  have hn : ¬ p ∣ 6 := by
    intro h
    have h2 : p ∣ 2 * 3 := by simpa using h
    rcases hp.dvd_mul.1 h2 with h' | h'
    · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h'
      omega
    · have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h'
      omega
  rcases hε with rfl | rfl
  ·
    have hq3 : (q : ZMod p) ^ 3 = 1 := by
      have h : (q : ZMod p) ^ 2 = -(q : ZMod p) - 1 := by linear_combination hq
      calc (q : ZMod p) ^ 3 = (q : ZMod p) * (q : ZMod p) ^ 2 := by ring
        _ = (q : ZMod p) * (-(q : ZMod p) - 1) := by rw [h]
        _ = 1 := by linear_combination -h
    have he : orderOf (q : ZMod p) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact orderOf_eq_prime hq3 hqne1
    have hR : ¬ (p : ℤ) ∣ (X - 1 : ℤ[X]).eval (q : ℤ) := by
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
      intro h
      have hmod : (q : ℤ) ≡ 1 [ZMOD (p : ℤ)] := by
        rw [Int.modEq_iff_dvd]
        rw [show (1 : ℤ) - (q : ℤ) = -((q : ℤ) - 1) from by ring]
        exact dvd_neg.mpr h
      have hcast : ((q : ℤ) : ZMod p) = ((1 : ℤ) : ZMod p) :=
        (ZMod.intCast_eq_intCast_iff _ _ _).2 hmod
      have hq1 : (q : ZMod p) = 1 := by simpa using hcast
      exact hqne1 hq1
    have hchar : ((1 : ℤ) • e7T3W).charpoly = cyclotomic 3 ℤ ^ 3 * (X - 1) := by
      rw [one_smul_e7T3W, charpoly_e7T3W, cyclotomic_three]
      ring
    have := natCard_solutions_modMat hp ((1 : ℤ) • e7T3W) (n := 6) (e := 3) (m := 3) (q := q)
      (X - 1) (by rw [one_smul_e7T3W]; exact e7T3W_pow_six) hn hchar hpq he hR
    simpa [one_smul_e7T3W] using this
  ·
    have hq3 : (q : ZMod p) ^ 3 = -1 := by
      have h : (q : ZMod p) ^ 2 = (q : ZMod p) - 1 := by linear_combination hq
      calc (q : ZMod p) ^ 3 = (q : ZMod p) * (q : ZMod p) ^ 2 := by ring
        _ = (q : ZMod p) * ((q : ZMod p) - 1) := by rw [h]
        _ = -1 := by linear_combination hq
    have hq6 : (q : ZMod p) ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hq3]; norm_num
    have hq2ne1 : (q : ZMod p) ^ 2 ≠ 1 := by
      intro h2
      have hqsub : (q : ZMod p) ^ 2 = (q : ZMod p) - 1 := by linear_combination hq
      rw [hqsub] at h2
      have hq2 : (q : ZMod p) = 2 := by linear_combination h2
      rw [hq2] at hq
      have h3 : (3 : ZMod p) = 0 := by linear_combination hq
      have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 (by simpa using h3)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hq3ne1 : (q : ZMod p) ^ 3 ≠ 1 := by
      rw [hq3]
      intro h
      have h2 : (2 : ZMod p) = 0 := by
        have h' : (1 : ZMod p) - (-1) = 0 := by rw [h]; ring
        norm_num at h'
        exact h'
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by simpa using h2)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have he : orderOf (q : ZMod p) = 6 := by
      refine (orderOf_eq_iff (by norm_num)).2 ⟨hq6, fun m hm hmlt => ?_⟩
      interval_cases m
      · simpa using hqne1
      · simpa using hq2ne1
      · simpa using hq3ne1
      · intro h4
        apply hq2ne1
        rw [← hq6, show (6 : ℕ) = 4 + 2 by norm_num, pow_add, h4, one_mul]
      · intro h5
        apply hqne1
        have h : (q : ZMod p) = 1 := by
          rw [← hq6, show (6 : ℕ) = 5 + 1 by norm_num, pow_add, h5, one_mul]
          simp
        simpa using h
    have hpow : ((-1 : ℤ) • e7T3W) ^ 6 = 1 := by
      rw [neg_one_smul_e7T3W]
      have h : (-e7T3W) ^ 6 = e7T3W ^ 6 := by
        rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, neg_sq, ← pow_mul]
      rw [h, e7T3W_pow_six]
    have hR : ¬ (p : ℤ) ∣ (X + 1 : ℤ[X]).eval (q : ℤ) := by
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      intro h
      have hne : (q : ℤ) ≡ -1 [ZMOD (p : ℤ)] := by
        rw [Int.modEq_iff_dvd]
        rw [show (-1 : ℤ) - (q : ℤ) = -((q : ℤ) + 1) from by ring]
        exact dvd_neg.mpr h
      have hcast : ((q : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) :=
        (ZMod.intCast_eq_intCast_iff _ _ _).2 hne
      have h2 : (q : ZMod p) = -1 := by simpa using hcast
      rw [h2] at hq
      have h3 : (3 : ZMod p) = 0 := by linear_combination hq
      have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 (by simpa using h3)
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hchar : (((-1 : ℤ) • e7T3W)).charpoly = cyclotomic 6 ℤ ^ 3 * (X + 1) := by
      rw [neg_one_smul_e7T3W, charpoly_neg_e7T3W, cyclotomic_six]
      ring
    have := natCard_solutions_modMat hp (((-1 : ℤ) • e7T3W)) (n := 6) (e := 6) (m := 3) (q := q)
      (X + 1) hpow hn hchar hpq he hR
    simpa [neg_one_smul_e7T3W] using this

theorem natCard_e7T3_fixedPTorsion {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (L : Type) [Field L] [IsAlgClosed L] {ℓ q : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (Fr : L →+* L) (hℓq : ℓ ∣ q) (hFr : ∀ c, Fr c = c ^ q)
    (hq : (q : ZMod p) ^ 2 + (ε : ZMod p) * (q : ZMod p) + 1 = 0) :
    Nat.card {b : Fin Tag.E7.rank → Lˣ //
      b ∈ fixedCharTuples (ε • e7T3W) Fr ∧ ∀ i, b i ^ p = 1} = p ^ 3 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpq : ¬ p ∣ q := by
    intro h
    have h0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 h
    rw [h0] at hq
    have h1 : (1 : ZMod p) = 0 := by simpa using hq
    have hdvd : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).1 (by simpa using h1)
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hpℓ : p ≠ ℓ := fun h => hpq (h ▸ hℓq)
  have hcard := natCard_fixedTorsion (ε • e7T3W) Fr (Fact.out) hFr hp hpℓ
  let e : {b : Fin Tag.E7.rank → Lˣ //
      b ∈ fixedCharTuples (ε • e7T3W) Fr ∧ ∀ i, b i ^ p = 1} ≃
      {a : fixedCharTuples (ε • e7T3W) Fr //
        ∀ i, (a : Fin Tag.E7.rank → Lˣ) i ^ p = 1} :=
    { toFun := fun b => ⟨⟨b.1, b.2.1⟩, b.2.2⟩
      invFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, hcard]
  exact natCard_e7T3_solutions hp hp3 hε hq

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
