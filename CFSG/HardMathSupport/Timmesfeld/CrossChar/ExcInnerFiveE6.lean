module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveLang
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExcFiveOrders
public import CFSG.LieType.SeitzGeneration.ExcTorusTw

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.TauCetiBridge
  CFSG.HardMathSupport.Timmesfeld.DefChar Polynomial
open scoped Matrix

theorem ordProj_charpoly_eval_of_blocks {r : ℕ} {M : Matrix (Fin r) (Fin r) ℤ} {p q e : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) (hq : 2 ≤ q) (he : orderOf (q : ZMod p) = e) (he0 : e ≠ 0)
    (ds : List ℕ) (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod)
    (hso : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2, 3, 4, 6]) :
    p ^ ((M.charpoly.eval (q : ℤ)).natAbs).factorization p =
      (p ^ (q ^ e - 1).factorization p) ^ ds.count e := by
  rw [hchar, prod_cyclotomic_split e ds]
  exact ordProj_cyclotomic_pow_mul_eval hp hq he he0
    (not_dvd_cyclotomic_eval_of_mem_small hp h5 he ds hso)

theorem charpoly_eval_ne_zero_of_blocks {r : ℕ} {M : Matrix (Fin r) (Fin r) ℤ} {q : ℕ}
    (hq : 2 ≤ q) (ds : List ℕ) (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod) :
    M.charpoly.eval (q : ℤ) ≠ 0 := by
  rw [hchar, eval_list_prod]
  refine List.prod_ne_zero fun h0 => ?_
  simp only [List.map_map, List.mem_map, Function.comp_apply] at h0
  obtain ⟨d, -, hd⟩ := h0
  exact (cyclotomic_pos' d (by exact_mod_cast hq : (1 : ℤ) < q)).ne' hd

theorem factorization_sq_sub_one_of_dvd_add_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 2 ≤ q) (h : p ∣ q + 1) : (q ^ 2 - 1).factorization p = (q + 1).factorization p := by
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [show 1 ≤ q by omega, Nat.one_le_pow 2 q (by omega)]
    ring
  have hpq : ¬ p ∣ q - 1 := by
    intro h1
    have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub h h1
    rw [show q + 1 - (q - 1) = 2 by omega] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  rw [hsq, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hpq, add_zero]

theorem factorization_sq_sub_one_of_dvd_sub_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 2 ≤ q) (h : p ∣ q - 1) : (q ^ 2 - 1).factorization p = (q - 1).factorization p := by
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [show 1 ≤ q by omega, Nat.one_le_pow 2 q (by omega)]
    ring
  have hpq : ¬ p ∣ q + 1 := by
    intro h1
    have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub h1 h
    rw [show q + 1 - (q - 1) = 2 by omega] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  rw [hsq, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hpq, zero_add]

noncomputable abbrev e6PhiTwoWeyl :
    WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd e6TwoWord

section Orders


theorem factorization_card_adjointE6_eq_of_dvd_add_one (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K + 1) :
    (Nat.card (adjointGroup Tag.E6 K)).factorization 5 =
      (((wordMat Tag.E6 e6TwoWord).charpoly.eval (Nat.card K : ℤ)).natAbs).factorization 5 := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have he := Proving.orderOf_natCast_zmod_five_of_dvd_add_one h5
  have h2 := ordProj_charpoly_eval_of_blocks Nat.prime_five le_rfl hq2 he (by norm_num) _
    e6Two_charpoly (by decide)
  have h3 : [1, 1, 2, 2, 2, 2].count 2 = 4 := by decide
  rw [h3, ← pow_mul] at h2
  rw [Proving.factorization_five_card_adjointGroup_E6_of_dvd_add_one K h5,
    Nat.pow_right_injective (by norm_num : 2 ≤ 5) h2,
    factorization_sq_sub_one_of_dvd_add_one Nat.prime_five (by norm_num) hq2 h5, mul_comm]

theorem isInnerLocallyBalanced_adjointE6_five_of_dvd_add_one
    (hres : LangTorusPlaneBalance Tag.E6 e6PhiTwoWeyl 5 fun q => 5 ∣ q + 1)
    (K : Type) [Field K] [Finite K] (h5 : 5 ∣ Nat.card K + 1) :
    IsInnerLocallyBalanced 5 (adjointGroup Tag.E6 K) :=
  isInnerLocallyBalanced_adjoint_of_langTorus 3 (Or.inl ⟨rfl, rfl⟩)
    (wordProd_smul_eq_wordMat_mulVec Tag.E6 e6TwoWord) (n := 2) (by norm_num) e6Two_pow
    Nat.prime_five (by norm_num) hres K h5
    (charpoly_eval_ne_zero_of_blocks Finite.one_lt_card _ e6Two_charpoly)
    ((factorization_card_adjointE6_eq_of_dvd_add_one K h5).le.trans (Nat.le_succ _))

end Orders

section Catalogue


theorem crossCharInnerAt_E6_five_dvd_add_one
    (hres : LangTorusPlaneBalance Tag.E6 e6PhiTwoWeyl 5 fun q => 5 ∣ q + 1) :
    CrossCharInnerAt .E6 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧ 5 ∣ q.card + 1) ∧ p = 5 := by
  rintro ⟨d, hv⟩ _ p _ _ _ ⟨⟨q, hd, h5⟩, rfl⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  rw [← hK] at h5
  exact (isInnerLocallyBalanced_adjointE6_five_of_dvd_add_one hres K h5).of_mulEquiv e

end Catalogue

end CFSG.HardMathSupport.Timmesfeld.CrossChar
