module

public import CFSG.HardMathSupport.Malle.SeitzCube.E8PhiFourD7
public import CFSG.HardMathSupport.Malle.SeitzCube.TwistedTorusCube
public import CFSG.HardMathSupport.Malle.SeitzCube.RootPairFixed

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice Polynomial
open CFSG.LieType.Steinberg.Adjoint (iform)
open scoped Matrix

section Arith

theorem three_lt_of_dvd_sq_add_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ q ^ 2 + 1) :
    3 < p := by
  have h3 : p ≠ 3 := by
    rintro rfl
    have := (ZMod.natCast_eq_zero_iff (q ^ 2 + 1) 3).2 h
    push_cast at this
    revert this
    generalize (q : ZMod 3) = x
    revert x
    decide
  have := hp.two_le
  omega

theorem not_dvd_of_dvd_sq_add_one {p q : ℕ} (hp : p.Prime) (h : p ∣ q ^ 2 + 1) : ¬ p ∣ q := by
  intro hq
  have h1 : p ∣ q ^ 2 := dvd_pow hq (by norm_num)
  exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 h))

theorem orderOf_eq_four_of_dvd_sq_add_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ q ^ 2 + 1) : orderOf ((q : ℕ) : ZMod p) = 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp3 := three_lt_of_dvd_sq_add_one hp hp2 h
  have : Fact (2 < p) := ⟨by omega⟩
  set x : ZMod p := ((q : ℕ) : ZMod p) with hx
  have hx2 : x ^ 2 = -1 := by
    have := (ZMod.natCast_eq_zero_iff (q ^ 2 + 1) p).2 h
    push_cast at this
    rw [← hx] at this
    exact eq_neg_of_add_eq_zero_left this
  have hx4 : x ^ 4 = 1 := by
    calc x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [hx2]
      _ = 1 := neg_one_sq
  have hne : x ^ 2 ≠ 1 := by
    rw [hx2]
    exact ZMod.neg_one_ne_one
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (show orderOf x ∣ 2 ^ 2 from orderOf_dvd_of_pow_eq_one hx4)
  interval_cases i
  · have h1 : orderOf x = 1 := by simpa using hio
    have h2 := pow_orderOf_eq_one x
    rw [h1, pow_one] at h2
    exact absurd (by rw [h2, one_pow]) hne
  · exact absurd (by
      have := pow_orderOf_eq_one x
      rwa [show orderOf x = 2 by simpa using hio] at this) hne
  · simpa using hio

end Arith

section Main


theorem twistedCubeE8_four : TwistedCubeE8 fun q p => p ≠ 2 ∧ p ∣ q ^ 2 + 1 := by
  intro K _ _ L _ _ _ Fr hFr p hp hP
  obtain ⟨hp2, hpq⟩ := hP
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpq' := not_dvd_of_dvd_sq_add_one hp hpq
  have hp3 := three_lt_of_dvd_sq_add_one hp hp2 hpq
  have he := orderOf_eq_four_of_dvd_sq_add_one hp hp2 hpq
  obtain ⟨w, hw⟩ := IsWeylMatrix.of_word Tag.E8 e8D7FourWord
  have hn4 : ¬ p ∣ 4 := by
    intro h
    have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hchar : (wordMat Tag.E8 e8D7FourWord).charpoly =
      cyclotomic 4 ℤ ^ 3 * (cyclotomic 1 ℤ * cyclotomic 2 ℤ) := by
    rw [e8D7Four_charpoly]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  have hR : ¬ (p : ℤ) ∣ (cyclotomic 1 ℤ * cyclotomic 2 ℤ).eval (Nat.card K : ℤ) := by
    intro h
    simp only [eval_mul, cyclotomic_one, cyclotomic_two, eval_sub, eval_X, eval_one,
      eval_add] at h
    have h1 : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by exact_mod_cast hpq
    have h2 : (p : ℤ) ∣ ((Nat.card K : ℤ) - 1) * ((Nat.card K : ℤ) + 1) := h
    have h3 : (p : ℤ) ∣ 2 := by
      have := dvd_sub h1 h2
      convert this using 1
      ring
    have h4 : p ∣ 2 := by exact_mod_cast h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h4)
  obtain ⟨E, hEt, hEab, hEc⟩ := exists_twistedTorus_elemAbelian K L Fr hFr hp hpq' w hw
    (n := 4) (e := 4) (m := 3) (cyclotomic 1 ℤ * cyclotomic 2 ℤ) (by norm_num) e8D7Four_pow hn4
    hchar he hR
  have hsym : ∀ i, Tag.E8.symmetrizer i i = 1 := fun i => by simp [Tag.symmetrizer]
  have hwγ : w • e8D7Gamma = e8D7GammaW := by rw [hw]; exact e8D7Four_mulVec_gamma
  have hwδ : w • e8D7GammaW = e8D7Gamma := by rw [hw]; exact e8D7Four_mulVec_gammaW
  obtain ⟨R, hRt, hRne, hRp, hRn⟩ := exists_rootPair_fixed hsym Fr hq2 hFr w
    (mem_rootFinset.1 e8D7Gamma_mem) (mem_rootFinset.1 e8D7GammaW_mem) e8D7Gamma_ne
    e8D7Gamma_height e8D7GammaW_height e8D7Gamma_orth hwγ hwδ
  have hEfix : E ≤ twistFix .E8 Fr (canonicalRep (coxeterSystem Tag.E8) L w) := fun x hx =>
    mem_twistFix.2 ⟨torusGroup_le_adjointGroup' (hEt hx).1, (hEt hx).2⟩
  exact ⟨canonicalRep (coxeterSystem Tag.E8) L w, canonicalRep_mem_adjointGroup _ L w, E, R,
    hEfix, hRt, hEab, hEc, hRne, hRp, fun x hx => hRn x (hEt hx).1 (hEfix hx)⟩

end Main

end CFSG.HardMathSupport.Malle.SeitzCube
