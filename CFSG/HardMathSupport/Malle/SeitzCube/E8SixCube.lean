module

public import CFSG.HardMathSupport.Malle.SeitzCube.E8PhiSixData
public import CFSG.HardMathSupport.Malle.SeitzCube.RootSingleFixed
public import CFSG.HardMathSupport.Malle.Proving.E8CubeOrders
public import CFSG.HardMathSupport.Malle.Proving.E8CubeSideConditions
public import CFSG.HardMathSupport.Malle.SeitzCube.TwistedTorusCube

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice Polynomial
open CFSG.HardMathSupport.Malle.Proving
open scoped Matrix

section Main


theorem twistedCubeE8_six : TwistedCubeE8 fun q p => p ≠ 3 ∧ p ∣ q ^ 2 - q + 1 := by
  intro K _ _ L _ _ _ Fr hFr p hp hP
  obtain ⟨hp3, hpq⟩ := hP
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp2 := ne_two_of_dvd_sq_sub_add_one hpq
  have hpq' := not_dvd_of_dvd_sq_sub_add_one hp hpq
  have he := orderOf_eq_six_of_dvd hp hp3 hpq
  obtain ⟨w, hw⟩ := IsWeylMatrix.of_word Tag.E8 e8W6Word
  have hn6 : ¬ p ∣ 6 := by
    intro h
    have h6 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h6] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)
  have hchar : (wordMat Tag.E8 e8W6Word).charpoly =
      cyclotomic 6 ℤ ^ 3 * (cyclotomic 1 ℤ * cyclotomic 2 ℤ) := by
    rw [e8W6_charpoly]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  have hR : ¬ (p : ℤ) ∣ (cyclotomic 1 ℤ * cyclotomic 2 ℤ).eval (Nat.card K : ℤ) := by
    intro h
    simp only [eval_mul, cyclotomic_one, cyclotomic_two, eval_sub, eval_X, eval_one,
      eval_add] at h
    exact not_int_dvd_sub_one_mul_add_one_of_orderOf hp he (by norm_num) (by norm_num) h
  obtain ⟨E, hEt, hEab, hEc⟩ := exists_twistedTorus_elemAbelian K L Fr hFr hp hpq' w hw
    (n := 6) (e := 6) (m := 3) (cyclotomic 1 ℤ * cyclotomic 2 ℤ) (by norm_num) e8W6_pow hn6
    hchar he hR
  have hwθ : w • e8Theta = e8Theta := by rw [hw]; exact e8W6_mulVec_theta
  obtain ⟨R, hRt, hRne, hRp, hRn⟩ := exists_rootSingle_fixed Fr hq2 hFr w
    (mem_rootFinset.1 e8Theta_mem) hwθ
  have hEfix : E ≤ twistFix .E8 Fr (canonicalRep (coxeterSystem Tag.E8) L w) := fun x hx =>
    mem_twistFix.2 ⟨torusGroup_le_adjointGroup' (hEt hx).1, (hEt hx).2⟩
  exact ⟨canonicalRep (coxeterSystem Tag.E8) L w, canonicalRep_mem_adjointGroup _ L w, E, R,
    hEfix, hRt, hEab, hEc, hRne, hRp, fun x hx => hRn x (hEt hx).1 (hEfix hx)⟩

end Main

end CFSG.HardMathSupport.Malle.SeitzCube
