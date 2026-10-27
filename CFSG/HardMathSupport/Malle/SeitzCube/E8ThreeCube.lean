module

public import CFSG.HardMathSupport.Malle.SeitzCube.E8ThreeData
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


theorem twistedCubeE8_three : TwistedCubeE8 fun q p => p ≠ 3 ∧ p ∣ q ^ 2 + q + 1 := by
  intro K _ _ L _ _ _ Fr hFr p hp hP
  obtain ⟨hp3, hpq⟩ := hP
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpq' := not_dvd_of_dvd_sq_add_add_one hp hpq
  have he := orderOf_eq_three_of_dvd hp hp3 hpq
  obtain ⟨w, hw⟩ := IsWeylMatrix.of_word Tag.E8 e8W3Word
  have hn3 : ¬ p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  have hchar : (wordMat Tag.E8 e8W3Word).charpoly =
      cyclotomic 3 ℤ ^ 3 * (cyclotomic 1 ℤ * cyclotomic 1 ℤ) := by
    rw [e8W3_charpoly]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  have hR : ¬ (p : ℤ) ∣ (cyclotomic 1 ℤ * cyclotomic 1 ℤ).eval (Nat.card K : ℤ) := by
    intro h
    simp only [eval_mul, cyclotomic_one, eval_sub, eval_X, eval_one] at h
    exact not_int_dvd_sub_one_sq_of_orderOf hp he (by norm_num) h
  obtain ⟨E, hEt, hEab, hEc⟩ := exists_twistedTorus_elemAbelian K L Fr hFr hp hpq' w hw
    (n := 3) (e := 3) (m := 3) (cyclotomic 1 ℤ * cyclotomic 1 ℤ) (by norm_num) e8W3_pow hn3
    hchar he hR
  have hwθ : w • e8Theta = e8Theta := by rw [hw]; exact e8W3_mulVec_theta
  obtain ⟨R, hRt, hRne, hRp, hRn⟩ := exists_rootSingle_fixed Fr hq2 hFr w
    (mem_rootFinset.1 e8Theta_mem) hwθ
  have hEfix : E ≤ twistFix .E8 Fr (canonicalRep (coxeterSystem Tag.E8) L w) := fun x hx =>
    mem_twistFix.2 ⟨torusGroup_le_adjointGroup' (hEt hx).1, (hEt hx).2⟩
  exact ⟨canonicalRep (coxeterSystem Tag.E8) L w, canonicalRep_mem_adjointGroup _ L w, E, R,
    hEfix, hRt, hEab, hEc, hRne, hRp, fun x hx => hRn x (hEt hx).1 (hEfix hx)⟩

end Main

end CFSG.HardMathSupport.Malle.SeitzCube
