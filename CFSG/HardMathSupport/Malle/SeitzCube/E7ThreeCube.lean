module

public import CFSG.HardMathSupport.Malle.SeitzCube.E7High
public import CFSG.HardMathSupport.Malle.SeitzCube.E7PhiThreeData
public import CFSG.HardMathSupport.Malle.SeitzCube.TwistedTorusCube
public import CFSG.HardMathSupport.Malle.SeitzCube.RootTripleFixed
public import CFSG.HardMathSupport.Malle.Proving.E8CubeSideConditions

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice Polynomial
open CFSG.HardMathSupport.Malle.Proving
open scoped Matrix

theorem symmetrizer_E7 : ∀ i, Tag.E7.symmetrizer i i = 1 := fun i => by simp [Tag.symmetrizer]

section Main


theorem twistedCubeE7_three : TwistedCubeE7 fun q p => orderOf ((q : ℕ) : ZMod p) = 3 := by
  intro K _ _ L _ _ _ Fr hFr p hp _ he
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hp3 : ¬ p ∣ 3 := not_dvd_of_orderOf hp hpq he
  obtain ⟨w, hw⟩ := IsWeylMatrix.of_word Tag.E7 e7W3Word
  have hchar : (wordMat Tag.E7 e7W3Word).charpoly = cyclotomic 3 ℤ ^ 3 * cyclotomic 1 ℤ := by
    rw [e7W3_charpoly]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  have hR : ¬ (p : ℤ) ∣ (cyclotomic 1 ℤ).eval (Nat.card K : ℤ) := by
    intro h
    simp only [cyclotomic_one, eval_sub, eval_X, eval_one] at h
    exact not_int_dvd_sub_one_sq_of_orderOf hp he (by norm_num) (dvd_mul_of_dvd_left h _)
  obtain ⟨E, hEt, hEab, hEc⟩ := exists_twistedTorus_elemAbelian K L Fr hFr hp hpq w hw
    (n := 3) (e := 3) (m := 3) (cyclotomic 1 ℤ) (by norm_num) e7W3_pow hp3 hchar he hR
  have hw₁ : w • e7Gamma₁ = e7Gamma₂ := by rw [hw]; exact e7W3_mulVec_gamma₁
  have hw₂ : w • e7Gamma₂ = e7Gamma₃ := by rw [hw]; exact e7W3_mulVec_gamma₂
  have hw₃ : w • e7Gamma₃ = e7Gamma₁ := by rw [hw]; exact e7W3_mulVec_gamma₃
  obtain ⟨R, hRt, hRne, hRp, hRn⟩ := exists_rootTriple_fixed symmetrizer_E7 Fr hq2 hFr w
    (mem_rootFinset.1 e7Gamma₁_mem) (mem_rootFinset.1 e7Gamma₂_mem)
    (mem_rootFinset.1 e7Gamma₃_mem) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) iform_e7Gamma₁₂ iform_e7Gamma₁₃
    iform_e7Gamma₂₃ hw₁ hw₂ hw₃
  have hEfix : E ≤ twistFix .E7 Fr (canonicalRep (coxeterSystem Tag.E7) L w) := fun x hx =>
    mem_twistFix.2 ⟨torusGroup_le_adjointGroup' (hEt hx).1, (hEt hx).2⟩
  exact ⟨canonicalRep (coxeterSystem Tag.E7) L w, canonicalRep_mem_adjointGroup _ L w, E, R,
    hEfix, hRt, hEab, hEc, hRne, hRp, fun x hx => hRn x (hEt hx).1 (hEfix hx)⟩

end Main

section At


theorem excCubeHighAt_E7_three : ExcCubeHighAt TauCeti.LieTypeIndex.E7 3 :=
  excCubeHighAt_E7_three_of_twisted twistedCubeE7_three

end At

end CFSG.HardMathSupport.Malle.SeitzCube
