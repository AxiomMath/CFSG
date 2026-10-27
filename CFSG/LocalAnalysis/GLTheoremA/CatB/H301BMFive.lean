module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenBW
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Census
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveCo1
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import Certificates.Certificate13670

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.HardMathSupport.Dickson.I271 Module
open scoped Matrix

private def fixSub (H : Subgroup ↥CFSG.Sporadic.Co1Schreier.GA) :
    Submodule (ZMod 2) (Fin 24 → ZMod 2) where
  carrier := {v | ∀ j ∈ H,
    ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v}
  add_mem' {u w} hu hw j hj := by rw [Matrix.mulVec_add, hu j hj, hw j hj]
  zero_mem' j _ := Matrix.mulVec_zero _
  smul_mem' c v hv j hj := by rw [Matrix.mulVec_smul, hv j hj]

private theorem natCard_fixSub (H : Subgroup ↥CFSG.Sporadic.Co1Schreier.GA) :
    Nat.card {v : Fin 24 → ZMod 2 // ∀ j ∈ H,
      ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} =
      2 ^ finrank (ZMod 2) (fixSub H) := by
  have e : Nat.card (fixSub H) = 2 ^ finrank (ZMod 2) (fixSub H) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact (Nat.card_congr (Equiv.subtypeEquivRight fun v => Iff.rfl)).trans e


private theorem fixCount_le_of_orderOf_five {j : ↥CFSG.Sporadic.Co1Schreier.GA}
    (hj : orderOf j = 5) :
    TabMFive.fixCount ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) ≤
      2 ^ 8 := by
  obtain ⟨c, hc⟩ := TabCo1.tabCo1_census Certificates.certificate13670 j hj
  have hconj : TabMFive.fixCount
      (((c * j * c⁻¹ : ↥CFSG.Sporadic.Co1Schreier.GA) : GL (Fin 24) (ZMod 2)) :
        Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      TabMFive.fixCount ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) :=
    TabMFive.fixCount_conj (c : GL (Fin 24) (ZMod 2)) j
  rw [← hconj]
  rcases hc with h | h | h
  · exact (TabMFive.fixCount_fiveA_le h).trans (by norm_num)
  · exact TabMFive.fixCount_fiveB_le h
  · exact (TabMFive.fixCount_fiveC_le h).trans (by norm_num)

theorem card_fixed_le_of_five_sq {H : Subgroup ↥CFSG.Sporadic.Co1Schreier.GA}
    (hH : IsElemAbelian 5 H) (hHc : Nat.card H = 5 ^ 2) :
    Nat.card {v : Fin 24 → ZMod 2 // ∀ j ∈ H,
      ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} ≤ 2 ^ 4 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hfix : ∀ a ∈ H.map CFSG.Sporadic.Co1Schreier.GA.subtype, a ≠ 1 →
      Nat.card {v : Fin 24 → ZMod 2 // (a : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} ≤
        2 ^ 8 := by
    rintro _ ⟨j, hj, rfl⟩ ha
    have hj1 : j ≠ 1 := by
      rintro rfl
      exact ha (map_one _)
    exact fixCount_le_of_orderOf_five (orderOf_eq_prime (hH.2 j hj) hj1)
  have h := card_fixed_pow_mul_le (by norm_num) (hH.map CFSG.Sporadic.Co1Schreier.GA.subtype)
    ((Subgroup.card_subtype _ H).trans hHc) hfix
  have hS := natCard_fixSub H
  have hA : Nat.card {v : Fin 24 → ZMod 2 // ∀ a ∈ H.map CFSG.Sporadic.Co1Schreier.GA.subtype,
      (a : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} = Nat.card {v : Fin 24 → ZMod 2 //
        ∀ j ∈ H, ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v =>
      ⟨fun hv j hj => hv _ (Subgroup.mem_map_of_mem _ hj), by
        rintro hv _ ⟨j, hj, rfl⟩
        exact hv j hj⟩)
  have h1 : 2 ^ 24 * (2 ^ finrank (ZMod 2) (fixSub H)) ^ 5 ≤ 2 ^ (8 * (5 + 1)) := by
    rw [← hS, ← hA]
    exact h
  rw [← pow_mul, ← pow_add] at h1
  have h2 := (pow_le_pow_iff_right₀ (by norm_num : 1 < 2)).1 h1
  rw [hS]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.LocalAnalysis.GLTheoremA.H301B
