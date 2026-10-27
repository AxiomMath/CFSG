module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Three
public import Certificates.Certificate17332

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native
  Timmesfeld.Co1Leaf

section Group

theorem eq_conj_of_conj {G : Type} [Group G] {t x g : G} (h : g * t * g⁻¹ = x) :
    t = g⁻¹ * x * g⁻¹⁻¹ := by
  rw [← h]
  group

end Group

theorem eltG_threeA (g0 g1 g2 g3 g4 g5 : ↥GA) :
    eltG [g0, g1, g2, g3, g4, g5] [0, 1, 0, 0, 1, 1] = g1 * g4 * g5 := by
  simp only [eltG, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
    pow_zero, pow_one, mul_one, one_mul]

theorem a_mem_GA (i : Fin 6) : ElemThree.a i ∈ GA :=
  A_le_GA (Subgroup.subset_closure (Set.mem_union_left _ (a_mem_E i)))

theorem aGA_eq : aGA = [⟨ElemThree.a 0, a_mem_GA 0⟩, ⟨ElemThree.a 1, a_mem_GA 1⟩,
    ⟨ElemThree.a 2, a_mem_GA 2⟩, ⟨ElemThree.a 3, a_mem_GA 3⟩, ⟨ElemThree.a 4, a_mem_GA 4⟩,
    ⟨ElemThree.a 5, a_mem_GA 5⟩] := rfl

theorem coe_eltG_threeA :
    ((eltG aGA [0, 1, 0, 0, 1, 1] : ↥GA) : GL24) = ElemThree.a 1 * ElemThree.a 4 * ElemThree.a 5 := by
  rw [aGA_eq, eltG_threeA, Subgroup.coe_mul, Subgroup.coe_mul]

section Census

theorem tabCo1_threeE_census (t : ↥GA) (ht : t ∈ eSplit.T) (ht1 : t ≠ 1) :
    ∃ g x : ↥GA, t = g * x * g⁻¹ ∧
      (MRep (rootRows 0) (x : GL24) ∨ MRep (rootRows 1) (x : GL24) ∨
        MRep (mul (mul (aRows 1) (aRows 4)) (aRows 5)) (x : GL24)) := by
  rw [eSplit.T_eq_closure] at ht
  obtain ⟨g, hg⟩ := Certificates.certificate17332 t ht ht1
  rcases hg with h | h | h
  · exact ⟨g⁻¹, root 0, @eq_conj_of_conj ↥GA (Subgroup.toGroup GA) _ _ _ h,
      Or.inl (wordL_rep _)⟩
  · exact ⟨g⁻¹, root 1, @eq_conj_of_conj ↥GA (Subgroup.toGroup GA) _ _ _ h,
      Or.inr (Or.inl (wordL_rep _))⟩
  · refine ⟨g⁻¹, eltG aGA [0, 1, 0, 0, 1, 1], @eq_conj_of_conj ↥GA (Subgroup.toGroup GA) _ _ _ h,
      Or.inr (Or.inr ?_)⟩
    rw [coe_eltG_threeA]
    exact ((a_rep 1).mul (a_rep 4)).mul (a_rep 5)

end Census

end CFSG.HardMathSupport.Dickson.I271.TabCo1
