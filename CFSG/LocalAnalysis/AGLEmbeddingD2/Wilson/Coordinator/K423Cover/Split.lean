module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent.Main

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent
open Item426Rest


theorem cover46_cases {X : Type} [Group X] [Finite X] (hlist : IsList46 X) (hX : IsQuasisimple X)
    (hZ : Subgroup.center X ≠ ⊥) (hnsl : ¬ IsSLThreePi X) :
    IsTripleCover X (alternatingGroup (Fin 6)) ∨ IsTripleCover X (alternatingGroup (Fin 7)) ∨
      IsTripleCover X (Blueprint.NativeSporadic.Carrier .M22) ∨
      IsTripleCover X (Blueprint.NativeSporadic.Carrier .J3) ∨
      IsTripleCover X (Blueprint.NativeSporadic.Carrier .McL) ∨
      IsTripleCover X (Blueprint.NativeSporadic.Carrier .ONan) ∨
      Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
      Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1) := by
  have hcov : ∀ {S : Type} [Group S], Subgroup.center S = ⊥ →
      IsExtOf X S (Multiplicative (ZMod 3)) → IsTripleCover X S :=
    fun hZS hext => (isTripleCover_iff_isExtOf hX hZS).mpr hext
  obtain ⟨hZJ3, hZMcL, hZON⟩ := Item426.center_J3_McL_ON
  have hZA : ∀ {n : ℕ}, 4 ≤ n → Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    fun hn => alternatingGroup.center_eq_bot (by simpa using hn)
  have hZM22 : Subgroup.center Blueprint.NativeSporadic.M22 = ⊥ := by
    have := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact Item426.center_eq_bot_of_isSimpleGroup (by rw [Item426.card_M22]; norm_num)
  rcases hlist with ⟨p, e, _, -, -, ⟨e1⟩⟩ |
      ⟨p, e, _, hp3, he1, -, hSL | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩ |
      ⟨p, _, hp3, hG2' | ⟨⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩⟩ |
      (⟨n, -, ⟨e1⟩⟩ | hA6' | hA7') | (⟨s, hs, ⟨e1⟩⟩ | ⟨s, hs, hext⟩) |
      (hchev | ⟨n, hn, hSL⟩) | (⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩) |
      ((⟨e, he1, -, ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩) | ⟨⟨e1⟩⟩ | ⟨-, hG23 | hU43'⟩)
  · exact (false_of_projSL hX hZ e1).elim
  · exact (false_of_slThreeEps hZ hnsl Fact.out (by omega) he1 hSL).elim
  · exact (false_of_projSL hX hZ e1).elim
  · exact (false_of_projSU hX hZ le_rfl he1 e1).elim
  · exact (false_of_chevalleyExceptional hX hZ (Or.inl rfl) hG2').elim
  · exact (false_of_projSp_any hX hZ e1).elim
  · exact (false_of_projSU hX hZ (by norm_num) le_rfl e1).elim
  · exact (false_of_projSL hX hZ e1).elim
  · exact (false_of_alternating_any hX hZ e1).elim
  · exact Or.inl (hcov (hZA (by norm_num)) hA6')
  · exact Or.inr (Or.inl (hcov (hZA (by norm_num)) hA7'))
  · exact (false_of_sporadic46 hX hZ hs e1).elim
  · simp only [sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (hcov hZM22 hext)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hcov hZJ3 hext))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hcov hZMcL hext)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hcov hZON hext))))))
  · rcases hchev with ⟨n, hn, ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩ |
      ⟨f, hG2' | hD4 | hSz | hF4 | hTits⟩
    · exact (false_of_projSL hX hZ e1).elim
    · exact (false_of_projSL hX hZ e1).elim
    · exact (false_of_projSU hX hZ le_rfl hn e1).elim
    · exact (false_of_projSp_any hX hZ e1).elim
    · exact (false_of_projSU hX hZ (by norm_num) hn e1).elim
    · exact (false_of_chevalleyExceptional hX hZ (Or.inl rfl) hG2').elim
    · exact (false_of_chevalleyExceptional hX hZ (Or.inr rfl) hD4).elim
    · exact (false_of_suzuki hX hZ hSz).elim
    · exact (false_of_reeTits hX hZ (Or.inl rfl) hF4).elim
    · exact (false_of_reeTits hX hZ (Or.inr rfl) hTits).elim
  · exact (false_of_slThreeEps hZ hnsl Nat.prime_two (by norm_num) hn hSL).elim
  · exact (false_of_projSL hX hZ e1).elim
  · exact (false_of_projSp_any hX hZ e1).elim
  · exact (false_of_projSU hX hZ (by norm_num) (by norm_num) e1).elim
  · exact (false_of_projSL hX hZ e1).elim
  · exact (false_of_projSU hX hZ le_rfl he1 e1).elim
  · exact (false_of_projSL hX hZ e1).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hG23))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hU43'))))))

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover
