module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLieDefs
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.RankThree.PartOne.S15K.ProjSLBridge
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
public import CFSG.RankThree.Classical.SteinbergR3EHigherSymplecticOuterOrder
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.Dihedral.Glauberman.DicksonMaxB
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.LieType.Steinberg.CentralExt
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound)
open CFSG.RankThree.Classical (higher_symplectic_outer_order_divides_field_multiplier_bound)

variable {S : Type} [Group S]

theorem card_outer_dvd_two_of_psl_two_four (h : StatedClassicalModel S .PSL 2 2 2) :
    Nat.card (OuterAutomorphisms.Outer S) ∣ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  let φ : K ≃+* GaloisField 2 2 :=
    ClassicalModels.finiteFieldEquivGaloisField K 2 2 (by norm_num) hK
  obtain ⟨eA⟩ := Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
  exact CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six (Or.inl rfl)
    (((e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))).trans eA)

theorem card_outer_dvd_two_of_psl_field_two {n : ℕ} (hn : 3 ≤ n)
    (h : StatedClassicalModel S .PSL n 2 1) : Nat.card (OuterAutomorphisms.Outer S) ∣ 2 := by
  obtain ⟨e⟩ := RankThree.PartOne.projSL_of_statedClassicalModel h
  rw [Nat.card_congr (OuterAutomorphisms.equivalence
    (e.trans (RankThree.PartOne.S15K.projSLEquivProjectiveSL n _))).toEquiv]
  simpa using higher_linear_outer_order_divides_field_gcd_bound Nat.prime_two le_rfl hn
    (GaloisField.card 2 1 one_ne_zero)

theorem card_outer_dvd_six_of_psu_field_two {n : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel S .PSU n 2 1) : Nat.card (OuterAutomorphisms.Outer S) ∣ 6 := by
  obtain ⟨e⟩ := RankThree.PartOne.projSU_of_statedClassicalModel h
  rw [Nat.card_congr (OuterAutomorphisms.equivalence e).toEquiv]
  simpa using RankThree.PartTwo.Sec4.card_outer_projSU_dvd n 2 1 le_rfl (by omega)
    fun h3 => absurd h3.1 (by omega)

theorem card_outer_eq_one_of_psp_three_two (h : StatedClassicalModel S .PSp 3 2 1) :
    Nat.card (OuterAutomorphisms.Outer S) = 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr (OuterAutomorphisms.equivalence e).toEquiv]
  simpa using (higher_symplectic_outer_order_divides_field_multiplier_bound Nat.prime_two le_rfl
    le_rfl hK).1

theorem card_outer_dvd_three_of_suzuki_eight
    (h : Blueprint.SuzukiModel S 2 3) : Nat.card (OuterAutomorphisms.Outer S) ∣ 3 := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  obtain rfl : a = 1 := by omega
  rw [Nat.card_congr (OuterAutomorphisms.equivalence e).toEquiv]
  exact (LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd le_rfl hK).2

theorem mem_of_two_dvd_exceptionalOrders {t : StatedLieTag} {n f : ℕ}
    (h : 2 ∣ (exceptionalOrders t n 2 f).1) :
    (t, n, f) ∈ [(.PSL, 2, 2), (.PSL, 3, 1), (.PSL, 4, 1), (.PSU, 4, 1), (.PSp, 3, 1),
      (.G2, 0, 2), (.F4, 0, 1), (.POmegaPlus, 4, 1), (.PSU, 6, 1), (.twistedB2, 0, 3),
      (.twistedE6, 0, 1), (.PSL, 3, 2)] := by
  revert h
  unfold exceptionalOrders
  split <;> simp_all

theorem card_outer_le_eight_of_even_exceptional
    (hexc : EvenLieExceptionalOuterInput) [Finite S] {t : StatedLieTag} {n f : ℕ}
    (hm : Blueprint.LieModel S t n 2 f) (h2 : 2 ∣ (exceptionalOrders t n 2 f).1)
    (hL : (t, n, f) ≠ (.PSL, 3, 2)) : Nat.card (OuterAutomorphisms.Outer S) ≤ 8 := by
  have hcl := GriessNative.classical_of_lieModel hm
  have h8 : ∀ k : ℕ, 0 < k → k ≤ 8 → Nat.card (OuterAutomorphisms.Outer S) ∣ k →
      Nat.card (OuterAutomorphisms.Outer S) ≤ 8 := fun k hk hk8 hd =>
    (Nat.le_of_dvd hk hd).trans hk8
  have hmem := mem_of_two_dvd_exceptionalOrders h2
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact h8 2 (by norm_num) (by norm_num) (card_outer_dvd_two_of_psl_two_four (hcl (by decide)))
  · exact h8 2 (by norm_num) (by norm_num)
      (card_outer_dvd_two_of_psl_field_two le_rfl (hcl (by decide)))
  · exact h8 2 (by norm_num) (by norm_num)
      (card_outer_dvd_two_of_psl_field_two (by norm_num) (hcl (by decide)))
  · exact h8 6 (by norm_num) (by norm_num)
      (card_outer_dvd_six_of_psu_field_two le_rfl (hcl (by decide)))
  · rw [card_outer_eq_one_of_psp_three_two (hcl (by decide))]
    norm_num
  · exact hexc S .G2 0 2 (by decide) hm
  · exact hexc S .F4 0 1 (by decide) hm
  · exact (EvenSmallLie.OmegaEight.card_outer_le_six (hcl (by decide))).trans (by norm_num)
  · exact h8 6 (by norm_num) (by norm_num)
      (card_outer_dvd_six_of_psu_field_two (by norm_num) (hcl (by decide)))
  · exact h8 3 (by norm_num) (by norm_num)
      (card_outer_dvd_three_of_suzuki_eight (GriessNative.suzuki_of_lieModel hm).2)
  · exact hexc S .twistedE6 0 1 (by decide) hm
  · exact absurd rfl hL

end CFSG.ComponentClassification.Foote5
