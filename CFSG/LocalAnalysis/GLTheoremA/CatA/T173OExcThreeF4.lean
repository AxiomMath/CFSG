module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeRankF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeF4Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpine
public import CFSG.LocalAnalysis.GLTheoremA.S9.ClosingB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
open CFSG.LieType.Steinberg (Sp.x)
open CFSG.RankThree.CentralCover (sl2Upper coe_sl2Upper sl2Upper_add sl2Upper_zero)
open scoped commutatorElement MatrixGroups


variable {F : Type} [Field F] [Finite F]

private theorem exists_conj_le_C3Levi_or_B3Levi_of_stdElt (hF : Nat.card F = 2)
    [Finite ↥(adjointGroup .F4 F)] {A : Subgroup ↥(adjointGroup .F4 F)} {d : ↥(adjointGroup .F4 F)}
    (hA27 : Nat.card A = 27) (hd : IsStdElt 3 A d)
    {T : Subgroup ↥(adjointGroup .F4 F)} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hTN : innerClosure A d ⊔ A ≤ Subgroup.normalizer (T : Set ↥(adjointGroup .F4 F))) :
    ∃ g : ↥(adjointGroup .F4 F),
      (A.map (MulAut.conj g).toMonoidHom ≤ C3Levi F ∧ stdLayer (MulAut.conj g d) ≤ C3Levi F) ∨
        (A.map (MulAut.conj g).toMonoidHom ≤ B3Levi F ∧ stdLayer (MulAut.conj g d) ≤ B3Levi F) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hK : stdLayer d ≤ Subgroup.normalizer (T : Set ↥(adjointGroup .F4 F)) :=
    (CFSG.LocalAnalysis.GLTheoremA.S9.Cl.le_closureIn_self (stdLayer d)
      (Subgroup.normalizer (A : Set ↥(adjointGroup .F4 F)))).trans (le_sup_left.trans hTN)
  have hAN : A ≤ Subgroup.normalizer (T : Set ↥(adjointGroup .F4 F)) := le_sup_right.trans hTN
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (hA27.trans (by norm_num))
  obtain ⟨g, J, hJ, hAL, hKP⟩ := exists_conj_le_parabolicLevi_of_le_normalizer .F4 hT hT2 hAN hK
    Nat.prime_three (by norm_num) hA3
  have hstd := isStdElt_map (MulAut.conj g) hd
  have hdL : ((MulAut.conj g d : ↥(adjointGroup .F4 F)) : ModGL .F4 F) ∈ parabolicLevi .F4 F J :=
    hAL (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hd.1))
  have hKP' : (stdLayer (MulAut.conj g d)).map (adjointGroup .F4 F).subtype ≤
      parabolicSubgroup .F4 F J := by
    rw [stdLayer_map_mulEquiv]
    exact hKP
  have hKL := map_subtype_le_parabolicLevi_of_isComponentOf .F4 J hstd.2.2.2.1 hdL hKP'
  have hAcard : Nat.card ((A.map (MulAut.conj g).toMonoidHom).map (adjointGroup .F4 F).subtype) =
      27 := by
    rw [Subgroup.card_map_of_injective (adjointGroup .F4 F).subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hA27]
  rcases parabolicLevi_le_rootSpan_c3_or_b3 hF hJ hAL hAcard with h | h
  · refine ⟨g, Or.inl ⟨fun z hz => ?_, fun z hz => ?_⟩⟩
    · exact mem_C3Levi_iff.2 (h (hAL (Subgroup.mem_map_of_mem _ hz)))
    · exact mem_C3Levi_iff.2 (h (hKL (Subgroup.mem_map_of_mem _ hz)))
  · refine ⟨g, Or.inr ⟨fun z hz => ?_, fun z hz => ?_⟩⟩
    · exact mem_B3Levi_iff.2 (h (hAL (Subgroup.mem_map_of_mem _ hz)))
    · exact mem_B3Levi_iff.2 (h (hKL (Subgroup.mem_map_of_mem _ hz)))

theorem stdVanishes_three_F4_two (hF : Nat.card F = 2) [Finite ↥(adjointGroup .F4 F)]
    {A : Subgroup ↥(adjointGroup .F4 F)} {d : ↥(adjointGroup .F4 F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d) : StdVanishes A d := by
  rintro ⟨T, hT, hT2, hTN⟩
  obtain ⟨-, hcard, -⟩ := hA
  have hA27 : Nat.card A = 27 := by rw [hcard, glaTwoLocalRank_three_F4_two hF]; norm_num
  obtain ⟨g, ⟨hAM, hKM⟩ | ⟨hAM, hKM⟩⟩ :=
    exists_conj_le_C3Levi_or_B3Levi_of_stdElt hF hA27 hd hT hT2 hTN
  · exact false_of_stdLayer_le_C3Levi hF ((isStdElt_map_iff (MulAut.conj g)).2 hd) hAM hKM
  · exact false_of_stdLayer_le_B3Levi hF ((isStdElt_map_iff (MulAut.conj g)).2 hd) hAM hKM

theorem modelFactV_three_F4_two [Finite ↥(adjointGroup .F4 F)] (hF : Nat.card F = 2) :
    ModelFactV 3 ↥(adjointGroup .F4 F) :=
  fun _ _ hA hd => stdVanishes_three_F4_two hF hA hd

theorem modelFactExcThree_F4 : ModelFactExcThree .F4 :=
  fun _ _ _ _ hF => (modelFactV_three_F4_two hF).modelFactO

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
