module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3S67Arith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F2GD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.KRank
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem i67Cover_of_autAt
       (hA : I107AutAt) : I67Cover := by
  intro G _ _ p X L lab hp hp2 hX hL hrk hlab hm hEven
  haveI hsimple : IsSimpleGroup (PSimple p L) := (isQuasisimple_pQuot_of_glaPComponent hp hL).2
  have hperf := ltilde_perfect hL
  obtain ⟨e⟩ := ltilde_centre_equiv hL
  have hraw : GLARawDatum lab (fun R _ _ _ => (∃ a b : R, a * b ≠ b * a) ∧
      Nonempty (LTilde p L ⧸ Subgroup.center (LTilde p L) ≃* R)) := by
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono (fun R _ I F hQ => ?_)
      (rk2IsLabel_rawDatum hrk)
    obtain ⟨-, hna, ⟨θ⟩⟩ := hQ
    have hZ : Subgroup.center (PSimple p L) = ⊥ := center_eq_bot_of_quotient_nonab θ hna
    let e₀ : PSimple p L ⧸ Subgroup.center (PSimple p L) ≃* PSimple p L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact ⟨hna, ⟨e.trans (e₀.symm.trans θ)⟩⟩
  obtain ⟨R, _, I, F, ⟨-, ⟨θ⟩⟩, hmR⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists
    (CFSG.StandardType.Canonical.largeEvenRawDatum_markedModel hlab (fun R _ I F hq => hq.1)
      hraw)
  have hM : CFSG.StandardType.MarkedModel lab (LTilde p L ⧸ Subgroup.center (LTilde p L)) :=
    CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hmR
  obtain ⟨-, hT⟩ :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models _ _ _ _ _ hM
  have hle := CFSG.StandardType.center_torsion_le_native hperf (MulEquiv.refl _) hM hT
    Nat.prime_two
  have h2 : 2 ≤ Nat.card {z : Subgroup.center (LTilde p L) // z ^ 2 = 1} := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (LTilde p L)) 2
      (even_iff_two_dvd.mp hEven)
    have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := fun h => by
      rw [h, orderOf_one] at hz
      norm_num at hz
    haveI : Nontrivial {w : Subgroup.center (LTilde p L) // w ^ 2 = 1} :=
      ⟨⟨⟨1, one_pow 2⟩, ⟨z, hz2⟩, fun h => hz1 (congrArg Subtype.val h).symm⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.2 inferInstance
  rcases torsBound_two_mark_cases hlab (h2.trans hle) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have h1 := hA (PSimple p L) lab p hsimple hrk hlab hp hp2
    have h3 := upA107_le_two_of_small67 h hp hp2
    omega

theorem i67Cover_holds :
       I67Cover :=
  i67Cover_of_autAt (i107AutAt_holds (rk2InnRank_of_kRank rk2KRank) outRank107_holds)

end CFSG.LocalAnalysis.GLTheoremA
