module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430AltTrans
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCTwoLocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

private theorem exists_elemAbelian_27_of_mulEquiv {X S : Type} [hX : Group X] [Group S]
    [Finite S] (b : X ≃* S) {A : Subgroup X} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAc : Nat.card A = 3 ^ 4) :
    ∃ E : Subgroup S, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 := by
  have hA' : CFSG.Open.IsElemAbelian 3 (A.map b.toMonoidHom) := hA.map _
  have hA'c : Nat.card (A.map b.toMonoidHom) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective b.injective, hAc]
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (n := 3) Nat.prime_three
    hA'.isPGroup (by rw [hA'c]; norm_num)
  refine ⟨B.map (A.map b.toMonoidHom).subtype, hA'.mono ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hB]


theorem i1430M23ON_holds : I1430M23ON := by
  intro H _ _ _ _ hcat h1
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  have hcen : Subgroup.center H = ⊥ := Subgroup.card_eq_one.1 h1
  let e' : H ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hcen.symm)).trans e
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  obtain ⟨A, hA, hAc⟩ := CFSG.SectionRank.ON_elementary_three_rank_four
  obtain ⟨E, hE, hEc⟩ :=
    exists_elemAbelian_27_of_mulEquiv (hX := Units.instGroup) (b0.trans e'.symm) hA hAc
  obtain ⟨T, hT, hT2, hTN⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.input20_29_holds H ⟨e'⟩ E hE hEc
  rw [hcen, pRank_bot_eq_zero 3 (by norm_num), add_zero]
  exact ⟨T, E, hT, hT2, hTN, hE, hEc⟩

end CFSG.LocalAnalysis.GLTheoremA.S8.L84

end
