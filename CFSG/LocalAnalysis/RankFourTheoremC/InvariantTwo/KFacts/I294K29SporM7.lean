module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporWit
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporOut
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCarrierSimple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

theorem sporadicClassWitnessNative_M_of_Gmat {p : ℕ} [Fact p.Prime]
    (hG : ∀ s : CFSG.Monster.Generated.Gmat, orderOf s = p → RankThreeWitness p s)
    (hrec : ∀ (T : Type) [Group T] [Finite T],
      Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.Carrier .M) →
        Nonempty (T ≃* CFSG.Monster.Generated.Gmat)) :
    ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.Carrier .M) →
      ∀ x : S, orderOf x = p → RankThreeWitness p x := by
  intro S _ _ he x hx
  obtain ⟨f⟩ := hrec S he
  exact RankThreeWitness.of_mulEquiv f (hG (f x) (by rw [MulEquiv.orderOf_eq]; exact hx))

section CertificateInstances

open CFSG.Monster.Generated CFSG.AGLEmbedding CFSG.AGLEmbedding.Norton.MON5_7


@[expose] noncomputable def sevenSpec : ModuleSpec Gmat 7 where
  n := 3
  m := 0
  a := ![dG, zG, eG]
  g := fun j => j.elim0
  M := fun j => j.elim0
  comm := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact dG_zG_comm
    · exact dG_eG_comm
    · exact dG_zG_comm.symm
    · rfl
    · exact zG_eG_comm
    · exact dG_eG_comm.symm
    · exact zG_eG_comm.symm
    · rfl
  pow := by
    intro i
    fin_cases i
    exacts [dG_pow, zG_pow, eG_pow]
  indep := seven_indep
  act := fun j => j.elim0

theorem rankThreeWitness_Gmat_seven (s : Gmat) (hs : orderOf s = 7) : RankThreeWitness 7 s := by
  have hEA : CFSG.Open.IsElemAbelian 7 (sevenSpec).span :=
    ⟨inferInstance, fun x hx => (sevenSpec).pow_eq_one_of_mem hx⟩
  have hcard : Nat.card (sevenSpec).span = 7 ^ 3 := (sevenSpec).card_span Nat.prime_seven
  have hd : dG ∈ (sevenSpec).span := Subgroup.subset_closure ⟨(0 : Fin 3), rfl⟩
  have hz : zG ∈ (sevenSpec).span := Subgroup.subset_closure ⟨(1 : Fin 3), rfl⟩
  rcases CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus.monsterSevenClasses
    s hs with h | h <;> obtain ⟨c, hc⟩ := isConj_iff.1 h
  · exact rankThreeWitness_of_conj_mem (MulEquiv.refl Gmat) hEA hcard c (by
      simpa [hc] using hd)
  · exact rankThreeWitness_of_conj_mem (MulEquiv.refl Gmat) hEA hcard c (by
      simpa [hc] using hz)

end CertificateInstances

section CertificateInstancesNative


theorem sporadicClassWitnessAt_M_seven : SporadicClassWitnessAt .M 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  refine sporadicClassWitnessAt_of_native
    (sporadicClassWitnessNative_M_of_Gmat rankThreeWitness_Gmat_seven ?_)
  intro T _ _ ⟨e⟩
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
    CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
  haveI : IsSimpleGroup T := e.isSimpleGroup
  exact CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e

end CertificateInstancesNative

end CFSG.LocalAnalysis.RankFourTheoremC
