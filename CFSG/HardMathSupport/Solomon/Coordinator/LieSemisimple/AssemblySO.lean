module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthAut
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthD4
public import CFSG.Yardstones.Md42047359a2a.Definitions
import CFSG.Adapters.TauCetiLieModels
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open TauCeti CFSG.Assembly.LowTwoRank


theorem lieSemisimpleCentSymplecticOrthogonal :
    CFSG.Yardstones.Md42047359a2a.LieSemisimpleCentSymplecticOrthogonal := by
  intro S _ _ _ _ idx hF he p hp hp2 hpc β hβp _
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  have hβ' : ∀ {T : Type} [Group T] (e' : S ≃* T), MulAut.congr e' β ^ p = 1 := fun e' => by
    rw [← map_pow, hβp, map_one]
  cases d with
  | B r q =>
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
    have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) = q.p ^ q.exponent :=
      CFSG.Models.card_fixedField_of (LieTypeIndex.characteristic_B r q)
        (LieTypeIndex.fieldExponent_B r q)
    have hpq : p ≠ q.p := (LieTypeIndex.characteristic_B r q) ▸ hpc
    have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · let e' := e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      refine perfectInLayer_of_congr e' β ?_
      exact perfectInLayer_projSp q.prime_p q.exponent_pos hK le_rfl
        (fun h => hr.2 ⟨rfl, by omega⟩) hp hp2 hpq _ (hβ' e')
    · by_cases hq2 : q.p = 2
      · let e' := e.trans
          (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3)
        refine perfectInLayer_of_congr e' β ?_
        exact perfectInLayer_projSp q.prime_p q.exponent_pos hK (by omega) (fun h => by omega)
          hp hp2 hpq _ (hβ' e')
      · have hm : StatedClassicalModel S .POmegaOdd r q.p q.exponent :=
          ⟨⟨q.prime_p, q.exponent_pos, hr3, hq2⟩, _, inferInstance,
            CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, hK,
            ⟨e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r
              q hv hq2 hr3)⟩⟩
        exact perfectInLayer_omega (Or.inl rfl) hm hp hp2 hpq (fun h => absurd h (by decide)) β
          hβp
  | C r q =>
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
    have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩) = q.p ^ q.exponent :=
      CFSG.Models.card_fixedField_of (LieTypeIndex.characteristic_C r q)
        (LieTypeIndex.fieldExponent_C r q)
    have hpq : p ≠ q.p := (LieTypeIndex.characteristic_C r q) ▸ hpc
    let e' := e.trans (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
    refine perfectInLayer_of_congr e' β ?_
    exact perfectInLayer_projSp q.prime_p q.exponent_pos hK (by omega) (fun h => by omega) hp hp2
      hpq _ (hβ' e')
  | D r q =>
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
    have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) = q.p ^ q.exponent :=
      CFSG.Models.card_fixedField_of (LieTypeIndex.characteristic_D r q)
        (LieTypeIndex.fieldExponent_D r q)
    have hpq : p ≠ q.p := (LieTypeIndex.characteristic_D r q) ▸ hpc
    have hm : StatedClassicalModel S .POmegaPlus r q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, hr⟩, _, inferInstance,
        CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, hK,
        ⟨e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r
          q hv)⟩⟩
    by_cases h43 : r = 4 ∧ p = 3
    · obtain ⟨rfl, rfl⟩ := h43
      exact perfectInLayer_omega_D4_three hm (Ne.symm hpq) β hβp
    · exact perfectInLayer_omega (Or.inr (Or.inl rfl)) hm hp hp2 hpq
        (fun _ h4 h3 => h43 ⟨h4, h3⟩) β hβp
  | twistedD r q =>
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
    have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) = q.p ^ q.exponent :=
      CFSG.Models.card_fixedField_of (LieTypeIndex.characteristic_twistedD r q)
        (LieTypeIndex.fieldExponent_twistedD r q)
    have hpq : p ≠ q.p := (LieTypeIndex.characteristic_twistedD r q) ▸ hpc
    obtain ⟨b, c, hirr, ⟨e'⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have hm : StatedClassicalModel S .POmegaMinus r q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, hr⟩, _, inferInstance,
        CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, hK, b, c, hirr, ⟨e.trans e'⟩⟩
    exact perfectInLayer_omega (Or.inr (Or.inr rfl)) hm hp hp2 hpq
      (fun h => absurd h (by decide)) β hβp
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
