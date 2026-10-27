module

public import CFSG.LieType.SeitzGeneration.OrthB3Gen
public import CFSG.LieType.SeitzGeneration.OrthHyperExNonsplit
public import CFSG.LieType.SeitzGeneration.UnitaryHyperNonsplit
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LieType.SeitzGeneration.OrthSmallMinus
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySelfDual

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank TauCeti OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

theorem orthHyperExSmallB3 : OrthHyperExSmallB3 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd - ⟨-, -, -, hO, q, hd, hq⟩
  change d = .B 3 q at hd
  subst hd
  have hqodd : q.p ≠ 2 := by
    rcases hO with ⟨r, q', h, -, hq'⟩ | ⟨r, q', h⟩ | ⟨r, q', h⟩
    · cases h
      exact hq'
    · cases h
    · cases h
  have hq' : p ≠ q.p := by simpa using hpd
  have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard := card_fixedField_eq_card ⟨.B 3 q, hv⟩ (q := q) (by simp)
  have hcard' : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) = q.p ^ q.exponent := by
    rw [hcard, PrimePower.card_def]
  have h2 : (2 : ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩)) ≠ 0 := by
    have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
      q.exponent_pos hcard'
    have : CharP ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) q.p := ringChar.of_eq hring
    intro h
    have : q.p ∣ 2 := (CharP.cast_eq_zero_iff
      ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) q.p 2).mp (by exact_mod_cast h)
    exact hqodd ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
  have hpKd : ¬ p ∣ Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩) := by
    rw [hcard']
    exact not_dvd_pow_of_ne hp q.prime_p hq'
  have hpK := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpKd
  have hreg := regular_quadOdd (K := ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩)) h2 le_rfl
  have hEq := commutator_orthogonalGroup_quadOdd
    (K := ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩)) h2 le_rfl
  obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadOdd 3 _) hEq hreg.1
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd 3 q hv hqodd le_rfl)
  exact exists_hyperGen_B3 h2 hπ ⟨hreg.1, hreg.2, hEq⟩ hp hp2 hpK (by rw [hcard]; exact hq)

theorem hyperExFor_orthogonal : HyperExFor fun d => IsOrthogonalIndex d.1 :=
  hyperExFor_orthogonal_of_small (orthHyperExSmall_of_B3 orthHyperExSmallB3)

theorem hyperExFor_isClassical : HyperExFor fun d => IsClassicalIndex d.1 :=
  hyperExFor_classical_of_orthogonal hyperExFor_orthogonal

end CFSG.LieType.SeitzGeneration
