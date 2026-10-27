module

public import CFSG.LocalAnalysis.RankThreeUC.K37HRGlue
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.RankThree.PartOne.N143.HighEvenU
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.LocalAnalysis.RankThreeUC.S15.K37
open CFSG.RankThree.PartTwo.Sec4.Census
  (IsThreeCenterCover TripleCoverLieIndex tripleCoverLie_of_griess)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open TauCeti

private theorem card_eq_two_aux {q : PrimePower} (h : q.card = 2) : q.p = 2 ∧ q.exponent = 1 := by
  rw [PrimePower.card_def] at h
  have hp : q.p ∣ 2 := by
    have : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [h] at this
    exact this
  have hp2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hp
  refine ⟨hp2, ?_⟩
  rw [hp2] at h
  have : (2 : ℕ) ^ q.exponent = 2 ^ 1 := by rw [h]; norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) this

theorem k37Rest₂Two_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : K37Rest₂Two := by
  intro X _ _ K E S hs hO
  exfalso
  obtain ⟨d, hc, m, q, hd, hq2⟩ := hO
  obtain ⟨φ, hφ, hker, h3, hodd⟩ := k37R_exists_cover hs.core hc
  have hidx := tripleCoverLie_of_griess hGA d ↥K hc
  obtain ⟨dd, hv⟩ := d
  obtain rfl : dd = .twistedA m q := hd
  have hrange := ((LieTypeIndex.valid_iff _).1 hv).1
  have hrange' : 2 ≤ m ∧ (m = 2 → 3 ≤ q.card) := hrange
  have hidx' : (3 ∣ m + 1 ∧ 3 ∣ q.card + 1) ∨ (m = 3 ∧ q.card = 3) := hidx
  have h5 : 5 ≤ m := by
    rcases hidx' with ⟨h31, -⟩ | ⟨-, h⟩
    · have := hrange'.2
      omega
    · omega
  obtain ⟨hp2, hf1⟩ := card_eq_two_aux hq2
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField q.p q.exponent
    q.exponent_pos
  obtain ⟨r', rfl⟩ : ∃ r', m = r' + 2 := ⟨m - 2, by omega⟩
  have eT : (CFSGIndex.lie ⟨.twistedA (r' + 2) q, hv⟩).Group ≃*
      StatedProj (StatedSU (r' + 2 + 1) (q.p ^ q.exponent) (GaloisField q.p (2 * q.exponent))) :=
    CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj (r' + 2) q hv
  let ψ : (CFSGIndex.lie ⟨.twistedA (r' + 2) q, hv⟩).Group ≃* unitaryPSU hU (r' + 2 + 1) :=
    eT.trans (unitaryPSUEquiv hU (n := r' + 2 + 1) (by omega)).symm
  let φ' : ↥K →* unitaryPSU hU (r' + 2 + 1) := ψ.toMonoidHom.comp φ
  have hφ' : Function.Surjective φ' := ψ.surjective.comp hφ
  have hkerφ : φ'.ker = φ.ker := by
    ext x
    simp [φ', MonoidHom.mem_ker]
  have hpq : 3 ∣ q.p ^ q.exponent + 1 := by
    rw [hp2, hf1]
    norm_num
  have h4 := CFSG.RankThree.PartOne.N143.succ_le_localRank_unitary_even hU hp2 hpq (r := r')
    (n := r' + 2 + 1) (by omega) φ' hφ' (hkerφ ▸ hker ▸ le_rfl) (hkerφ ▸ h3)
  exact k37R_false_of_four_le_localRank hs (show 4 ≤ localRank 3 ↥K by omega)

theorem k37Rest₂Two_holds
    : K37Rest₂Two :=
  k37Rest₂Two_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H
