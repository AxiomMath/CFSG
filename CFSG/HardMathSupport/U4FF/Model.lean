module

public import CFSG.LocalAnalysis.EvenBN.U4.Setup
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.EvenBN.U4
  CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.SQTK CFSG.ClassicalGroups.UnitaryFlag

theorem one_le_of_isU4Group {S : Type} [CommGroup S] {n : ℕ} {L : Subgroup (MulAut S)}
    (hL : IsU4Group n L) : 1 ≤ n := by
  obtain ⟨d, ⟨q, hp, he, hd⟩, -⟩ := hL
  rw [← he]
  exact q.exponent_pos

theorem exists_equiv_gramSU {S : Type} [CommGroup S] {n : ℕ} {L : Subgroup (MulAut S)}
    (hL : IsU4Group n L) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 n K),
      Nonempty (↥L ≃* gramSU h (miyamotoJ4 K)) := by
  have hn := one_le_of_isU4Group hL
  obtain ⟨d, ⟨q, hp, he, hd⟩, ⟨e⟩⟩ := hL
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hmodel := statedClassicalModel_twistedA 3 q hv e
  rw [hp, he] at hmodel
  have hlie : CFSG.Blueprint.LieModel (↥L) .PSU 4 2 n :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).2 hmodel
  exact exists_mulEquiv_gramSU hn hlie

theorem exists_equiv_statedProj {S : Type} [CommGroup S] {n : ℕ} {L : Subgroup (MulAut S)}
    (hL : IsU4Group n L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
      Nonempty (↥L ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Open.StatedSU 4 (2 ^ n) F)) := by
  obtain ⟨d, ⟨q, hp, he, hd⟩, ⟨e⟩⟩ := hL
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have h := statedClassicalModel_twistedA 3 q hv e
  obtain ⟨-, F, hF, hFin, hcard, ⟨e'⟩⟩ := h
  rw [hp, he] at hcard e'
  exact ⟨F, hF, hFin, hcard, ⟨e'⟩⟩

theorem exists_equiv_SU {S : Type} [CommGroup S] {n : ℕ} {L : Subgroup (MulAut S)}
    (hL : IsU4Group n L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (_ : Nat.card K = (2 ^ n) ^ 2),
      Nonempty (↥L ≃* ↥(CFSG.LieType.Universal.Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 n) 4)) := by
  obtain ⟨F, _, hFfin, hcard, ⟨e⟩⟩ := exists_equiv_statedProj hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hcard
  have hn := one_le_of_isU4Group hL
  have hcop : Nat.Coprime 4 (2 ^ n + 1) := by
    have h2 : Nat.Coprime 2 (2 ^ n + 1) := by
      rw [Nat.coprime_two_left]
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    simpa using Nat.Coprime.pow_left 2 h2
  have hZ : Subgroup.center (CFSG.Open.StatedSU 4 (2 ^ n) F) = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSU_eq_bot_of_coprime hcard hn (by norm_num)
      hcop
  have hsc : (CFSG.Open.StatedScalars (Fin 4) F).subgroupOf
      (CFSG.Open.StatedSU 4 (2 ^ n) F) = ⊥ := by
    refine eq_bot_iff.2 ?_
    refine (CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center 4 (2 ^ n)).trans ?_
    rw [hZ]
  let e2 : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Open.StatedSU 4 (2 ^ n) F) ≃*
      CFSG.Open.StatedSU 4 (2 ^ n) F :=
    (QuotientGroup.quotientMulEquivOfEq hsc).trans QuotientGroup.quotientBot
  exact ⟨F, inferInstance, hFfin, inferInstance, hcard,
    ⟨(e.trans e2).trans (CFSG.LieType.Universal.Unitary.equivStatedSU hcard 4).symm⟩⟩

end CFSG.HardMathSupport.U4FF
