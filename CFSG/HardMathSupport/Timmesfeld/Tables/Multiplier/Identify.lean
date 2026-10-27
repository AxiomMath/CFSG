module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Basic
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.CompCenterNineU43
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.Blueprint.Multiplier TauCeti
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.Open (GriessAllModelsStatement)
open CFSG.LieType.Multipliers.U43 (X₀ F9)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.Sec4 (Spor)
open CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def sporadicMultiplierOrder : TauCeti.SporadicName → ℕ
  | .M12 => 2 | .M22 => 12 | .J2 => 2 | .J3 => 3 | .HS => 2 | .McL => 3 | .Suz => 6
  | .Ru => 2 | .ONan => 3 | .Co1 => 2 | .Fi22 => 6 | .Fi24Prime => 3 | .B => 2 | _ => 1

@[expose] def SporadicMultipliers : Prop :=
  (∀ s : TauCeti.SporadicName,
      Nat.card (hopfMultiplier (Spor s)) = sporadicMultiplierOrder s) ∧
    Nat.card (hopfMultiplier CFSG.Blueprint.NativeSporadic.ON) = 3

theorem sporadicMultiplierOrder_dvd_twelve (s : TauCeti.SporadicName) :
    sporadicMultiplierOrder s ∣ 12 := by
  cases s <;> decide

theorem card_center_dvd_twelve (hSpM : SporadicMultipliers) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (s : TauCeti.SporadicName)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.sporadic s).Group) :
    Nat.card (Subgroup.center K) ∣ 12 := by
  have hq' : CFSG.IsQuasisimple K :=
    ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      K hq⟩
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq' e
  rw [hSpM.1 s] at hdvd
  exact hdvd.trans (sporadicMultiplierOrder_dvd_twelve s)

theorem nonempty_mulEquiv_X₀_of_classical {G : Type} [Group G]
    (h : StatedClassicalModel G .PSU 4 3 1) : Nonempty (G ≃* X₀) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card F9 := by
    rw [← Nat.card_eq_fintype_card, hK, CFSG.LieType.Multipliers.U43.F9.card_eq]
    norm_num
  exact ⟨e.trans (CFSG.Fischer.Classification.Recognition.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 4 (3 ^ 1))⟩

theorem lie_center_nine_iso (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (d : ValidLieTypeIndex)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group)
    (hc : 9 ≤ Nat.card {z : Subgroup.center K // z ^ 3 = 1}) :
    Nonempty (K ⧸ Subgroup.center K ≃* X₀) ∧
      Nat.card {z : Subgroup.center K // z ^ 3 = 1} ≤ 9 ∧
      Nat.card (Outer (K ⧸ Subgroup.center K)) = 8 := by
  obtain ⟨t, n, p, f, hm⟩ := exists_lieModel d
  have hle := center_torsion_le hGA hq e hm Nat.prime_three
  obtain ⟨rfl, rfl, rfl, rfl⟩ := eq_psu_four_three_of_nine_le (hc.trans hle)
  have h9 : torsBound 3 .PSU 4 3 1 = 9 := by
    simp [torsBound, genericOrders, exceptionalOrders, tors]
  rw [h9] at hle
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hm
  swap
  · exact absurd h0 (by norm_num)
  refine ⟨?_, hle, ?_⟩
  · obtain ⟨e'⟩ := nonempty_mulEquiv_X₀_of_classical hcl
    exact ⟨e.trans e'⟩
  · obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ := hcl
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 F :=
      ⟨Nat.prime_three, le_rfl, by rw [hF]; norm_num⟩
    exact (CFSG.AGLEmbedding.CompCenterNine.outer_facts_of_psu43 hU (by norm_num)
      (e.trans e')).1

theorem card_le_torsion_center {L : Type} [Group L] [Finite L] {p : ℕ} {E : Subgroup L}
    (hE : CFSG.Open.IsElemAbelian p E) (hZ : E ≤ Subgroup.center L) :
    Nat.card E ≤ Nat.card {z : Subgroup.center L // z ^ p = 1} := by
  refine Nat.card_le_card_of_injective (fun x => ⟨⟨x.1, hZ x.2⟩, Subtype.ext (hE.2 x.1 x.2)⟩) ?_
  intro x y hxy
  exact Subtype.ext (congrArg (fun w : {z : Subgroup.center L // z ^ p = 1} => (w.1 : L)) hxy)

theorem identify_of_two_le_pRank_center (hGA : GriessAllModelsStatement)
    (hSpM : SporadicMultipliers) {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) (hK : CFSG.Open.IsKGroup L) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h2 : 2 ≤ CFSG.Open.pRank p (Subgroup.center L)) :
    p = 3 ∧ Nonempty (L ⧸ Subgroup.center L ≃* X₀) ∧
      Nat.card {z : Subgroup.center L // z ^ 3 = 1} = 9 ∧
      Nat.card (Outer (L ⧸ Subgroup.center L)) = 8 := by
  obtain ⟨E, hEZ, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center L)
  have hp2' : p ^ 2 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hp.pos h2
  have hEdvd : p ^ 2 ∣ Nat.card (Subgroup.center L) := by
    refine (pow_dvd_pow p h2).trans ?_
    rw [← hEcard]
    exact Subgroup.card_dvd_of_le hEZ
  have hcube := hp2'.trans (card_le_torsion_center hEab hEZ)
  have hp3 : 3 ≤ p := hp.two_le.lt_of_ne (Ne.symm hp2)
  have hq' : CFSG.IsQuasisimple L :=
    ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      L hq⟩
  rcases centralQuotient_family hq hK with ⟨n, ⟨e⟩⟩ | ⟨d, ⟨e⟩⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    have : Group.IsPerfect L := ⟨hq.1⟩
    have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
    have hn := Tables.Alt.five_le_of_centerQuotient hq.1 e
    have := Tables.Alt.pRank_center_le_one hn e hp hp2
    omega
  · obtain ⟨t, n, p', f, hm⟩ := exists_lieModel d
    have hle := center_torsion_le hGA hq e hm hp
    by_cases hp5 : 5 ≤ p
    · exfalso
      have h1 := hcube.trans (hle.trans (torsBound_le_of_five_le hp5 t n p' f))
      have h2' : p < p ^ 2 := by nlinarith
      omega
    · have hp3' : p = 3 := by
        have := hp.eq_one_or_self_of_dvd 2
        interval_cases p <;> simp_all
      subst hp3'
      obtain ⟨h1, h2', h3⟩ := lie_center_nine_iso hGA hq d e (by omega)
      exact ⟨rfl, h1, le_antisymm h2' (by omega), h3⟩
  · exfalso
    have hd := card_center_dvd_twelve hSpM hq s e
    have h12 : p ^ 2 ∣ 12 := hEdvd.trans hd
    have := Nat.le_of_dvd (by norm_num) h12
    have hp5 : p ≤ 3 := by nlinarith
    obtain rfl : p = 3 := by omega
    omega

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
