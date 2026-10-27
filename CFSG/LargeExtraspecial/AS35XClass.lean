module

public import CFSG.LargeExtraspecial.AS35XQuot
public import CFSG.LargeExtraspecial.AS35XTriGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.RankThree.OrthogonalInvolutions

namespace AS35X

theorem commute_of_center {O : Type*} [Group O] {P : Subgroup O} {t : O}
    (hcard : Nat.card (center P) = 2)
    (hcen : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x = 1 ∨ x = t) :
    ∀ p ∈ P, p * t = t * p := by
  have : Finite (center P) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Nontrivial (center P) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨c, hc1⟩ := exists_ne (1 : center P)
  have hcP := (c : P).2
  have hcc : ∀ y ∈ P, ((c : P) : O) * y = y * c := fun y hy =>
    (congrArg Subtype.val (mem_center_iff.mp c.2 ⟨y, hy⟩)).symm
  rcases hcen _ hcP hcc with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hc1
  · intro p hp
    rw [← h]
    exact (hcc p hp).symm

theorem oddCore_sup_layer_eq_top {X : Type*} [Group X] (hX : Odd (Nat.card X)) :
    CFSG.oddCore X ⊔ CFSG.layer X = ⊤ := by
  refine eq_top_iff.mpr (le_trans ?_ le_sup_left)
  exact le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩

end AS35X

namespace S14

theorem asc512ClassifyStmt_of_inputs (hARS : CFSG.Timmesfeld.ARSInput)
    (hTri : FischerTrialityInput) (hF : S12FischerStatement) (hP : Asc512PbarStmt)
    (h58 : Asc512FiveEightStmt) : Asc512ClassifyStmt := by
  intro G _ _ S hS hst
  obtain ⟨t, htD⟩ := S.DSet_nonempty hS.sixFour hS.hSet_nonempty
  have htM : t ∈ S.M := S.mem_M_of_mem_ESet hS.sixFour htD.1
  obtain ⟨g, rfl, -, -⟩ := htD.1
  have htb : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := S.ρ_mem_DbarAsc htD htM
  have hD := Setting.transpositionData_X hS hst htb
  have hFit := hst.fitting_le_center
  by_cases hnd : InspNondeg _ S.EhatAsc
  · refine Or.inl ⟨hnd, ?_⟩
    have hA := hD.arsHyp (AS35X.center_trivial_top hFit) (AS35X.noNormalTwo_top hFit) hnd
    exact AS35X.outcome_of_mulEquiv Subgroup.topEquiv (hARS _ _ hA)
  · refine Or.inr ⟨hnd, ?_⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨-, hPx, -, hcen, hPn, -, -⟩ := hP G S hS g htD htM
    have hPM : S.PbarAsc g ≤ S.Mbar := Subgroup.map_le_range S.ρ _
    have hPt := AS35X.commute_of_center hPx.2.2.2 hcen
    have h58' : ∀ X : Subgroup S.O, X ≤ S.Mbar →
        (∀ x ∈ X, x * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * x) →
        (∀ p ∈ S.PbarAsc g, ∀ x ∈ X, p * x * p⁻¹ ∈ X) → Odd (Nat.card X) → Nat.card X ≤ 3 :=
      fun X hXM hXt hXP hodd =>
        h58 G S hS g htD htM X hXM hXt hXP (AS35X.oddCore_sup_layer_eq_top hodd)
    have hloc : S12NoNormalTwo (fischerQ S.EhatAsc ⊓
          centralizer {QuotientGroup.mk' (center S.LbarAsc) ⟨_, subset_closure htb⟩}) →
        Group.IsSolvable (fischerQ S.EhatAsc ⊓
          centralizer {QuotientGroup.mk' (center S.LbarAsc) ⟨_, subset_closure htb⟩} :
          Subgroup (S.LbarAsc ⧸ center S.LbarAsc)) := fun h2 => by
      by_contra hns
      exact AS35X.false_of_triality (hDL := subset_closure) Setting.LbarAsc_le_Mbar_X hPM htb
        (fun m hm d hd => S.conj_mem_DbarAsc_L hm hd)
        (fun d hd => Setting.mul_self_of_mem_DbarAsc_X hd) Setting.center_noInvol_X hPx.1 hPt
        hPn h58' hns h2
    have hFis := hD.fischer hTri hF (AS35X.center_trivial_top hFit)
      (AS35X.noNormalTwo_top hFit) (AS35X.pGroup_eq_bot_top hFit) hnd hloc
    exact AS35X.s12FischerConclusion_of_mulEquiv Subgroup.topEquiv (fun _ => Iff.rfl) hFis

end S14

end CFSG.LargeExtraspecial
