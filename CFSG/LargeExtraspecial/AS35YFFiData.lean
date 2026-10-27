module

public import CFSG.LargeExtraspecial.AS35YFFi
public import CFSG.LargeExtraspecial.AS35XClass
public import CFSG.LargeExtraspecial.AS35YFOMin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35YF

theorem center_eq_bot_and_pGroup {L : Type*} [Group L] [Finite L]
    (hF : CFSG.fittingSubgroup L ≤ center L) :
    center (L ⧸ center L) = ⊥ ∧
      (∀ N : Subgroup (L ⧸ center L), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      ∀ N : Subgroup (L ⧸ center L), N.Normal → IsPGroup 3 N → N = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨AS35X.eq_bot_of_nilpotent hF _ inferInstance inferInstance,
    fun N hN hp => AS35X.eq_bot_of_nilpotent hF N hN hp.isNilpotent,
    fun N hN hp => AS35X.eq_bot_of_nilpotent hF N hN hp.isNilpotent⟩

end AS35YF

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem asc_solvable_of_noNormalTwo (hP : S14.Asc512PbarStmt) (h58 : S14.Asc512FiveEightStmt)
    (hS : S.SixHyp) {g : G} (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    (hno2 : S12NoNormalTwo (fischerQ S.EhatAsc ⊓
      centralizer {(QuotientGroup.mk (ascTL htD htM) : S.LbarAsc ⧸ center S.LbarAsc)})) :
    Group.IsSolvable (fischerQ S.EhatAsc ⊓
      centralizer {(QuotientGroup.mk (ascTL htD htM) : S.LbarAsc ⧸ center S.LbarAsc)} :
        Subgroup (S.LbarAsc ⧸ center S.LbarAsc)) := by
  by_contra hns
  have hPx := (hP G S hS g htD htM).2.1
  have hcen := (hP G S hS g htD htM).2.2.2.1
  have hPn := (hP G S hS g htD htM).2.2.2.2.1
  have hPM : S.PbarAsc g ≤ S.Mbar := Subgroup.map_le_range S.ρ _
  have hPt := AS35X.commute_of_center hPx.2.2.2 hcen
  have h58' : ∀ X : Subgroup S.O, X ≤ S.Mbar →
      (∀ x ∈ X, x * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * x) →
      (∀ p ∈ S.PbarAsc g, ∀ x ∈ X, p * x * p⁻¹ ∈ X) → Odd (Nat.card X) → Nat.card X ≤ 3 :=
    fun X hXM hXt hXP hodd =>
      h58 G S hS g htD htM X hXM hXt hXP (AS35X.oddCore_sup_layer_eq_top hodd)
  exact AS35X.false_of_triality (hDL := subset_closure) Setting.LbarAsc_le_Mbar_X hPM
    (S.ρ_mem_DbarAsc htD htM) (fun m hm d hd => S.conj_mem_DbarAsc_L hm hd)
    (fun d hd => Setting.mul_self_of_mem_DbarAsc_X hd) Setting.center_noInvol_X hPx.1 hPt
    hPn h58' hns hno2

theorem asc_orderOf_mul_mem (hS : S.SixHyp) (hst : S.Asc512Standing) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    (hnd : ¬ InspNondeg _ S.EhatAsc) :
    ∀ d ∈ S.EhatAsc, ∀ e ∈ S.EhatAsc, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
  intro d hd e he
  have hle := (transpositionData_X hS hst (S.ρ_mem_DbarAsc htD htM)).ord d hd e he
  have hne : orderOf (d * e) ≠ 4 := fun h => hnd ⟨d, hd, e, he, h⟩
  have hpos : 0 < orderOf (d * e) := orderOf_pos _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

theorem asc_orderOf_eq_two (hS : S.SixHyp) (hst : S.Asc512Standing) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) :
    ∀ d ∈ S.EhatAsc, orderOf d = 2 := fun d hd =>
  have hD := transpositionData_X hS hst (S.ρ_mem_DbarAsc htD htM)
  orderOf_eq_prime (by rw [pow_two]; exact hD.invol d hd) (hD.ne_one d hd)

end Setting

namespace S14

theorem asc512FischerData_of (hTri : FischerTrialityInput) (hP : Asc512PbarStmt)
    (h58 : Asc512FiveEightStmt) : Asc512FischerDataStmt := by
  intro G _ _ S hS hst hnd
  obtain ⟨t, htD⟩ := S.DSet_nonempty hS.sixFour hS.hSet_nonempty
  have hconj : ∃ h : G, h * S.z * h⁻¹ = t := Setting.exists_conj_of_mem_DSet S htD
  obtain ⟨g, rfl⟩ := hconj
  have htM := Setting.mem_M_of_mem_ESet S hS.sixFour htD.1
  have hclass := Setting.EhatAsc_eq_isConj_X hS hst (S.ρ_mem_DbarAsc htD htM)
  have hinv := Setting.asc_orderOf_eq_two hS hst htD htM
  have hprod := Setting.asc_orderOf_mul_mem hS hst htD htM hnd
  have hgen : closure S.EhatAsc = ⊤ := Setting.asc_closure_Ehat
  have hFit : CFSG.fittingSubgroup S.LbarAsc ≤ center S.LbarAsc := hst.fitting_le_center
  have hc := AS35YF.center_eq_bot_and_pGroup (L := S.LbarAsc) hFit
  have hcenter := hc.1
  have h2 := hc.2.1
  have h3 := hc.2.2
  have hPair : CFSG.Blueprint.Fischer.Pair (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc :=
    ⟨inferInstance, ⟨_, hclass⟩, hinv, hprod, hgen⟩
  refine ⟨⟨_, hclass⟩, hinv, hprod, hgen, hcenter, ?_⟩
  by_cases hcos : ∀ d ∈ S.EhatAsc, ∀ e ∈ S.EhatAsc, d * e ∈ fischerQ S.EhatAsc
  · exact (isSimpleGroup_commutator_iff hPair hcenter h2 h3).2 hcos
  exfalso
  push Not at hcos
  have hT := hTri _ _ hPair hcenter h2 h3 hcos (QuotientGroup.mk (Setting.ascTL htD htM))
    ⟨Setting.ascTL htD htM, S.ρ_mem_DbarAsc htD htM, rfl⟩
  exact hT.1 (Setting.asc_solvable_of_noNormalTwo hP h58 hS htD htM hT.2)

end S14

end CFSG.LargeExtraspecial
