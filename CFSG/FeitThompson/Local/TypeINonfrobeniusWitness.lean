module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.OddOrder.ComplementPlaneCentralizerWitness
import CFSG.FeitThompson.Local.TypeIExteriorFixedElementPowers
import CFSG.FeitThompson.OddOrder.InvariantHallComplement
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Foundations.SolvableHallExistence

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson.Prep05
open CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G]

theorem hallCoreOf_eq_hallCoreIn (M : Subgroup G) : hallCoreOf M = Prep09.hallCoreIn M := (rfl)

theorem centralizerIn_eq_centIn (X Y : Subgroup G) :
    centralizerIn X Y = centIn X (Y : Set G) := (rfl)

theorem hallCoreOf_ne_bot [Finite G] {M : Subgroup G} (h : IsTypeI M) : hallCoreOf M ≠ ⊥ := by
  rw [hallCoreOf_eq]
  simp [Subgroup.map_eq_bot_iff, M.ker_subtype, h.hallCore_ne_bot]

theorem exists_isPPlane_le [Finite G] {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (hrank : elementaryAbelianPRank p ↥P = 2) : ∃ A : Subgroup G, A ≤ P ∧ IsPPlane p A := by
  have h2 : (2 : ℕ) ∈ elementaryAbelianRanks p ↥P := by
    rw [← hrank]
    exact elementaryAbelianPRank_mem_elementaryAbelianRanks hp.one_lt
  obtain ⟨B, hBcomm, hBexp, hBcard⟩ := (mem_elementaryAbelianRanks_iff_exists_subgroup hp).1 h2
  refine ⟨B.map P.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact (isElementaryAbelianSubgroup_iff.2 ⟨hBcomm, hBexp⟩).map P.subtype
  · rw [Subgroup.card_subtype, hBcard]

theorem FPF_type_i_nonfrobenius_witness
    (h₁ : Statements.FTS_type_I_complement_structure.{u})
    (h₂ : Statements.FTS_type_I_dade_support.{u}) :
    Statements.FPF_type_i_nonfrobenius_witness.{u} := by
  intro G _ _ hG M hM hMI p hp hrank hpK P hP
  have hfp : Fact p.Prime := ⟨hp⟩
  have hG' : IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hPM, hPcard⟩ := hP
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hsig : sigmaCore M = hallCoreOf M := (h₂ G hG' M hM hMI).1
  have hKcard : Nat.card ↥(hallCoreOf M) = Nat.card ↥(hallCore ↥M) :=
    Subgroup.card_subtype M (hallCore ↥M)
  have hpK' : ¬ p ∣ Nat.card ↥(hallCore ↥M) := by rwa [hKcard] at hpK
  have hPP' : Nat.card ↥(P.subgroupOf M) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
  have hcop : Nat.Coprime (Nat.card ↥(hallCore ↥M)) (Nat.card ↥(P.subgroupOf M)) := by
    rw [hPP', hPcard]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK').symm
  obtain ⟨L₀, hP'L, hcompl⟩ :=
    exists_isComplement'_le_of_coprime (H := hallCore ↥M) (K := P.subgroupOf M)
      isGreatest_hallCore.1.2.2 hcop
  set U : Subgroup G := L₀.map M.subtype with hU
  have hUcompl : IsComplementTo M (Prep09.hallCoreIn M) U := isComplementTo_map_subtype hcompl
  have hPU : P ≤ U := by
    rw [hU, ← Subgroup.map_subgroupOf_eq_of_le hPM]
    exact Subgroup.map_mono hP'L
  have hcardU : Nat.card ↥U = Nat.card ↥L₀ := Subgroup.card_subtype M L₀
  have hfact : (Nat.card ↥U).factorization p = (Nat.card ↥M).factorization p := by
    have h := hcompl.card_mul_card
    rw [hcardU, ← h, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hpK']
  have hP''card : Nat.card ↥(P.subgroupOf U) = p ^ (Nat.card ↥U).factorization p := by
    rw [hfact, ← hPcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPU).toEquiv
  obtain ⟨hPab'', hPrank''⟩ :=
    (h₁ G hG' M hM hMI U hUcompl).1 p hp (Sylow.ofCard (P.subgroupOf U) hP''card)
  rw [Sylow.coe_ofCard] at hPab'' hPrank''
  have hPab : IsMulCommutative ↥P :=
    isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPU).symm
  have hrankP : elementaryAbelianPRank p ↥P = 2 := by
    refine Nat.le_antisymm ?_ ?_
    · calc elementaryAbelianPRank p ↥P
          = elementaryAbelianPRank p ↥(P.subgroupOf U) :=
            elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt
              (Subgroup.subgroupOfEquivOfLe hPU).symm
        _ ≤ maxElementaryAbelianPRank ↥(P.subgroupOf U) :=
            elementaryAbelianPRank_le_maxElementaryAbelianPRank hp
        _ ≤ 2 := hPrank''
    · calc (2 : ℕ) ≤ elementaryAbelianPRank p ↥M := hrank
        _ = elementaryAbelianPRank p ↥(P.subgroupOf M) :=
            (elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hp
              (by rw [hPP', hPcard])).symm
        _ = elementaryAbelianPRank p ↥P :=
            elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt (Subgroup.subgroupOfEquivOfLe hPM)
  refine ⟨hPab, hrankP, ?_⟩
  have hPp : IsPGroup p ↥P := IsPGroup.of_card hPcard
  have hSbot : sigmaCore M ≠ ⊥ := by rw [hsig]; exact hallCoreOf_ne_bot hMI
  have hpS : ¬ p ∣ Nat.card ↥(sigmaCore M) := by rw [hsig]; exact hpK
  have huniq : ∀ a ∈ P, orderOf a = p → centralizerIn (sigmaCore M) (zpowers a) ≠ ⊥ →
      IsUniqueMaximalOvergroup (centralizer ({a} : Set G)) M := by
    intro a haP hord hca
    have ha1 : a ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord
      exact hp.one_lt.ne hord
    have hzbot : (zpowers a : Subgroup G) ≠ ⊥ := fun h => ha1 (Subgroup.zpowers_eq_bot.mp h)
    have hzU : (zpowers a : Subgroup G) ≤ U := by
      rw [Subgroup.zpowers_le]
      exact hPU haP
    have hcne : centIn (Prep09.hallCoreIn M) ((zpowers a : Subgroup G) : Set G) ≠ ⊥ := by
      rw [← hallCoreOf_eq_hallCoreIn, ← hsig, ← centralizerIn_eq_centIn]
      exact hca
    obtain ⟨hle, huq⟩ := (h₁ G hG' M hM hMI U hUcompl).2 _ hzU hzbot hcne
    rw [centralizer_coe_zpowers] at hle huq
    exact ⟨hM, hle, fun N hN hNle => huq N hN hNle⟩
  obtain ⟨A, hAP, hAplane⟩ := exists_isPPlane_le hp hrankP
  rw [← hsig]
  exact FPF_complement_plane_centralizer_witness G hG M hM hSbot p hp hpS P hPM hPp
    ⟨A, hAP, hAplane⟩ huniq

end

end CFSG.FeitThompson.Proofs
