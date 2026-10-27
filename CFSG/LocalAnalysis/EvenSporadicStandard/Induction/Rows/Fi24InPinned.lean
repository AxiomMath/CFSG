module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F24LLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi22FinalK

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Sporadic CFSG.Blueprint.Fischer CFSG.Sporadic.Fi24
open CFSG.Fischer hiding OutTwo
open CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78.Fi24Row (edge_hW edge_surj ρE)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem fi24in_tRxb_mem_JR : tR * xb ∈ (JR : Subgroup R) :=
  (Subgroup.mem_inf.1 tR_mul_xb_mem_CE).2

theorem fi24in_tRxb_mem_LE : tR * xb ∈ Fi24.LE :=
  Subgroup.mem_inf.2 ⟨tR_mul_xb_mem_CE, mem_centralizer_R.2 (by rw [mul_assoc, ← tR_xb_comm])⟩

theorem fi24in_LE_le_JR : Fi24.LE ≤ (JR : Subgroup R) := inf_le_left.trans inf_le_right

theorem fi24in_edge_cent_LE
    (ψ : ↥(LocalClass D24 tR ∩ LocalClass D24 xb) ≃ Fi22.D)
    (hψc : ∀ x y : ↥(LocalClass D24 tR ∩ LocalClass D24 xb),
      (x : R) * y = y * x ↔ (ψ x : Fi22.J) * ψ y = ψ y * ψ x)
    (hψt : ∀ x y : ↥(LocalClass D24 tR ∩ LocalClass D24 xb),
      ∃ h : (x : R) * y * x ∈ LocalClass D24 tR ∩ LocalClass D24 xb,
        (ψ ⟨_, h⟩ : Fi22.J) = ψ x * ψ y * ψ x)
    (hfix22 : ∀ g : Fi22.J, g ^ 2 = 1 → g ≠ 1 →
      Nat.card {x : Fi22.D // g * (x : Fi22.J) * g⁻¹ = x} ∈ ({54, 182, 694} : Set ℕ))
    {e : J} (he : EdgeSwap e) {z : R} (hz : z ∈ CE) (hc : ∀ ℓ ∈ Fi24.LE, z * ℓ = ℓ * z) :
    z = 1 ∨ z = tR * xb := by
  have hrangeL := range_edgeHomL pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ
    hψc hψt Fi22.center_eq_bot Fi22.index_innerTau_range (inf_le_left : CE ≤ _) commutator_LE
    (by rw [Fi22.card_tauGroup]; exact card_LE) (fun ℓ hℓ h => eq_of_mem_LE_centralizes hℓ h)
  have hsurj := edge_surj ψ hψc hψt hfix22 he
  have hz1 : z ∈ Subgroup.centralizer ({tR * xb} : Set R) := (Subgroup.mem_inf.1 hz).1
  have hone : ρE ψ hψc hψt ⟨z, hz1⟩ = 1 := by
    apply eq_one_of_commute_innerTau Fi22.pair_D Fi22.center_eq_bot
    intro x
    have hmem : innerTau Fi22.pair_D (x : Fi22.J) ∈ (innerTau Fi22.pair_D).range := ⟨x, rfl⟩
    rw [← hrangeL] at hmem
    obtain ⟨ℓ, hℓ⟩ := hmem
    have hzℓ := hc (ℓ : R) ℓ.2
    have h1 : ρE ψ hψc hψt ⟨z, hz1⟩ *
        ρE ψ hψc hψt (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) =
        ρE ψ hψc hψt (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) *
          ρE ψ hψc hψt ⟨z, hz1⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg (ρE ψ hψc hψt) (Subtype.ext hzℓ)
    have h0 : ρE ψ hψc hψt (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) =
        innerTau Fi22.pair_D x := hℓ
    rw [h0] at h1
    exact h1
  exact edgeHomC_ker pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt
    Fi22.center_eq_bot (inf_le_left : CE ≤ _) hsurj (card_CE he (edge_hW ψ hψc))
    tR_mul_xb_mem_CE ⟨z, hz⟩ hone

theorem fi24in_cent_LE {z : R} (hzJ : z ∈ (JR : Subgroup R))
    (hz : ∀ ℓ ∈ Fi24.LE, z * ℓ = ℓ * z) : z = 1 ∨ z = tR * xb := by
  obtain ⟨ψ, hψc, hψt⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 CFSG.Fischer.polarFacts) ⟨tR, tR_mem_D24⟩
    ⟨xb, xb_mem_D24⟩ tR_ne_xb tR_xb_comm
  have hzCE : z ∈ CE :=
    Subgroup.mem_inf.2 ⟨mem_centralizer_R.2 (hz _ fi24in_tRxb_mem_LE), hzJ⟩
  exact fi24in_edge_cent_LE ψ hψc hψt CFSG.Sporadic.Fi22.card_fixed_involution_D edgeSwap_a
    hzCE hz

theorem fi24in_isSporadic_quot {G C : Type} [Group G] [Group C] {J K : Subgroup G} (hKJ : K ≤ J)
    (e : C ≃* ↥K) (iso : Nonempty ((C ⧸ center C) ≃* Blueprint.NativeSporadic.Fi22)) :
    IsSporadic (↥(K.subgroupOf J) ⧸ center ↥(K.subgroupOf J)) .Fi22 := by
  obtain ⟨iso⟩ := iso
  exact ⟨(quotientCenterCongr ((Subgroup.subgroupOfEquivOfLe hKJ).trans e.symm)).trans iso⟩

theorem fi24in_outTwo_quot :
    OutTwo (↥(Fi24.LE.subgroupOf JR) ⧸ center ↥(Fi24.LE.subgroupOf JR)) := by
  obtain ⟨-, h1, -⟩ := Fi23.localStructureAt_of_mem sb_mem_D23
  obtain ⟨-, -, -, hiso⟩ := h1 rfl
  have h := fi24in_isSporadic_quot (G := R) (J := JR) (K := Fi24.LE)
    (C := ↥(Subgroup.centralizer ({sb} : Set Fi23.J))) fi24in_LE_le_JR leEquiv hiso
  exact fi22_outTwo_of_isSporadic h

theorem fi24in_base_pinned :
    Fi24InBase ↥(JR : Subgroup R) (⟨tR * xb, fi24in_tRxb_mem_JR⟩ : ↥(JR : Subgroup R))
      (Fi24.LE.subgroupOf JR) := by
  obtain ⟨ψ, hψc, hψt⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 CFSG.Fischer.polarFacts) ⟨tR, tR_mem_D24⟩
    ⟨xb, xb_mem_D24⟩ tR_ne_xb tR_xb_comm
  have hW := edge_hW ψ hψc
  exact fi24in_base_of_data (G := R) (J := JR) (K := Fi24.LE) fi24in_tRxb_mem_JR
    fi24in_LE_le_JR fi24in_tRxb_mem_LE tR_mul_xb_sq (mul_ne_one_edge pair_R xb_mem_D24 tR_ne_xb)
    (fun k hk => (mem_centralizer_R.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).1))
    (card_eq_two_mul_of_index (inf_le_left : Fi24.LE ≤ CE) (index_LE edgeSwap_a hW))
    (Cover.commutator_eq_self_of_isPerfect (Group.isPerfect_def.2 commutator_LE))
    (fun z hz hc => fi24in_cent_LE hz hc) fi24in_outTwo_quot fi24_outTwo_P

end CFSG.EvenSporadicStandard.Induction
