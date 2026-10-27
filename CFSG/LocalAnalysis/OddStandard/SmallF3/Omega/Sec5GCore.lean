module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GClause
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GSetup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412 CFSG.ABGLocalTools

theorem sec5g_trichotomy
    (hGold : GoldStmt) (hN11a : S_N11a) (hN11b : S_N11b)
    {X : Type} [Group X] [Finite X] (S : Sylow 2 X) (A : Subgroup X)
    (hAS : A ≤ (S : Subgroup X))
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAsq : ∀ a ∈ A, a * a = 1)
    (hA4 : Nat.card A = 4)
    (hclosed : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A)
    (htrans : ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 → ∃ g : X, g⁻¹ * a * g = b) :
    ((S : Subgroup X) ⊓ normalClosure (A : Set X) = A ∧ (Sec5GCaseI A ∨ Sec5GCaseII A)) ∨
      Sec5GCaseIII (S : Subgroup X) A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAab : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAcomm a a.2 b b.2)⟩⟩
  obtain ⟨hlay0, hbar0, hcomp0⟩ := hGold X S A hAS hAab hclosed
  set M : Subgroup X := Subgroup.normalClosure (A : Set X) with hMdef
  have hAM : A ≤ M := Subgroup.subset_normalClosure
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hSyl : IsSylowOf 2 (S : Subgroup X) ⊤ :=
    (isSylowOf_iff).2 ⟨le_top, S.isPGroup', by
      rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  have hSylM : IsSylowOf 2 ((S : Subgroup X) ⊓ M) M :=
    hSyl.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.2 hMn).ge
  obtain ⟨Qs, hQs⟩ := hSylM.exists_sylow_eq_subgroupOf
  rw [Subgroup.inf_subgroupOf_right] at hQs
  have hQsP : IsPGroup 2 ↥((S : Subgroup X).subgroupOf M) := by
    rw [← hQs]; exact Qs.isPGroup'
  let Ts : Sylow 2 (Sec5GBar A) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (goldschmidtOddCore ↥M)) Qs
  have hTs : (Ts : Subgroup (Sec5GBar A)) =
      ((S : Subgroup X).subgroupOf M).map (sec5g_pi A) := by
    rw [Sylow.coe_mapSurjective, hQs]
  have hcardSM : Nat.card ↥((S : Subgroup X) ⊓ M) = Nat.card (Ts : Subgroup (Sec5GBar A)) := by
    rw [hTs, card_map_eq_of_injOn (sec5g_pi A) _
      (fun x hx y hy hxy => sec5g_inj_of_pgroup A hQsP hx hy hxy)]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm.trans
      (by rw [Subgroup.inf_subgroupOf_right])
  have hAle : A ≤ (S : Subgroup X) ⊓ M := le_inf hAS hAM
  have hAbcard : Nat.card ↥(Sec5GImg A) = 4 := sec5g_card_img A hAsq hA4
  have hbar : Sec5GImg A = CFSG.Open.pCore 2 (Sec5GBar A) ⊔ Subgroup.closure
      {t | t ∈ ((S : Subgroup X).subgroupOf M).map (sec5g_pi A) ⊓
        goldschmidtLayer (Sec5GBar A) ∧ t ^ 2 = 1} := hbar0
  have hUAb : CFSG.Open.pCore 2 (Sec5GBar A) ≤ Sec5GImg A := by
    rw [hbar]
    exact le_sup_left
  rcases sec5g_dich A htrans hUAb with hU0 | hAbU
  ·
    have hlay' : goldschmidtLayer (Sec5GBar A) = ⊤ := by
      have h : CFSG.Open.pCore 2 (Sec5GBar A) ⊔ goldschmidtLayer (Sec5GBar A) = ⊤ := hlay0
      rwa [hU0, bot_sup_eq] at h
    have hbar' : Sec5GImg A = Omega1 (Ts : Subgroup (Sec5GBar A)) := by
      rw [hbar, hU0, bot_sup_eq, hlay', inf_top_eq, hTs]
      rfl
    have hVcomm : IsMulCommutative (Omega1 (Ts : Subgroup (Sec5GBar A))) := by
      rw [← hbar']
      have : IsMulCommutative (A.subgroupOf M) :=
        ⟨⟨fun a b => Subtype.ext (Subtype.ext (hAcomm _ a.2 _ b.2))⟩⟩
      exact isMulCommutative_map this (sec5g_pi A)
    have hV : Nat.card (Omega1 (Ts : Subgroup (Sec5GBar A))) = 4 := by
      rw [← hbar']; exact hAbcard
    have hO' : goldschmidtOddCore (Sec5GBar A) = ⊥ := goldschmidtOddCore_quotient_eq_bot (↥M)
    rcases sylow_card_of_layer hN11a hN11b hU0 hO' hlay' hcomp0 Ts hV hVcomm with h4 | h64
    ·
      have hSMA : (S : Subgroup X) ⊓ M = A := by
        have : Nat.card ↥((S : Subgroup X) ⊓ M) ≤ Nat.card A := by rw [hcardSM, h4, hA4]
        exact (Subgroup.eq_of_le_of_card_ge hAle this).symm
      left
      refine ⟨hSMA, Or.inr ⟨?_, ⟨Ts, ?_⟩⟩⟩
      · obtain ⟨K, hK, hKtop⟩ :=
          GoldY.exists_component_eq_top hN11b hU0 hO' hlay' hcomp0 Ts hV hVcomm
        subst hKtop
        have hZ : Subgroup.center ↥(⊤ : Subgroup (Sec5GBar A)) = ⊥ :=
          GoldY.component_center_eq_bot (GoldY.center_eq_bot hU0 hO' hlay') hlay' hK
        obtain ⟨TQ, hcardT, -, -⟩ :=
          GoldY.exists_sylow_quotient (⊤ : Subgroup (Sec5GBar A)) hZ Ts
        rw [inf_top_eq] at hcardT
        obtain ⟨p, f, hp, hpo, hf, h5, h8, ⟨e⟩⟩ :=
          sec5g_psl2_of_sylow_card_four (hcomp0 ⊤ hK) TQ (by rw [hcardT, h4])
        let e0 : (↥(⊤ : Subgroup (Sec5GBar A)) ⧸ Subgroup.center ↥(⊤ : Subgroup (Sec5GBar A))) ≃*
            Sec5GBar A :=
          ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
            Subgroup.topEquiv
        exact ⟨p, f, hp, hpo, hf, h5, h8, ⟨e0.symm.trans e⟩⟩
      · have : ((S : Subgroup X).subgroupOf M) = A.subgroupOf M := by
          rw [← Subgroup.inf_subgroupOf_right, hSMA]
        rw [hTs, this]
        rfl
    ·
      right
      refine ⟨by rw [hcardSM, h64], ?_⟩
      intro s hs hs2
      obtain ⟨hsS, hsM⟩ := hs
      have hsx : (⟨s, hsM⟩ : ↥M) ∈ (S : Subgroup X).subgroupOf M := hsS
      have hπs : sec5g_pi A ⟨s, hsM⟩ ∈ Omega1 (Ts : Subgroup (Sec5GBar A)) := by
        refine Subgroup.subset_closure ⟨?_, ?_⟩
        · rw [hTs]; exact ⟨_, hsx, rfl⟩
        · rw [sq, ← map_mul]
          have : (⟨s, hsM⟩ : ↥M) * ⟨s, hsM⟩ = 1 := Subtype.ext hs2
          rw [this, map_one]
      rw [← hbar'] at hπs
      obtain ⟨a, ha, haπ⟩ := (sec5g_mem_img A).1 hπs
      have haS : (⟨a, subset_normalClosure ha⟩ : ↥M) ∈ (S : Subgroup X).subgroupOf M := hAS ha
      have h2 : a = s := congrArg Subtype.val (sec5g_inj_of_pgroup A hQsP haS hsx haπ)
      rw [← h2]
      exact ha
  ·
    have hI : Sec5GImg A = ⊤ := sec5g_img_top A hAbU hUAb
    left
    refine ⟨?_, Or.inl hI⟩
    have hcard : Nat.card ↥((S : Subgroup X) ⊓ M) ≤ Nat.card A := by
      rw [hcardSM]
      calc Nat.card (Ts : Subgroup (Sec5GBar A)) ≤ Nat.card (Sec5GBar A) :=
            Subgroup.card_le_card_group _
        _ = Nat.card ↥(Sec5GImg A) := by rw [hI, Subgroup.card_top]
        _ = Nat.card A := hAbcard.trans hA4.symm
    exact (Subgroup.eq_of_le_of_card_ge hAle hcard).symm

end CFSG.OddStandard.SmallF3.Omega
