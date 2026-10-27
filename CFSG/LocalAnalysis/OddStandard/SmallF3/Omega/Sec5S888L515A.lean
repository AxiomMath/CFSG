module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Lay
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Glue
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements2
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem s888_odd_card_oddCore {H : Type*} [Group H] [Finite H] :
    Odd (Nat.card (CFSG.oddCore H)) := by
  have h := CFSG.LocalCores.piCore_isPiSubgroup (G := H) {q : Nat.Primes | q.val ≠ 2}
  rw [← CFSG.oddCore_eq_piCore] at h
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  exact h ⟨2, Nat.prime_two⟩ h2 rfl

private theorem s888_oddCore_ne_top_of_twoU43 {G : Type} [Group G] [Finite G] {I : Subgroup G}
    (h : IsTwoU43 (↥I ⧸ CFSG.oddCore ↥I)) : CFSG.oddCore ↥I ≠ ⊤ := by
  intro htop
  haveI : Subsingleton (↥I ⧸ CFSG.oddCore ↥I) := (QuotientGroup.subsingleton_iff).mpr htop
  haveI : Finite (↥I ⧸ CFSG.oddCore ↥I) := inferInstance
  have h1 : Nat.card (Subgroup.center (↥I ⧸ CFSG.oddCore ↥I)) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr inferInstance
  have h2 : Nat.card (Subgroup.center (↥I ⧸ CFSG.oddCore ↥I)) = 2 := h.1
  omega

private theorem s888_oddCoreIn_le_centerIn {G : Type} [Group G] [Finite G] {I : Subgroup G}
    (h : IsOm6Z2 I) : oddCoreIn I ≤ centerIn I := by
  have hne : CFSG.oddCore ↥I ≠ ⊤ := s888_oddCore_ne_top_of_twoU43 h.2
  have hle : CFSG.oddCore ↥I ≤ Subgroup.center ↥I :=
    oddCore_le_center_of_isQuasisimple h.1 hne
  unfold oddCoreIn centerIn CFSG.inSubgroup
  exact Subgroup.map_mono hle

private theorem s888_oddCoreIn_eq_bot {G : Type} [Group G] [Finite G] {d : G} {I : Subgroup G}
    (h : IsOm6Z2 I) (hd : orderOf d = 2) (hcenter : centerIn I = zpowers d) :
    oddCoreIn I = ⊥ := by
  rw [← le_bot_iff]
  intro x hx
  have hxZ : x ∈ centerIn I := s888_oddCoreIn_le_centerIn h hx
  have hxd : x ∈ zpowers d := by rwa [hcenter] at hxZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxd
  have hd2 : d ^ 2 = 1 := by simpa [hd] using pow_orderOf_eq_one d
  have hx2 : x * x = 1 := by
    rw [← hk, ← zpow_add]
    have h2 : k + k = 2 * k := by ring
    rw [h2, zpow_mul]
    have hd2z : d ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = 1 + 1 by norm_num, zpow_add, zpow_one]
      simpa [pow_two] using hd2
    rw [hd2z, one_zpow]
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hx2)
  have hodd_x : Odd (orderOf x) := by
    have hx' := hx
    rw [oddCoreIn, CFSG.inSubgroup, Subgroup.mem_map] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hdvd_y : orderOf y ∣ Nat.card (CFSG.oddCore ↥I) := Subgroup.orderOf_dvd_natCard _ hy
    have hodd_y : Odd (orderOf y) := (s888_odd_card_oddCore (H := ↥I)).of_dvd_nat hdvd_y
    have hxy : orderOf x = orderOf y := by rw [← hyx]; exact Subgroup.orderOf_coe y
    rwa [hxy]
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd_x; exact absurd hodd_x (by decide)

private theorem s888_isTwoU43_of_equiv {Q Q' : Type} [Group Q] [Group Q']
    (e : Q ≃* Q') (h : IsTwoU43 Q) : IsTwoU43 Q' := by
  refine ⟨?_, ?_⟩
  · have hmap : (Subgroup.center Q).map e.toMonoidHom = Subgroup.center Q' :=
      Subgroup.map_center_eq e
    rw [← hmap, Subgroup.card_map_of_injective e.injective]
    exact h.1
  · exact LieModel.quotient_center_of_mulEquiv e h.2

theorem sec5_setting_data (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b) (h56 : Asc82Lemma56)
    (hZ : Asc82ZExists) (hB : Asc82Sec5FactB5) (h512b : Asc82Lemma512b) {G : Type} [Group G]
    [Finite G] {d : G} {I : Subgroup G} (hs : Sec5Setting G d I) :
    layerC5 d = I ∧ centerIn I = zpowers d ∧ oddCoreIn I = ⊥ ∧ IsTwoU43 ↥I ∧
      ∃ (S' : Subgroup G) (z' r' : G) (B' A' : Subgroup G), Sec5RCtx G d I S' z' r' B' A' := by
  have hlayer : layerC5 d = I := layerC5_eq_of_setting h52a hs
  obtain ⟨S', z', r', B', A', hR⟩ := sec5_exists_rctx h52b h56 hZ hB hs
  have hcenter : centerIn I = zpowers d := h512b G d I S' z' r' B' A' hR
  have hcore : oddCoreIn I = ⊥ := s888_oddCoreIn_eq_bot hs.isOm6Z2 hs.involution hcenter
  have hbot : CFSG.oddCore ↥I = ⊥ := by
    rw [oddCoreIn, CFSG.inSubgroup] at hcore
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.oddCore ↥I)
      (Subgroup.subtype_injective I)).mp hcore
  have htwo : IsTwoU43 ↥I := by
    let e : (↥I ⧸ CFSG.oddCore ↥I) ≃* ↥I :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    exact s888_isTwoU43_of_equiv e hs.twoU43
  exact ⟨hlayer, hcenter, hcore, htwo, S', z', r', B', A', hR⟩

end CFSG.OddStandard.SmallF3.Omega
