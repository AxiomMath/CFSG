module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VBar
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VLayer
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

variable {G : Type} [Group G] [Finite G] {m : ℕ}

theorem i112v_barLayer (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) (hS : GLStanding G m 3) {X B L : Subgroup G} (hB : IsElemAbelian 3 B)
    (hBX : B ≤ X) (hr : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B) (hL : GLAPComponent 3 X L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) {y : G} (hyB : y ∈ B)
    (hyn : y ∉ Subgroup.normalizer (L : Set G)) :
    IsSimpleGroup ↥(GLAPLayer 3 (barX 3 X (bClosure B L) ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨y, hBX hyB⟩} :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))) ∧
      3 ∣ Nat.card ↥(GLAPLayer 3 (barX 3 X (bClosure B L) ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨y, hBX hyB⟩} :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))) ∧
      Nonempty (↥(GLAPLayer 3 (barX 3 X (bClosure B L) ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨y, hBX hyB⟩} :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))) ≃*
        (↥(barX 3 X L) ⧸ Subgroup.center ↥(barX 3 X L))) := by
  obtain ⟨hp, -, -, hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ := i112v_bar hS hB hBX hr hL hnL
  obtain ⟨-, hrel, -, -, hZ9, hcase⟩ :=
    i112v_core T TL TT TM hQK hp (by norm_num) hQcore hBel hrankQ hLbar hnLQ
  have hJ : barX 3 X (bClosure B L) = i112J (barX 3 X B) (barX 3 X L) :=
    i112f_barX_bClosure hBX hL.1
  have hyB' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨y, hBX hyB⟩ ∈ barX 3 X B :=
    ⟨⟨y, hBX hyB⟩, (Subgroup.mem_subgroupOf).2 hyB, rfl⟩
  have hyn' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨y, hBX hyB⟩ ∉
      Subgroup.normalizer ((barX 3 X L : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
    intro h
    apply hyn
    have h2 : (⟨y, hBX hyB⟩ : ↥X) ∈ (Subgroup.normalizer (L : Set G)).subgroupOf X := by
      rw [← i112f_comap_normalizer_barX hL]
      exact h
    exact (Subgroup.mem_subgroupOf).1 h2
  have hZL : Nat.card ↥(barX 3 X L ⊓ Subgroup.centralizer
        ((barX 3 X L : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) = 1 ∨
      Nat.card ↥(barX 3 X L ⊓ Subgroup.centralizer
        ((barX 3 X L : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) :
          Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) = 3 := by
    rw [card_center_eq]
    rcases hcase with ⟨h1, -⟩ | ⟨h3, -⟩
    · exact Or.inl h1
    · exact Or.inr h3
  have hZ : Nat.card ↥(i112J (barX 3 X B) (barX 3 X L) ⊓
      Subgroup.centralizer (i112J (barX 3 X B) (barX 3 X L) :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) < 3 ^ 3 :=
    lt_of_le_of_lt hZ9 (by norm_num)
  have h := i112v_layer hp hQcore hBel hLbar hrel hyB' hyn' hZL hZ
  rw [hJ, inf_comm]
  exact h

theorem i112v_layer_G (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) (hS : GLStanding G m 3) {X B L : Subgroup G} (hB : IsElemAbelian 3 B)
    (hBX : B ≤ X) (hr : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B) (hL : GLAPComponent 3 X L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) {y : G} (hyB : y ∈ B)
    (hyn : y ∉ Subgroup.normalizer (L : Set G)) :
    GLAPComponent 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))
        (GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ∧
      Nonempty ((↥(GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ⧸
          GLAPPrimeCore 3 ↥(GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G)))) ≃*
        (↥(barX 3 X L) ⧸ Subgroup.center ↥(barX 3 X L))) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hs, hdvd, ⟨e₁⟩⟩ := i112v_barLayer T TL TT TM hS hB hBX hr hL hnL hyB hyn
  have hJX : bClosure B L ≤ X := by
    refine iSup₂_le fun b hb => ?_
    rw [← mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hBX hb))]
    exact gLBConj_mono b hL.1
  have hyJ : y ∈ Subgroup.normalizer ((bClosure B L : Subgroup G) : Set G) :=
    i112_B_le_normalizer_J (B := B) (L := L) hyB
  have hy3 : IsPGroup 3 (Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    by_cases hy1 : y = 1
    · exact absurd (by rw [hy1]; exact Subgroup.one_mem _) hyn
    · exact orderOf_eq_prime (hB.2 y hyB) hy1
  have hbar := barX_inf_centralizer hp (hBX hyB) hJX hyJ hy3
  have hHX : bClosure B L ⊓ Subgroup.centralizer ({y} : Set G) ≤ X := inf_le_left.trans hJX
  rw [← hbar] at hs e₁ hdvd
  obtain ⟨hc, ⟨e₂⟩⟩ := i112v_layer_lift hp hHX hs
  have : IsSimpleGroup ↥(GLAPLayer 3 (barX 3 X (bClosure B L ⊓
      Subgroup.centralizer ({y} : Set G)))) := hs
  have hO := i112v_glaPPrimeCore_eq_bot hp hdvd
  exact ⟨hc, ⟨e₂.trans ((QuotientGroup.quotientMulEquivOfEq hO).trans
    (QuotientGroup.quotientBot.trans e₁))⟩⟩

end CFSG.HardMathSupport.Solomon.Coordinator
