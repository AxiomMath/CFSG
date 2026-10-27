module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideComp
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideOdd
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G]

structure D1SmallMDataP (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R Np Z : Subgroup G)
    (r : ℕ) (t : G) : Prop where
  ph3 : D1PhaseThree p P M H R
  ind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q
  le_R : Z ≤ R
  elem : IsElemAbelian p Z
  card_le : p ^ 2 ≤ Nat.card Z
  r_four : 4 ≤ r
  t_mem : t ∈ H ⊓ M
  t_norm : t ∈ Subgroup.normalizer (Z : Set G)
  irr : ∀ k : ℕ, ¬ r ∣ k → ∀ Y : Subgroup G, Y ≤ Z →
    t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = Z
  plus_le : Np ≤ H ⊓ M
  core_le : GLBPrimeCore p H ≤ Np
  plus_cyclic : ∀ A : Subgroup G, A ≤ Np → IsPGroup p A → IsCyclic A
  perfect_le : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ Np
  comm_le : ∀ z ∈ Z, ∀ c ∈ Np, z * c * z⁻¹ * c⁻¹ ∈ GLBPrimeCore p H

variable {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R Np Z : Subgroup G} {r : ℕ} {t : G}

theorem D1SmallMDataP.isElemAbelian_barM (h : D1SmallMDataP p P M H R Np Z r t) :
    IsElemAbelian p (barM M Z) :=
  isElemAbelian_barM_of_isElemAbelian h.elem

theorem D1SmallMDataP.card_barM (h : D1SmallMDataP p P M H R Np Z r t) :
    Nat.card (barM M Z) = Nat.card Z :=
  card_barM_of_isPGroup Fact.out h.ph3.ne_two (h.le_R.trans h.ph3.le_M)
    fun x => ⟨1, Subtype.ext (by simpa using h.elem.2 x x.2)⟩

theorem D1SmallMDataP.cyc (h : D1SmallMDataP p P M H R Np Z r t) :
    ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) → ⁅Y, Y⁆ = Y →
      ∀ A : Subgroup G, A ≤ Y → IsPGroup p A → IsCyclic A := fun Y hY hperf A hAY hA =>
  h.plus_cyclic A (hAY.trans (h.perfect_le Y (h.ph3.inf_eq_inf_normalizer_twoCore ▸ hY) hperf))
    hA

theorem D1SmallMDataP.oddCore (h : D1SmallMDataP p P M H R Np Z r t) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsp : s ≠ p) :
    barM M Z ≤ Subgroup.centralizer
        ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
          Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
      4 ≤ Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype) :=
  barM_le_centralizer_pCore_or_four_le_pRank (h.le_R.trans h.ph3.le_M) h.isElemAbelian_barM
    (h.card_barM ▸ h.card_le) ⟨r, t, h.r_four, h.t_mem.2, h.t_norm, h.irr⟩ hs
    hs2 hsp

theorem D1SmallMDataP.compNotLe (h : D1SmallMDataP p P M H R Np Z r t) {L : Subgroup G}
    (hL2 : IsTwoPrimeComponent M L) (hLK : L ≤ H ⊓ M) (hLN : ¬ L ≤ GLBPrimeCore p H) :
    barM M Z ≤ Subgroup.centralizer (barM M L : Set _) :=
  h.ph3.barM_le_centralizer_of_not_le_glbPrimeCore h.le_R h.perfect_le h.comm_le hL2 hLK hLN

theorem D1SmallMDataP.compFive (hα : KFactThreeOrFiveDvd) (hβ : KFactOutElemRank)
    (h : D1SmallMDataP p P M H R Np Z r t) (hp5 : 5 ≤ p) {L : Subgroup G}
    (hL2 : IsTwoPrimeComponent M L) (hLN : L ≤ GLBPrimeCore p H) :
    barM M Z ≤ Subgroup.centralizer (barM M L : Set _) :=
  h.ph3.barM_le_centralizer_of_le_glbPrimeCore hα hβ h.ind h.le_R h.elem h.isElemAbelian_barM
    h.card_barM h.card_le (h.core_le.trans h.plus_le) ⟨r, t, h.r_four, h.t_mem, h.t_norm, h.irr⟩ hp5
    hL2 hLN

theorem D1SmallMDataP.core (hα : KFactThreeOrFiveDvd) (hβ : KFactOutElemRank)
    (h : D1SmallMDataP p P M H R Np Z r t) (hp5 : 5 ≤ p)
    (hblocks : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M Z ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    (∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      barM M Z ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∧
    ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p →
      barM M Z ≤ Subgroup.centralizer
        ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
          Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
      4 ≤ Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype) := by
  refine ⟨fun Lb hLb => ?_, fun s hs hs2 hsp => h.oddCore hs hs2 hsp⟩
  obtain ⟨L, hL2, rfl, hw | hle⟩ := h.ph3.exists_weakSBlock_or_le_inf hLb
  · exact hblocks L hw
  · by_cases hLN : L ≤ GLBPrimeCore p H
    · exact h.compFive hα hβ hp5 hL2 hLN
    · exact h.compNotLe hL2 hle hLN

end Data

end CFSG.AGLEmbedding
