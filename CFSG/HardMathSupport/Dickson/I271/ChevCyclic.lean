module

public import CFSG.HardMathSupport.Dickson.I271.Support.CyclicAut
public import CFSG.HardMathSupport.Dickson.I271.Support.CyclicNine

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

theorem chevCyclicCase_of_kdata (hK65 : ∀ p : ℕ, p.Prime → p ≠ 2 → KD65 p) (hRank : KDRankOne)
    (hCen : KDCenterCase) : ChevCyclicCase := by
  have hHH := kdHallHigmanL2_holds
  intro X _ _ p K B hH hLie hcyc
  have hp := hH.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hin := hH.inducesInnerIn_of_cyclic (hK65 p hp hH.odd) hcyc
  obtain ⟨k, b₀, hb₀B, hb₀act, hkZ, hkp, hstar⟩ := hH.exists_gen hcyc hin
  have hq := hH.quasi
  have hZp : IsPGroup p (Subgroup.center ↥K) := i271h_center_isPGroup hp hH.primeCore
  by_cases hZ : Subgroup.center ↥K = ⊥
  swap
  · exfalso
    obtain ⟨x, hxp, hxk, hxn⟩ := hCen p hp hH.odd ↥K hq hLie hZp hZ k hkZ hkp
    exact hxn (hstar x hxp hxk)
  left
  have hkp1 : k ^ p = 1 := by simpa [hZ] using hkp
  have hk1 : k ≠ 1 := fun h => hkZ (h ▸ Subgroup.one_mem _)
  have hko : orderOf k = p := orderOf_eq_prime hkp1 hk1
  have hstar' : ∀ x : ↥K, x ^ p = 1 → x * k = k * x → x ∈ Subgroup.zpowers k := by
    intro x hx hxk
    have := hstar x hx hxk
    rwa [hZ, sup_bot_eq] at this
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 1 := by
    apply CFSG.SectionRank.pRank_le hp.one_lt
    intro E _ hE
    simpa using card_le_of_elemAbelian_of_unique hko hstar' hE
  let eS : (↥K ⧸ Subgroup.center ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  haveI hsimpQ : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  haveI hsimp : IsSimpleGroup ↥K := eS.symm.isSimpleGroup
  have hnc : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨u, v, huv⟩ := exists_noncomm_of_isQuasisimple hq
    exact ⟨eS u, eS v, fun h => huv (eS.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hLie' : LieCharOf p ↥K := by
    obtain ⟨idx, ⟨e⟩, hchar⟩ := hLie
    exact ⟨idx, ⟨eS.symm.trans e⟩, hchar⟩
  obtain ⟨hp5, F, _, _, hFcard, ⟨eF⟩⟩ := hRank p hp hH.odd ↥K hsimp hnc hLie' hrank
  have hHH' := hHH p hp hp5 ↥K F hFcard ⟨eF⟩ k hko
  intro S hSN hcop hBS
  have hb₀N : b₀ ∈ Subgroup.normalizer (K : Set X) := hH.norm hb₀B
  exact le_centralizer_of_trivial_aut hSN hb₀N k.2 hb₀act (hBS ⟨hb₀B, hb₀N⟩) hcop hHH'

theorem chevCyclicCase_of_nineFold
    (hGA : CFSG.Open.GriessAllModelsStatement) (hK65 : ∀ p : ℕ, p.Prime → p ≠ 2 → KD65 p)
    (hNine : KDU43NineFold) : ChevCyclicCase :=
  chevCyclicCase_of_kdata hK65 kdRankOne_holds
    (kdCenterCase_of_nineFold hGA hNine)

theorem chevCyclicCase_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) (hK65 : ∀ p : ℕ, p.Prime → p ≠ 2 → KD65 p) :
    ChevCyclicCase :=
  chevCyclicCase_of_kdata hK65 kdRankOne_holds (kdCenterCase_holds hGA)

end CFSG.HardMathSupport.Dickson.I271
