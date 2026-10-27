module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockClose
import CFSG.LocalAnalysis.ComponentClassification.GrSLitGW36
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem sq_dvd_card_sup_of_commute {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]
    {V₁ V₂ : Subgroup X} (h₁ : ⁅V₁, V₁⁆ = V₁) (hc : V₁ ≤ Subgroup.centralizer (V₂ : Set X))
    (hd₁ : p ∣ Nat.card V₁) (hd₂ : p ∣ Nat.card V₂) : p ^ 2 ∣ Nat.card (V₁ ⊔ V₂ : Subgroup X) := by
  by_contra hn
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' (G := V₂) p hd₂
  have hb₀p : orderOf (b₀ : X) = p := by rw [Subgroup.orderOf_coe]; exact hb₀
  have hc' : V₂ ≤ Subgroup.centralizer (V₁ : Set X) := Subgroup.le_centralizer_iff.mp hc
  have hkey : ∀ a ∈ V₁, orderOf a = p → a ∈ Subgroup.zpowers (b₀ : X) := by
    intro a ha hap
    by_contra hab
    have hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers (b₀ : X) = ⊥ := by
      have hdvd : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers (b₀ : X) : Subgroup X) ∣ p := by
        rw [← hap, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | h1
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have h2 : Subgroup.zpowers a ⊓ Subgroup.zpowers (b₀ : X) = Subgroup.zpowers a :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, Nat.card_zpowers, hap])
        exact hab ((h2 ▸ inf_le_right : Subgroup.zpowers a ≤ _) (Subgroup.mem_zpowers a))
    have hAp : IsPGroup p (Subgroup.zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hap, pow_one])
    have hBp : IsPGroup p (Subgroup.zpowers (b₀ : X)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb₀p, pow_one])
    have hAB : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers (b₀ : X) : Set X) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact Subgroup.mem_centralizer_iff.mp (hc ha) _ (V₂.zpow_mem b₀.2 k)
    have hEp := hAp.to_sup_of_normal_right' hBp hAB
    have hle := mul_card_le_of_inf_eq_bot (le_sup_left : Subgroup.zpowers a ≤ _) le_sup_right hdisj
    rw [Nat.card_zpowers, Nat.card_zpowers, hap, hb₀p] at hle
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    rw [hk] at hle
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos (by omega)
      nlinarith [hp.out.two_le]
    apply hn
    have hEle : Subgroup.zpowers a ⊔ Subgroup.zpowers (b₀ : X) ≤ V₁ ⊔ V₂ :=
      sup_le (le_sup_left.trans' (Subgroup.zpowers_le.mpr ha))
        (le_sup_right.trans' (Subgroup.zpowers_le.mpr b₀.2))
    exact ((pow_dvd_pow p hk2).trans (hk ▸ dvd_rfl)).trans (Subgroup.card_dvd_of_le hEle)
  have hn₁ : ¬ p ^ 2 ∣ Nat.card V₁ := fun h => hn (h.trans (Subgroup.card_dvd_of_le le_sup_left))
  obtain ⟨Q⟩ : Nonempty (Sylow p V₁) := inferInstance
  have hQc : (Q : Subgroup V₁) ≤ Subgroup.center V₁ := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact Subgroup.one_mem _
    have hxp : orderOf (x : X) = p := by
      rw [Subgroup.orderOf_coe]
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') ⟨x, hx⟩
      rw [Subgroup.orderOf_mk] at hk
      have hdvd : p ^ k ∣ Nat.card V₁ := hk ▸ orderOf_dvd_natCard x
      have hk1 : k ≤ 1 := by
        by_contra h
        exact hn₁ ((pow_dvd_pow p (by omega : 2 ≤ k)).trans hdvd)
      interval_cases k
      · exact absurd (orderOf_eq_one_iff.mp (by simpa using hk)) hx1
      · simpa using hk
    have hxb := hkey x x.2 hxp
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp
      (hc' ((Subgroup.zpowers_le.mpr b₀.2) hxb)) (y : X) y.2
    simpa using this
  have : Group.IsPerfect V₁ := Subgroup.isPerfect_iff.mpr h₁
  exact ComponentClassification.GrSLit.not_dvd_card_of_perfect_of_sylow_le_center Q hQc hd₁

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.exists_perfect_dvd_of_pRank (h : D1PhaseThree p P M H R)
    (hrk3 : Open.pRank 3 (H ⊓ M) ≤ 3) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hInn : KFactBlockAutPrimeInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hp5 : 5 ≤ p) {z : G} (hzK : z ∈ H ⊓ M)
    (hzp : orderOf z = p) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ∧ ⁅V, V⁆ = V ∧
        p ∣ Nat.card V := by
  have hp := h.prime
  have hzL := h.mem_normalizer_block_of_five_of_pRank hrk3 h85 h86 h93 hD2 hK2 hC3' hK5' hp5 hzK
      hzp hL
  have hdvd := h.dvd_card_of_centralizer_le h84 h85 h86 h93 hD2 hInn hp5 hzK hzp hCz hL hzL
  by_contra hno
  push Not at hno
  have hcop := h.coprime_card_barM_normalizer_inf h85 h93 hD2 hKP hC3 hK5 hL hp hp5
    fun V hVP hVp => (Nat.Prime.coprime_iff_not_dvd hp).mpr (hno V hVP hVp)
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop hdvd

theorem D1PhaseThree.exists_perfect_dvd (h : D1PhaseThree p P M H R)
    (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hInn : KFactBlockAutPrimeInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hp5 : 5 ≤ p) {z : G} (hzK : z ∈ H ⊓ M)
    (hzp : orderOf z = p) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ∧ ⁅V, V⁆ = V ∧
        p ∣ Nat.card V := by
  have hrk3 : Open.pRank 3 (H ⊓ M) ≤ 3 := by
    by_contra hc
    exact h.false_of_four_le_pRank' hind Nat.prime_three (by decide) (by omega) (by omega)
  exact h.exists_perfect_dvd_of_pRank hrk3 h84 h85 h86 h93 hD2 hInn hKP hC3 hK5 hK2 hC3' hK5' hp5
      hzK hzp
    hCz hL

theorem D1PhaseThree.barM_eq_of_perf (h : D1PhaseThree p P M H R)
    (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hInn : KFactBlockAutPrimeInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hp5 : 5 ≤ p) {z : G} (hzK : z ∈ H ⊓ M)
    (hzp : orderOf z = p) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hperf : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ¬ p ^ 2 ∣ Nat.card V) :
    ∀ L₁ L₂ : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L₁ →
      IsWeakSBlock M (pCoreOf 2 H) L₂ → barM M L₁ = barM M L₂ := by
  intro L₁ L₂ hL₁ hL₂
  by_contra hne
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨V₁, hV₁P, hV₁p, hV₁d⟩ := D1PhaseThree.exists_perfect_dvd h hind h84 h85 h86 h93 hD2
    hInn hKP hC3 hK5 hK2 hC3' hK5' hp5 hzK hzp hCz hL₁
  obtain ⟨V₂, hV₂P, hV₂p, hV₂d⟩ := D1PhaseThree.exists_perfect_dvd h hind h84 h85 h86 h93 hD2
    hInn hKP hC3 hK5 hK2 hC3' hK5' hp5 hzK hzp hCz hL₂
  have hPHM : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≤ barM M (H ⊓ M) := by
    intro L hL
    refine barM_mono ?_
    rw [h.normalizer_twoCore_H]
    exact inf_le_inf_left H hL.le
  have hcomm : V₁ ≤ Subgroup.centralizer (V₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have h1 := le_centralizer_of_component_ne hL₁.component hL₂.component hne
    exact (hV₁P.trans (barM_mono inf_le_right)).trans
      (Subgroup.centralizer_le (hV₂P.trans (barM_mono inf_le_right)) |>.trans' h1)
  have hsup := sq_dvd_card_sup_of_commute hV₁p hcomm hV₁d hV₂d
  have hVp : ⁅V₁ ⊔ V₂, V₁ ⊔ V₂⁆ = V₁ ⊔ V₂ := by
    refine le_antisymm (Subgroup.commutator_le_self _) (sup_le ?_ ?_)
    · calc V₁ = ⁅V₁, V₁⁆ := hV₁p.symm
        _ ≤ ⁅V₁ ⊔ V₂, V₁ ⊔ V₂⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc V₂ = ⁅V₂, V₂⁆ := hV₂p.symm
        _ ≤ ⁅V₁ ⊔ V₂, V₁ ⊔ V₂⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  exact hperf _ (sup_le (hV₁P.trans (hPHM L₁ hL₁)) (hV₂P.trans (hPHM L₂ hL₂))) hVp hsup

end CFSG.AGLEmbedding
