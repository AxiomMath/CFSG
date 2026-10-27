module

public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockRank
public import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D1L2Data.false_of_four_le_pRank {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqp : q < p) (h4 : 4 ≤ Open.pRank q (H ⊓ M)) : False := by
  have hH4 : 4 ≤ Open.pRank q H := h4.trans (pRank_mono q hq inf_le_left)
  have hβ : q ∈ GLBBetaFour G := by
    refine ⟨hq, hq2, prime_dvd_card_of_positive_rank q hq H (by omega), ?_⟩
    exact hH4.trans (le_csSup (twoLocalRank_bddAbove q hq) ⟨H, h.ph3.maxTwoLocal_H.1, rfl⟩)
  exact false_of_guestPrime h.ph3.glob.pre hβ (h.ind q hβ hqp) h.ph3.maxTwoLocal_M
    h.ph3.maxTwoLocal_H h.ph3.not_le (by omega)

theorem D1PhaseThree.exists_weakSBlock_or_le_inf {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) {Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hL : IsComponentOf Lbar ⊤) :
    ∃ L : Subgroup G, IsTwoPrimeComponent M L ∧ barM M L = Lbar ∧
      (IsWeakSBlock M (pCoreOf 2 H) L ∨ L ≤ H ⊓ M) :=
  h.toD1Escape.toTwoLocalPair.exists_weakSBlock_or_le_inf hL

theorem D1L2Data.le_pRank_three_of_not_mem_normalizer {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) (_hRank : StmtComponentRank)
    (_hLift : StmtBarPRankLift)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {r : ℕ} [Fact r.Prime] {g : G} (hgK : g ∈ H ⊓ M) (hg : IsPGroup r (Subgroup.zpowers g))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hgL : g ∉ Subgroup.normalizer (L : Set G)) : r ≤ Open.pRank 3 (H ⊓ M) :=
  h.ph3.toD1Escape.toTwoLocalPair.le_pRank_three_of_not_mem_normalizer hB3 hgK hg hL hgL

theorem D1PhaseThree.twoCore_M_le_glbPrimeCore {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) : pCoreOf 2 M ≤ GLBPrimeCore p H :=
  (h.twoCore_M_le h.twoCore_inf).trans (pCoreOf_le_glbPrimeCore Nat.prime_two
    ((Nat.coprime_primes h.prime Nat.prime_two).mpr h.ne_two) H)

theorem D1L2Data.normal_sup_of_le_pCore {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hX : barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)) :
    ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal := by
  have hp : p.Prime := Fact.out
  set Q := pCoreOf 2 M with hQdef
  set N := GLBPrimeCore p H with hNdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Ob := CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) with hOb
  set Y : Subgroup G := (Ob.comap mk).map M.subtype with hY
  have hYM : Y ≤ M := Subgroup.map_subtype_le _
  have hYsub : Y.subgroupOf M = Ob.comap mk :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hkerQ : ∀ m : M, mk m = 1 → (m : G) ∈ Q := coe_mem_pCoreOf_two_of_mk_eq_one
  have hQker : ∀ m : M, (m : G) ∈ Q → mk m = 1 := by
    intro m hm
    obtain ⟨m', hm', hmm'⟩ := hm
    have : m' = m := Subtype.ext hmm'
    subst this
    exact (QuotientGroup.eq_one_iff _).mpr hm'
  have hQN : Q ≤ N := h.ph3.twoCore_M_le_glbPrimeCore
  have hObOdd : Ob ≤ CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) := by
    refine le_sSup ⟨inferInstance, ?_⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := p)
      (G := ↥M ⧸ CFSG.pCore 2 ↥M))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr
      (fun h2 => h.ph3.ne_two h2.symm))
  have hcent := hObOdd.trans (h.ph3.oddCore_le_centralizer h84 hD2)
  have hYS : Y ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    refine le_normalizer_of_forall_map_conj_le fun g hg => ?_
    obtain ⟨m, hm, rfl⟩ := hg
    rintro _ ⟨s, hs, rfl⟩
    have hsM : s ∈ M := h.ph3.twoCore_le hs
    have hsbar : mk ⟨s, hsM⟩ ∈ barM M (pCoreOf 2 H) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
    have hcomm := Subgroup.mem_centralizer_iff.mp (hcent hm) _ hsbar
    have hc : mk (⟨s, hsM⟩ * m * (⟨s, hsM⟩)⁻¹ * m⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have hq : ((⟨s, hsM⟩ * m * (⟨s, hsM⟩)⁻¹ * m⁻¹ : M) : G) ∈ Q := hkerQ _ hc
    have hQS : Q ≤ pCoreOf 2 H := h.ph3.twoCore_M_le h.ph3.twoCore_inf
    have heq : (MulAut.conj (m : G)).toMonoidHom s =
        (((⟨s, hsM⟩ * m * (⟨s, hsM⟩)⁻¹ * m⁻¹ : M) : G))⁻¹ * s := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group
    change (MulAut.conj (m : G)).toMonoidHom s ∈ pCoreOf 2 H
    rw [heq]
    exact (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem (hQS hq)) hs
  have hYK : Y ≤ H ⊓ M := fun y hy =>
    h.ph3.inf_eq_inf_normalizer_twoCore ▸ ⟨hYM hy, hYS hy⟩
  have hYn : H ⊓ M ≤ Subgroup.normalizer (Y : Set G) :=
    inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mp
      (hYsub ▸ Subgroup.Normal.comap inferInstance mk))
  have hpow : ∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k ∈ Q := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := ↥M ⧸ CFSG.pCore 2 ↥M) ⟨mk m, hm⟩
    refine ⟨k, ?_⟩
    have h1 : mk (m ^ p ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    simpa using hkerQ _ h1
  have hYle := h.pcore_le Y hYK hYn fun y hy => (hpow y hy).imp fun k hk => hQN hk
  have hXM : X ≤ M := h.le_R.trans h.ph3.le_M
  have hXY : X ≤ Y := fun x hx =>
    ⟨⟨x, hXM hx⟩, hX (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)), rfl⟩
  have hQM : Q ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hQY : Q ≤ Y := fun q hq => ⟨⟨q, hQM hq⟩, by
    show mk ⟨q, hQM hq⟩ ∈ Ob
    rw [hQker _ hq]
    exact Ob.one_mem, rfl⟩
  have hYXQ : Y ≤ X ⊔ Q := by
    intro y hy
    have hXN : X ≤ Subgroup.normalizer (N : Set G) :=
      (h.le_R.trans h.ph3.le_H).trans (le_normalizer_glbPrimeCore p H)
    have hy' : y ∈ ((X ⊔ N : Subgroup G) : Set G) := hYle hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X N hXN] at hy'
    obtain ⟨x, hx, m, hmN, rfl⟩ := hy'
    have hmY : m ∈ Y := by
      have := Y.mul_mem (Y.inv_mem (hXY hx)) hy
      rwa [inv_mul_cancel_left] at this
    obtain ⟨k, hk⟩ := hpow m hmY
    obtain ⟨m', -, hmm'⟩ := hmY
    have hmm'' : (m' : G) = m := hmm'
    have hk' : mk (m' ^ p ^ k) = 1 := hQker _ (by rw [Subgroup.coe_pow, hmm'']; exact hk)
    have hord1 : orderOf (mk m') ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by rwa [map_pow] at hk')
    have hord2 : orderOf (mk m') ∣ Nat.card N :=
      (orderOf_map_dvd _ _).trans (by
        rw [← Subgroup.orderOf_coe, hmm'']
        exact Subgroup.orderOf_dvd_natCard N hmN)
    have hcop : Nat.Coprime (p ^ k) (Nat.card N) :=
      Nat.Coprime.pow_left k (glbPrimeCore_coprime p H)
    have h1 : orderOf (mk m') = 1 := Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
    have hmQ : m ∈ Q := hmm'' ▸ hkerQ m' (orderOf_eq_one_iff.mp h1)
    exact (X ⊔ Q).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hmQ)
  have heq : X ⊔ Q = Y := le_antisymm (sup_le hXY hQY) hYXQ
  rw [heq, hYsub]
  exact Subgroup.Normal.comap inferInstance mk

theorem stmtNormalSupOfLePCore :
    ∀ {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
      {M H R X : Subgroup G}, D1L2Data p n P M H R X → Asc81bEightFour → D1NoXBlock →
      barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) → ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal :=
  fun h h84 hD2 hX => h.normal_sup_of_le_pCore h84 hD2 hX

end CFSG.AGLEmbedding
