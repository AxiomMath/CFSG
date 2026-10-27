module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaPThree
import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section BlockData

variable {G : Type} [Group G] [Finite G]

structure D1BlockData (p : ℕ) (P : Sylow p G) (M H R X : Subgroup G) : Prop
    extends D1SurvivorData p P M H R X where
  elem : IsElemAbelian p X
  card_le : p ^ 3 ≤ Nat.card X
  perfect_le : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ GLBPrimeCore p H
  ppd : ∃ (r : ℕ) (t : G), r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ p ∧ ¬ r ∣ p - 1 ∧
    Open.pRank p (H ⊓ M) < r ∧ t ∈ H ⊓ M ∧ t ∈ Subgroup.normalizer (X : Set G) ∧
    IsPGroup r (Subgroup.zpowers t) ∧ (∀ x ∈ X, t ^ r * x * (t ^ r)⁻¹ = x) ∧
    (∃ x ∈ X, t * x * t⁻¹ ≠ x) ∧
    ∀ k : ℕ, ¬ r ∣ k → ∀ Y : Subgroup G, Y ≤ X → t ^ k ∈ Subgroup.normalizer (Y : Set G) →
      Y = ⊥ ∨ Y = X

variable {p : ℕ} {P : Sylow p G} {M H R X : Subgroup G}

theorem D1PhaseThree.le_pRank_three_of_not_mem_normalizer' (h : D1PhaseThree p P M H R)
    (_hRank : StmtComponentRank) (_hLift : StmtBarPRankLift)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {r : ℕ} [Fact r.Prime] {g : G} (hgK : g ∈ H ⊓ M) (hg : IsPGroup r (Subgroup.zpowers g))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hgL : g ∉ Subgroup.normalizer (L : Set G)) : r ≤ Open.pRank 3 (H ⊓ M) :=
  h.toD1Escape.toTwoLocalPair.le_pRank_three_of_not_mem_normalizer hB3 hgK hg hL hgL

theorem D1BlockData.barM_le_centralizer (hB3 : StmtBlockThree) (hLB : StmtLemmaB)
    (h85 : Asc81bEightFive) (hD2 : D1NoXBlock) (h : D1BlockData p P M H R X) (hp3 : p = 3)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    barM M X ≤ Subgroup.centralizer (barM M L : Set _) := by
  have hKM : H ⊓ M ≤ M := inf_le_right
  have hXN : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      X ≤ Subgroup.normalizer (L' : Set G) := by
    intro L' hL'
    have hT : ∀ k ∈ H ⊓ M, barM M (L'.map (MulAut.conj k).toMonoidHom) ≤
        Subgroup.normalizer (barM M L' : Set _) := by
      intro k hk z hz
      have hLk := hL'.toIsTwoPrimeComponent.map_conj (hKM hk)
      by_cases he : barM M (L'.map (MulAut.conj k).toMonoidHom) = barM M L'
      · rw [he] at hz
        exact Subgroup.le_normalizer hz
      · have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hLk.component
          hL'.component he
        exact Subgroup.centralizer_le_normalizer _
          ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc hz)
    have hXbar := barM_le_of_le_preimage ((h.le_blockClosure hp3 hL' (hB3 h.ph3 hL')).trans
      (blockClosure_le_preimage hKM hL'.toIsTwoPrimeComponent hT))
    exact hL'.toIsTwoPrimeComponent.le_normalizer hXbar (h.le_R.trans h.ph3.le_M)
  obtain ⟨r, t, hr, hr2, hr3, hrp, hrp1, hrK, htK, htX, htr, htr1, htnt, hirr⟩ := h.ppd
  have : Fact r.Prime := ⟨hr⟩
  have htL : t ∈ Subgroup.normalizer (L : Set G) := by
    by_contra htL
    have hle := h.ph3.le_pRank_three_of_not_mem_normalizer' stmtComponentRank stmtBarPRankLift
      (fun L' hL' => hB3 h.ph3 hL') htK htr hL htL
    subst hp3
    omega
  have hpp : p.Prime := h.ph3.prime
  obtain ⟨hnot1, -⟩ := h.ph3.nineThree_not_one h85 hD2 hL
  have hKS : X ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    h.ph3.inf_eq_inf_normalizer_twoCore ▸ h.le_R.trans h.ph3.le_inf
  have hcop : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) →
      ⁅Y, Y⁆ = Y → p.Coprime (Nat.card Y) := by
    intro Y hY hperf
    have hYN := h.perfect_le Y (h.ph3.inf_eq_inf_normalizer_twoCore ▸ hY) hperf
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hYN)
      (glbPrimeCore_coprime p H)
  exact hLB G M (pCoreOf 2 H) L X p r t h.ph3.isKGroup.1 h.ph3.asc81bHyp hL hnot1
    (h.ph3.not_isSylowTwoOf_inf h85 hD2 hL) hpp h.ph3.ne_two hcop hKS (hXN L hL) h.elem
    h.card_le (h.ph3.inf_eq_inf_normalizer_twoCore ▸ htK) htL htX hr hr2 hr3 hrp hrp1 htr1 htnt
    (fun Y hYX hYt => hirr 1 (by simpa using hr.one_lt.ne') Y hYX (by simpa using hYt))

theorem D1BlockData.barM_le_pCore (hB3 : StmtBlockThree) (hLB : StmtLemmaB)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (h : D1BlockData p P M H R X) (hp3 : p = 3) :
    barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
  obtain ⟨L, hL⟩ := h.ph3.exists_weakSBlock h84 hD2
  have hKM : H ⊓ M ≤ M := inf_le_right
  have hKeq := h.ph3.inf_eq_inf_normalizer_twoCore
  have hXE := h.le_blockClosure hp3 hL (hB3 h.ph3 hL)
  set E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := GLBLayer ⊤ with hEdef
  have hXbarE : barM M X ≤ E := barM_le_of_le_preimage (hXE.trans
    (blockClosure_le_preimage hKM hL.toIsTwoPrimeComponent (fun k hk =>
      le_sSup (hL.toIsTwoPrimeComponent.map_conj (hKM hk)).component)))
  have hXcent : ∀ L' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L' ⊤ →
      barM M X ≤ Subgroup.centralizer (L' : Set _) := by
    intro L' hL'
    by_cases hex : ∃ k ∈ H ⊓ M, barM M (L.map (MulAut.conj k).toMonoidHom) = L'
    · obtain ⟨k, hk, rfl⟩ := hex
      exact h.barM_le_centralizer hB3 hLB h85 hD2 hp3 (hL.map_conj (hKM hk) (hKeq ▸ hk).2)
    · push Not at hex
      refine barM_le_of_le_preimage (hXE.trans
        (blockClosure_le_preimage hKM hL.toIsTwoPrimeComponent (fun k hk => ?_)))
      have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
        (hL.toIsTwoPrimeComponent.map_conj (hKM hk)).component hL' (hex k hk)
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc
  have hXC : barM M X ≤ Subgroup.centralizer (E : Set _) := by
    rw [Subgroup.le_centralizer_iff]
    exact sSup_le fun L' hL' => Subgroup.le_centralizer_iff.mp (hXcent L' hL')
  have hEn : E.Normal := glbLayer_top_normal
  have hZn : (E ⊓ Subgroup.centralizer (E : Set _)).Normal := inferInstance
  have hZ : ∀ a ∈ E ⊓ Subgroup.centralizer (E : Set _),
      ∀ b ∈ E ⊓ Subgroup.centralizer (E : Set _), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb.2 a ha.1
  have hXp : IsPGroup p (barM M X) := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hxp : (x : G) ^ p = 1 := h.elem.2 x (Subgroup.mem_subgroupOf.mp hx)
    have : x ^ p = 1 := Subtype.ext (by simpa using hxp)
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, this, map_one]
  exact le_pCore_of_le_normal_comm hZn hZ (le_inf hXbarE hXC) hXp

theorem D1BlockData.pCore_ne_bot (hB3 : StmtBlockThree) (hLB : StmtLemmaB)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (hD2 : D1NoXBlock)
    (h : D1BlockData p P M H R X) (hp3 : p = 3) :
    CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥ := by
  intro hbot
  have hle := h.barM_le_pCore hB3 hLB h84 h85 hD2 hp3
  rw [hbot, le_bot_iff] at hle
  apply h.ne_bot
  rw [eq_bot_iff]
  intro x hx
  have hxM : x ∈ M := h.le_R.trans h.ph3.le_M hx
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ = 1 := by
    have : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ barM M X :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    rw [hle] at this
    exact this
  have hxQ : x ∈ pCoreOf 2 M := coe_mem_pCoreOf_two_of_mk_eq_one ⟨x, hxM⟩ h1
  have hp : p.Prime := h.ph3.prime
  have : Fact p.Prime := ⟨hp⟩
  have hXp : IsPGroup p X := h.ph3.isPGroup_R.to_le h.le_R
  have hdisj := IsPGroup.disjoint_of_ne p 2 h.ph3.ne_two X (pCoreOf 2 M) hXp
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
  exact hdisj.le_bot ⟨hx, hxQ⟩

end BlockData

end CFSG.AGLEmbedding
