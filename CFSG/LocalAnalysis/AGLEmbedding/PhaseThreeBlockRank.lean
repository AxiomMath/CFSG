module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.LocalAnalysis.AGLEmbedding.LemmaPThree
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockRank
import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockClosure
public import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPair
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section BlockRank

variable {G : Type} [Group G] [Finite G]

theorem D1PhaseThree.false_of_four_le_pRank' {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q < p) (h4 : 4 ≤ Open.pRank q (H ⊓ M)) : False := by
  have hH4 : 4 ≤ Open.pRank q H := h4.trans (pRank_mono q hq inf_le_left)
  have hβ : q ∈ GLBBetaFour G := by
    refine ⟨hq, hq2, prime_dvd_card_of_positive_rank q hq H (by omega), ?_⟩
    exact hH4.trans (le_csSup (twoLocalRank_bddAbove q hq) ⟨H, h.maxTwoLocal_H.1, rfl⟩)
  exact false_of_guestPrime h.glob.pre hβ (hind q hβ hqp) h.maxTwoLocal_M
    h.maxTwoLocal_H h.not_le (by omega)

theorem D1PhaseThree.le_pRank_three_of_injective_conj {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (h : D1PhaseThree p P M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {m : ℕ} (g : Fin m → G)
    (hgK : ∀ j, g j ∈ H ⊓ M)
    (hinj : Function.Injective fun j => L.map (MulAut.conj (g j)).toMonoidHom) :
    m ≤ Open.pRank 3 (H ⊓ M) :=
  h.toD1Escape.toTwoLocalPair.le_pRank_three_of_injective_conj hB3 hL g hgK hinj

theorem D1PhaseThree.relIndex_le_pRank_three {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {A : Subgroup G} (hAK : A ≤ H ⊓ M) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    (A ⊓ Subgroup.normalizer (L : Set G)).relIndex A ≤ Open.pRank 3 (H ⊓ M) :=
  h.toD1Escape.toTwoLocalPair.relIndex_le_pRank_three hB3 hAK hL

theorem D1PhaseThree.le_blockClosure_of_dichotomy {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) (hp3 : p = 3) {X : Subgroup G}
    (hD : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
      Y ≤ GLBPrimeCore p H ∨ X ≤ Y)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hB : BlockHasThree M (pCoreOf 2 H) L) : X ≤ blockClosure M (H ⊓ M) L :=
  h.toD1Escape.toTwoLocalPair.le_blockClosure_of_dichotomy hp3 hD hL hB

theorem barM_le_pCore_of_le_blockClosure {M K L W : Subgroup G} (hKM : K ≤ M)
    (hL : IsTwoPrimeComponent M L) (hWE : W ≤ blockClosure M K L) {q : ℕ}
    (hWq : IsPGroup q W)
    (hWC : ∀ k ∈ K, barM M W ≤
      Subgroup.centralizer (barM M (L.map (MulAut.conj k).toMonoidHom) : Set _)) :
    barM M W ≤ CFSG.pCore q (↥M ⧸ CFSG.pCore 2 ↥M) := by
  set E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := GLBLayer ⊤ with hEdef
  have hWbarE : barM M W ≤ E := barM_le_of_le_preimage (hWE.trans
    (blockClosure_le_preimage hKM hL (fun k hk => le_sSup (hL.map_conj (hKM hk)).component)))
  have hWcent : ∀ L' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L' ⊤ →
      barM M W ≤ Subgroup.centralizer (L' : Set _) := by
    intro L' hL'
    by_cases hex : ∃ k ∈ K, barM M (L.map (MulAut.conj k).toMonoidHom) = L'
    · obtain ⟨k, hk, rfl⟩ := hex
      exact hWC k hk
    · push Not at hex
      refine barM_le_of_le_preimage (hWE.trans
        (blockClosure_le_preimage hKM hL (fun k hk => ?_)))
      have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
        (hL.map_conj (hKM hk)).component hL' (hex k hk)
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc
  have hWC' : barM M W ≤ Subgroup.centralizer (E : Set _) := by
    rw [Subgroup.le_centralizer_iff]
    exact sSup_le fun L' hL' => Subgroup.le_centralizer_iff.mp (hWcent L' hL')
  have hEn : E.Normal := glbLayer_top_normal
  have hZn : (E ⊓ Subgroup.centralizer (E : Set _)).Normal := inferInstance
  have hZ : ∀ a ∈ E ⊓ Subgroup.centralizer (E : Set _),
      ∀ b ∈ E ⊓ Subgroup.centralizer (E : Set _), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb.2 a ha.1
  have hWp : IsPGroup q (barM M W) := (hWq.comap_subtype (K := M)).map _
  exact le_pCore_of_le_normal_comm hZn hZ (le_inf hWbarE hWC') hWp

theorem D1PhaseThree.barM_le_pCore_of_forall_centralizer {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (h : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) (hp3 : p = 3) {X : Subgroup G} (hXR : X ≤ R)
    (hD : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
      Y ≤ GLBPrimeCore p H ∨ X ≤ Y)
    (hR1 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M X ≤ Subgroup.centralizer (barM M L : Set _)) :
    barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
  obtain ⟨L, hL⟩ := h.exists_weakSBlock h84 hD2
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  exact barM_le_pCore_of_le_blockClosure inf_le_right hL.toIsTwoPrimeComponent
    (h.le_blockClosure_of_dichotomy hp3 hD hL (hB3 h hL))
    ((h.isPGroup_R.to_le hXR)) fun k hk => hR1 _ (hL.map_conj hk.2 (hKeq ▸ hk).2)

end BlockRank

end CFSG.AGLEmbedding
