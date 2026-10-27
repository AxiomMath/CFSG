module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Core

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def StmtSp62MSide : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R V : Subgroup G},
    D1Sp62Data P M H R V → ∃ L : Subgroup G, Sp62BlockShape M H R L

theorem stmtSp62MSide_of (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) (hLevi : KFactBlockLeviU42) : StmtSp62MSide := by
  intro G _ _ P M H R V h
  have h3 := h.surv.ph3
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  obtain ⟨L, hL⟩ := h3.exists_weakSBlock h84 hD2
  obtain ⟨hVV, -, -, hKVN, -, ⟨d, ψ, hd, hψ, hker⟩, -, -⟩ := h.piece
  have hO3 := h.pCore_eq_bot h84 hD2
  have hLn := h.barM_normal h84 h86 hD2 hB3 hb hL
  set N := GLBPrimeCore 3 H with hN
  set Pi := (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L with hPi
  have hVPi := h.le_Pi hB3 hL
  have hPiK : Pi ≤ H ⊓ M := inf_le_left
  have hPiH : Pi ≤ H := hPiK.trans inf_le_left
  have hPiM : Pi ≤ M := hPiK.trans inf_le_right
  have hPiPL : barM M Pi ≤ blockParabolic M (pCoreOf 2 H) L :=
    h.barM_le h84 h86 hD2 hB3 hb hL le_rfl
  have hPLPi := blockParabolic_le_barM hKeq hL.le (le_rfl : Pi ≤ Pi)
  have hPiNPi : ∀ x ∈ Pi, x ∈ Subgroup.normalizer ((Pi ⊓ N : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      le_normalizer_glbPrimeCore 3 H (hPiH hx)⟩
  have hPiNV : ∀ x ∈ Pi, x ∈ Subgroup.normalizer ((Pi ⊓ (V ⊔ N) : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      hKVN (hPiK hx)⟩
  have hPLnorm : ∀ Y : Subgroup G, (∀ x ∈ Pi, x ∈ Subgroup.normalizer (Y : Set G)) →
      blockParabolic M (pCoreOf 2 H) L ≤
        Subgroup.normalizer (barM M Y : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro Y hY
    refine hPLPi.trans ?_
    rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
    exact mem_normalizer_barM hxM (hY x (Subgroup.mem_subgroupOf.mp hx))
  refine ⟨L, hL, fun L' hL' => h.barM_eq h84 h86 hD2 hB3 hb hL hL', hLn,
    ((Subgroup.map_mono (Subgroup.comap_mono (h.R_le_Pi hB3 hL))).trans hPiPL).trans
      (blockParabolic_le_barM' _ _ _), hO3, ?_⟩
  exact hLevi G M (pCoreOf 2 H) L h3.isKGroup.1 h3.asc81bHyp hL (h3.nineThree h93 hL)
    (h3.nineThree_not_one h85 hD2 hL).1 (h3.not_isSylowTwoOf_inf h85 hD2 hL)
    (fun l hl hcond => hb h3 h84 h86 hD2 hL l hl hcond) (barM M (Pi ⊓ N)) V
    (hVPi.trans hPiM) ((Subgroup.map_mono (Subgroup.comap_mono inf_le_left)).trans hPiPL)
    ((Subgroup.map_mono (Subgroup.comap_mono hVPi)).trans hPiPL) (hPLnorm _ hPiNPi)
    (Nat.Coprime.coprime_dvd_right ((card_barM_dvd (inf_le_left.trans hPiM)).trans
      (Subgroup.card_dvd_of_le inf_le_right)) (glbPrimeCore_coprime 3 H))
    (by rw [barM_sup_eq hVPi hPiH hPiM]; exact hPLnorm _ hPiNV)
    (h.relIndex_le h84 h86 hD2 hB3 hb hL) hVV d ψ hd hψ hker
    (h.card_sylow h84 h86 hD2 hB3 hb hL)
    (@not_dvd_card_center_of_normal _ _ _ 3 ⟨Nat.prime_three⟩ _ hLn hO3)

end CFSG.AGLEmbedding
