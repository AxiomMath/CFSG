module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292Defs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniMain
import CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294Lemmas
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.GLTheoremB (IsSCp isSCp_subgroupOf)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (I292.exists_conj_normalizes
  I292.exists_sylow_le_of_conj I292.le_normalizer_map_subtype K62.fusionIsSylowIn_of_isMax)
open P614K292

namespace P614K292

theorem pRank_le_of_frameNormalizer {X : Type} [Group X] [Finite X] {B T N : Subgroup X}
    (hSC : IsSCp 3 ⊤ B) (hT : IsMaxTwoInvariantIn B ⊤ T) (hTN : T ≤ N) (hBN : B ≤ N)
    (hsol : Group.IsSolvable ↥N) (hQN : ∃ Q : Sylow 3 X, (Q : Subgroup X) ≤ N) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ CFSG.Open.pRank 3 (normalizer (T : Set X)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨Q, hQN⟩ := hQN
  have hBp : IsPGroup 3 B := fun b => ⟨1, Subtype.ext (by simpa using hSC.2.1.2 b.1 b.2)⟩
  have hT2 : IsPGroup 2 T := hT.1.2.1
  have hBT : B ≤ normalizer (T : Set X) := hT.1.2.2
  have hlay : GLAPLayer 3 N = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt.glaPLayer_eq_bot_of_isSolvable hp
  have hlayer : GLAPLayer 3 (⊤ : Subgroup ↥N) = ⊥ :=
    CFSG.LocalAnalysis.RankFourTheoremC.glaPLayer_top_eq_bot_of_subgroup hp N hlay
  have hSC' : IsSCp 3 ⊤ (B.subgroupOf N) := isSCp_subgroupOf hSC hBN
  have key := GL83.I_20_1_proved ↥N 3 hp hp2 hlayer (B.subgroupOf N) hSC'.2.1
    (fun E hE hBE => hSC'.2.2 E le_top hE hBE)
  have hT'cop : Nat.Coprime 3 (Nat.card (T.subgroupOf N)) := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hT'norm : B.subgroupOf N ≤ normalizer ((T.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := Subgroup.mem_normalizer_iff.1 (hBT ((Subgroup.mem_subgroupOf).1 hb)) (y : X)
    simpa [Subgroup.mem_subgroupOf] using this
  have hT'O : T.subgroupOf N ≤ GLAPPrimeCoreOf 3 (⊤ : Subgroup ↥N) := by
    rw [← key]
    exact le_iSup_of_le _ (le_iSup_of_le hT'cop (le_iSup_of_le hT'norm le_rfl))
  rw [GL83.glaPPrimeCoreOf_top_eq] at hT'O
  set O : Subgroup ↥N := primeComplementCore (G := ↥N) 3 with hO
  haveI hOn : O.Normal := inferInstance
  set D : Subgroup X := O.map N.subtype with hD
  have hTD : T ≤ D := fun t ht => ⟨⟨t, hTN ht⟩, hT'O (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hDcop : ¬ 3 ∣ Nat.card D := by
    rw [hD, Subgroup.card_map_of_injective N.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (primeComplementCore_coprime 3)
  have hND : N ≤ normalizer (D : Set X) := I292.le_normalizer_map_subtype O
  have hDfus : fusionIsSylowIn 2 T D :=
    K62.fusionIsSylowIn_of_isMax hp hBp hT hTD hDcop (hBN.trans hND)
  obtain ⟨c, -, hc⟩ := I292.exists_conj_normalizes hp hDcop hDfus Q.isPGroup' (hQN.trans hND)
  obtain ⟨Q', hQ'⟩ := I292.exists_sylow_le_of_conj Q c hc
  exact (CFSG.LocalAnalysis.RankThreeTheoremC.pRank_le_pRank_sylow hp Q' ⊤).trans
    (pRank_mono 3 (by norm_num) hQ')

end P614K292

theorem kFact292_of_pieces (h1 : KD292Shape3) (h2 : KD292TwoFrame3) (h3 : KD292ThreeFrameLin3)
    (h4 : KD292UniOuter3) (h5 : KD292ThreeFrameNorm3) (h5x : KD292FrameNormX3)
    (h7a : KD292CaseA3) (h7b : KD292CaseB3) (h291 : KFactProofs.T29.GL83I291Three) :
    KFact292 := by
  intro X _ _ hcat hcore L hL hLu hrank hperf x hx hcent Px B hPx hBPx hBe hΩ T hT
  have hcfg : LinUniCfgThree L x Px B :=
    ⟨⟨hcat, hcore, hL, hLu, hrank, hx, hcent⟩, hperf, hPx, hBPx, hBe, hΩ⟩
  obtain ⟨π, p, f, K, _, ν, y, hS⟩ := h1 h291 X L x Px B hcfg
  have hT2 : IsPGroup 2 T := hT.1.2.1
  have hxB : x ∈ B := by
    rw [hS.plane]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hxT : x ∈ normalizer (T : Set X) := hT.1.2.2 hxB
  have hend : ∀ v : Fin 3 → K, v ≠ 0 → (π = false → YFrameOrth (p ^ f) y v) →
      T ≤ normalizer (threeFrameIn ν y v : Set X) →
      CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ CFSG.Open.pRank 3 (normalizer (T : Set X)) := by
    intro v hv horth hTv
    obtain ⟨hBN, hsol, hQ⟩ := h5x h5 X L x Px B π p f K ν y hcfg hS v hv horth
    exact pRank_le_of_frameNormalizer hS.sc hT hTv hBN hsol hQ
  by_cases hTL : T ⊓ L = ⊥
  ·
    obtain ⟨hlin, huni⟩ := h7a h3 h4 X L x Px B π p f K ν y hcfg hS T hT2 hxT hTL
    rcases Bool.eq_false_or_eq_true π with hπ | hπ
    · obtain ⟨v, hv, hTv⟩ := hlin hπ
      exact hend v hv (fun h => absurd (hπ.symm.trans h) (by decide)) hTv
    · have hN : normalizer ((⊥ : Subgroup X) : Set X) = ⊤ := Subgroup.normalizer_eq_top ⊥
      rw [huni hπ, hN]
  ·
    obtain ⟨v, hv, horth, hTv⟩ := h7b h2 h5 X L x Px B π p f K ν y hcfg hS T hT2 hxT hTL
    exact hend v hv horth hTv

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
