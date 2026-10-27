module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakLie
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeChevTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakRes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakSpor
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3Out
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaFiveUni
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.AGLEmbedding

open TauCeti
open CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.AGLEmbedding.KFactProofs.AlphaFive

@[expose] def AlphaThreeConclW2 (K : Type) [Group K] [Finite K] (T : Sylow 3 K) : Prop :=
  (KGenTwoModAbFix 3 K ∧ Nat.card (Subgroup.center K) = 3 ∧ KOutNormalSylow 3 K) ∨
    (Open.GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K))

@[expose] def KFactAlphaLieThreeW2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → ∀ d : ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) →
    Subgroup.center K ≠ ⊥ → IsPGroup 3 (Subgroup.center K) →
    IsCyclic (Subgroup.center K) → ∀ T : Sylow 3 K, AlphaThreeConclW2 K T

@[expose] def IsAlphaThreeResIndex (d : LieTypeIndex) : Prop :=
  (∃ (r : ℕ) (q : PrimePower), d = .twistedA r q ∧ 8 ≤ r ∧ 3 ∣ r + 1 ∧ q.card = 2) ∨
    (∃ q : PrimePower, d = .E6 q ∧ 3 ∣ q.card - 1) ∨
    (∃ q : PrimePower, d = .twistedE6 q ∧ 3 ∣ q.card + 1)

@[expose] def AlphaThreeLieResidual : Prop :=
  ∀ d : ValidLieTypeIndex, IsAlphaThreeResIndex d.1 →
    @CoverWeakGen (CFSGIndex.lie d).Group _ 3 ⟨Nat.prime_three⟩

theorem glbCore_eq_top_of_statedSU_odd {ℓ f : ℕ} {F : Type} [Field F] {n : ℕ}
    (hU : UnitaryFieldData ℓ f F) {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : ℓ ^ f ≠ 2) (hn : 5 ≤ n)
    (hpq : p ∣ ℓ ^ f + 1) (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU n (ℓ ^ f) F))
    (hpZ : p ∣ Nat.card (Subgroup.center K)) (T : Sylow p K) :
    Open.GLBCore p 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank p (⊤ : Subgroup K) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ζ, hζ, -⟩ := exists_orderOf_eq_norm_one hU hp hpq
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p hpZ
  have hz1 : (z : K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzp : (z : K) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  let φ : K →* StatedProj (StatedSU (m + 1) (ℓ ^ f) F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact glbCore_eq_top_of_torus (torusHyp_unitarySU hU hp hp2 hpq hζ (by omega)) hφ hker.le
    hperf (by rw [hker]; exact z.2) hz1 hzp (unitarySU_le_closure hU hq (by omega) ζ) T

theorem kFactAlphaLieThreeW2_of
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSL3 : KFactProofs.CoverThree.SL3CoverGenTwoModAbFix)
    (hU43 : KFactProofs.ThreeWeak.WeakGenU43) (hO73 : KFactProofs.ThreeWeak.WeakGenO73)
    (hG23 : KFactProofs.ThreeWeak.WeakGenG23) (hCin : KFactChevTwoInnerGen)
    (hRes : AlphaThreeLieResidual) : KFactAlphaLieThreeW2 := by
  intro K _ _ hK d ⟨e⟩ hZ hZp hZc T
  have hq' : CFSG.IsQuasisimple K := KFactProofs.CoverFive.isQuasisimple_of_open hK
  have h3 : 3 ∣ Nat.card (Subgroup.center K) :=
    KFactProofs.CoverFive.dvd_card_center_of_isPGroup Nat.prime_three hZ hZp
  have hperf : commutator K = ⊤ := hK.1
  have hidx := tripleCoverLie_of_griess hGA d K ⟨hq', h3, ⟨e⟩⟩
  have hcw : @CoverWeakGen (CFSGIndex.lie d).Group _ 3 ⟨Nat.prime_three⟩ →
      AlphaThreeConclW2 K T := fun h =>
    Or.inr (KFactProofs.ThreeWeak.weakCore_rank_of_coverWeakGen hK hZ hZp hZc e h T)
  have hcs : Open.GLBCore 3 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K) →
      AlphaThreeConclW2 K T := fun ⟨hc, h3'⟩ => Or.inr ⟨eq_top_iff.mpr (hc ▸
        CFSG.PreuniquenessRankFour.Helpers.rankThreeCore_le_weakCore 3 Nat.prime_three _), h3'⟩
  have ha : LocalAnalysis.RankThreeTheoremC.IsLinThreeCover3 d → AlphaThreeConclW2 K T :=
    fun hd => by
      have hZ3 := KFactProofs.CoverThree.card_center_linThree hGA hK hZp hZ hd e
      exact Or.inl ⟨hSL3 K hK hZ3 d hd ⟨e⟩, hZ3,
        LocalAnalysis.RankThreeTheoremC.kFactSL3OutNormalSylow K hK d hd ⟨e⟩⟩
  obtain ⟨dd, hv⟩ := d
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases dd with
  | A r q =>
    obtain ⟨hr, hq⟩ := hidx
    have hr1 : 1 ≤ r := hrange.1
    by_cases hr2 : r = 2
    · subst hr2
      exact ha (Or.inl ⟨q, rfl, hq⟩)
    · apply hcs
      obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ := (lieModel_typeA r q hv).2.resolve_right
        (fun h => absurd h.1 (Nat.succ_ne_zero r))
      refine glbCore_eq_top_of_statedSL hperf Nat.prime_three (by norm_num) (by omega) ?_
        (e.trans e') h3 T
      rw [hF]
      simpa only [PrimePower.card_def] using hq
  | twistedA r q =>
    rcases hidx with ⟨hr, hq⟩ | ⟨rfl, hq3⟩
    · have hr1 : 2 ≤ r := hrange.1
      by_cases hr2 : r = 2
      · subst hr2
        exact ha (Or.inr ⟨q, rfl, hq⟩)
      · by_cases hq2 : q.card = 2
        · by_cases hr5 : r = 5
          · subst hr5
            have hpe : q.p = 2 ∧ q.exponent = 1 :=
              (Nat.prime_two.pow_eq_iff).1 (by rw [← PrimePower.card_def]; exact hq2)
            have hw := hCin ⟨.twistedA 5 q, hv⟩ ⟨q, hpe.1, hpe.2, Or.inr (Or.inr (Or.inl rfl))⟩
              K hK ⟨e⟩ hZp hZc T
            have : Nontrivial K := by
              obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
              exact ⟨⟨x, 1, fun h => hx (Subtype.ext h)⟩⟩
            exact Or.inr ⟨hw, (three_le_pRank_of_weakCore_eq_top Nat.prime_three hw).trans
              (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three le_top)⟩
          · exact hcw (hRes ⟨.twistedA r q, hv⟩ (Or.inl ⟨r, q, rfl, by omega, hr, hq2⟩))
        · apply hcs
          obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ :=
            CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
          have hU : UnitaryFieldData q.p q.exponent F :=
            ⟨q.prime_p, q.exponent_pos, by rw [hF, ← pow_mul, mul_comm]⟩
          exact glbCore_eq_top_of_statedSU_odd hU hperf Nat.prime_three (by norm_num)
            (by simpa only [PrimePower.card_def] using hq2) (by omega)
            (by simpa only [PrimePower.card_def] using hq) e' h3 T
    · exact hcw (hU43 q hv hq3)
  | B r q =>
    obtain ⟨rfl, hq3⟩ := hidx
    exact hcw (hO73 q hv hq3)
  | G2 q => exact hcw (hG23 q hv hidx)
  | E6 q => exact hcw (hRes ⟨.E6 q, hv⟩ (Or.inr (Or.inl ⟨q, rfl, hidx⟩)))
  | twistedE6 q => exact hcw (hRes ⟨.twistedE6 q, hv⟩ (Or.inr (Or.inr ⟨q, rfl, hidx⟩)))
  | C r q => exact hidx.elim
  | D r q => exact hidx.elim
  | twistedD r q => exact hidx.elim
  | E7 q => exact hidx.elim
  | E8 q => exact hidx.elim
  | F4 q => exact hidx.elim
  | trialityD4 q => exact hidx.elim
  | suzuki m => exact hidx.elim
  | reeG2 m => exact hidx.elim
  | reeF4 m => exact hidx.elim
  | tits => exact hidx.elim

theorem kFactAlphaLieThreeW_of_W2 (h : KFactAlphaLieThreeW2) : KFactAlphaLieThreeW := by
  intro K _ _ hK d he hZ hZp hZc T
  rcases h K hK d he hZ hZp hZc T with ha | hc
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))

theorem coverWeakGen_of_normalizerGen {L : Type} [Group L] (hL : LiftableNormalizerGen L) :
    @CoverWeakGen L _ 3 ⟨Nat.prime_three⟩ := by
  intro K _ _ π hπ hker _ _ hZp _ T
  have e : K ⧸ Subgroup.center K ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  exact weakCore_eq_top_of_normalizerGen hL e hZp T

theorem alphaThreeLieResidual_of_normalizerGen
    (h : ∀ d : ValidLieTypeIndex, IsAlphaThreeResIndex d.1 →
      LiftableNormalizerGen (CFSGIndex.lie d).Group) : AlphaThreeLieResidual :=
  fun d hd => coverWeakGen_of_normalizerGen (h d hd)

end CFSG.AGLEmbedding
