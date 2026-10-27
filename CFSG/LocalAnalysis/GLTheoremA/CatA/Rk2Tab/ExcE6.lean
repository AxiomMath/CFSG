module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num
public import CFSG.LocalAnalysis.SectionRank.PRankIndex
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerExcTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Glue
public import CFSG.HardMathSupport.Lang.AnisoE6.F4InTwistedE6
public import CFSG.LieType.SeitzGeneration.ExcTorusSylow
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE6
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Six
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.UpperReduce
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6JBoundTw
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwSetup
public import CFSG.LieType.SeitzGeneration.ExcTorusRankTw
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedTorus
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Eight
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Ten
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Twelve
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Eighteen
public import CFSG.HardMathSupport.Lang.TwE6Step3.SylowTorusSix
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Lang.AnisoE6.CatBridge
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.RankThree.PartOne.KE.SLnShape

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Blueprint.Chevalley CFSG.Blueprint.Multiplier CFSG.LieType.Chevalley
open CFSG.LieType.SeitzGeneration
open CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial


@[expose] def Rk2E6Covered (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ) : Prop :=
  p ≠ 3 ∨
    (p = 3 ∧ ¬ 3 ∣ Nat.card (Subgroup.center K) ∧
      ((lab.tag = .E6 ∧ rk2Ord p lab.n = 1) ∨
        (lab.tag = .twE6 ∧ rk2Ord p lab.n = 2)))

@[expose] def Rk2E6CoverThreeFrontier : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ),
    Rk2IsLabel K lab → lab.tag = .E6 → p = 3 → 3 ∣ Nat.card (Subgroup.center K) →
      CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n)

@[expose] def Rk2TwE6CoverThreeFrontier : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ),
    Rk2IsLabel K lab → lab.tag = .twE6 → p = 3 → 3 ∣ Nat.card (Subgroup.center K) →
      CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n)

structure Rk2E6Frontier : Prop where
  coverE6 : Rk2E6CoverThreeFrontier
  coverTwE6 : Rk2TwE6CoverThreeFrontier

private theorem sylowTorus_E6_one {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 1) :
    SylowTorus (adjointGroup Tag.E6 K) p 6 := by
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hother : ∀ d ∈ [1, 1, 1, 1, 1, 1], d ≠ 1 → ¬ p ∣ d := by
    intro d hd hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (hne rfl).elim
  have hdeg : ∀ d ∈ degreesE Tag.E6, 1 ∣ d → ¬ p ∣ d / 1 := by
    intro d hd _
    rw [Nat.div_one]
    simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · intro hdvd; have hle := Nat.le_of_dvd (by norm_num) hdvd; omega
    · intro hdvd; have hle := Nat.le_of_dvd (by norm_num) hdvd; omega
    · intro hdvd; have hle := Nat.le_of_dvd (by norm_num) hdvd; omega
    · intro hdvd; have hle := Nat.le_of_dvd (by norm_num : 0 < 8) hdvd
      interval_cases p
      all_goals (try norm_num at hp; try norm_num at hdvd; try omega)
    · intro hdvd; have hle := Nat.le_of_dvd (by norm_num : 0 < 9) hdvd
      interval_cases p
      all_goals (try norm_num at hp; try norm_num at hdvd; try omega)
    · intro hdvd; have hle := Nat.le_of_dvd (by norm_num : 0 < 12) hdvd
      interval_cases p
      all_goals (try norm_num at hp; try norm_num at hdvd; try omega)
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.sylowTorus_of_blocks_of_three_lt 3
    (Or.inl ⟨rfl, rfl⟩) K hp (by omega) hpq
    (CFSG.RankThree.PartOne.KE.IsWeylMatrix.of_word Tag.E6 e6OneWord) [1, 1, 1, 1, 1, 1]
    e6One_charpoly e6One_pow he hother hdeg ?_
  decide

private theorem rk2_not_dvd_card_center_twE6 {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hQ : CFSG.IsQuasisimple K) (hM : MarkedModel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .twE6) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag hM
  subst htag
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    (K ⧸ Subgroup.center K) (markTag ⟨.twE6, r, n⟩) (markRank ⟨.twE6, r, n⟩)
    (markChar ⟨.twE6, r, n⟩) (markDeg ⟨.twE6, r, n⟩) hM
  have hg : genericOrders (markTag ⟨.twE6, r, n⟩) (markRank ⟨.twE6, r, n⟩)
      (markChar ⟨.twE6, r, n⟩) (markDeg ⟨.twE6, r, n⟩) = (Nat.gcd 3 (2 ^ n + 1), 1) := rfl
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) =
      Nat.gcd 3 (2 ^ n + 1) * (if n = 1 then 4 else 1) := by
    rw [Nat.card_congr eM.toEquiv,
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg]
    by_cases hn : n = 1
    · subst hn
      simp [exceptionalOrders, markTag, markRank, markChar, markDeg]
    · simp [exceptionalOrders, markTag, markRank, markChar, markDeg, hn]
  haveI : Finite (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcard]
      exact (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ (by norm_num))
        (by by_cases hn : n = 1 <;> simp [hn])).ne')
  have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  rw [hcard] at hdvd
  intro h
  have hpdiv : p ∣ Nat.gcd 3 (2 ^ n + 1) * (if n = 1 then 4 else 1) := h.trans hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hpdiv with hg' | h4
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      (hg'.trans (Nat.gcd_dvd_left _ _)))
  · by_cases hn : n = 1
    · have hp4 : p ∣ 4 := by simpa [hn] using h4
      have hp2' : p ∣ 2 := by
        rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 2 by simpa using hp4) with h' | h'
        · exact h'
        · exact h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2')
    · have hp1 : p ∣ 1 := by simpa [hn] using h4
      exact hp.not_dvd_one hp1

theorem rk2Ord_three_eq_one_or_two (n : ℕ) :
    rk2Ord 3 n = 1 ∨ rk2Ord 3 n = 2 := by
  have h2 : (((2 : ZMod 3) ^ n)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm n 2, pow_mul]
    have h4 : ((2 : ZMod 3)) ^ 2 = 1 := by decide
    rw [h4, one_pow]
  have hdvd : rk2Ord 3 n ∣ 2 := by
    rw [rk2Ord]
    exact orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem mem_E6_degrees_of_degCount_pos {m : ℕ} (h : 0 < degCount Tag.E6 m) :
    m ∈ [1, 2, 3, 4, 5, 6, 8, 9, 12] := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E6) (by simp) h
  interval_cases m <;> first | (exfalso; revert h; decide) | decide

theorem mem_twE6_orders_of_degCountTw_pos {m : ℕ} (h : 0 < degCountTw m) :
    m ∈ [1, 2, 3, 4, 6, 8, 10, 12, 18] := by
  have h60 := le_sixty_of_degCountTw_pos h
  interval_cases m <;> first | (exfalso; revert h; decide) | decide

private theorem pRank_adjoint_E6_five_le_six {K : Type} [Field K] [Finite K]
    (h : orderOf ((Nat.card K : ℕ) : ZMod 5) = 1) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 6 := by
  have hq1 : ((Nat.card K : ℕ) : ZMod 5) = 1 := orderOf_eq_one_iff.1 h
  have h5 : 5 ∣ Nat.card K - 1 := by
    rw [← ZMod.natCast_eq_zero_iff (Nat.card K - 1) 5, Nat.cast_sub Nat.card_pos, hq1,
      Nat.cast_one, sub_self]
  have hT := CFSG.StandardType.TableBExc.ggExcToralRankInput_E6_of_ne_three (K := K)
    Nat.prime_five (by norm_num) (by norm_num) h5
  have hV : Nat.card (CFSG.StandardType.TableBExc.torusPow Tag.E6 K 5) = 5 ^ Tag.E6.rank := by
    have h := CFSG.StandardType.TableBExc.card_torusPow_E6 (K := K) Nat.prime_five
      (by norm_num) h5
    have hrank : Tag.E6.rank = 6 := rfl
    simpa [hrank] using h
  refine CFSG.SectionRank.pRank_le (by norm_num : 1 < 5) ?_
  intro E _ hE
  have hrank : Tag.E6.rank = 6 := rfl
  simpa [hrank] using hT.card_le hV hE

private theorem three_dvd_two_pow_sub_one_of_rk2Ord_eq_one {n : ℕ}
    (h : rk2Ord 3 n = 1) : 3 ∣ 2 ^ n - 1 := by
  have hq : ((2 : ZMod 3) ^ n) = 1 := orderOf_eq_one_iff.1 (by simpa [rk2Ord] using h)
  have hcast : (((2 ^ n : ℕ)) : ZMod 3) = 1 := by
    rw [Nat.cast_pow]
    exact hq
  rw [← ZMod.natCast_eq_zero_iff (2 ^ n - 1) 3,
    Nat.cast_sub (Nat.one_le_two_pow), hcast, Nat.cast_one, sub_self]

private theorem three_dvd_two_pow_add_one_of_rk2Ord_eq_two {n : ℕ}
    (h : rk2Ord 3 n = 2) : 3 ∣ 2 ^ n + 1 := by
  have hq2 : (((2 : ZMod 3) ^ n)) ^ 2 = 1 := by
    have hpow := pow_orderOf_eq_one ((2 : ZMod 3) ^ n)
    have hord : orderOf ((2 : ZMod 3) ^ n) = 2 := by simpa [rk2Ord] using h
    rwa [hord] at hpow
  have hfac : (((2 : ZMod 3) ^ n) - 1) * (((2 : ZMod 3) ^ n) + 1) = 0 := by
    calc (((2 : ZMod 3) ^ n) - 1) * (((2 : ZMod 3) ^ n) + 1) =
        (((2 : ZMod 3) ^ n)) ^ 2 - 1 := by ring
      _ = 0 := by rw [hq2]; ring
  have hqne : ((2 : ZMod 3) ^ n) ≠ 1 := by
    intro hq
    have : rk2Ord 3 n = 1 := by
      rw [rk2Ord]
      exact orderOf_eq_one_iff.2 hq
    omega
  have hqneg : ((2 : ZMod 3) ^ n) = -1 := by
    rcases mul_eq_zero.1 hfac with h' | h'
    · exact absurd (sub_eq_zero.1 h') hqne
    · linear_combination h'
  have hcast : (((2 ^ n : ℕ)) : ZMod 3) = -1 := by
    rw [Nat.cast_pow]
    exact hqneg
  rw [← ZMod.natCast_eq_zero_iff (2 ^ n + 1) 3, Nat.cast_add, hcast, Nat.cast_one,
    neg_add_cancel]

private theorem mod_three_eq_two_of_dvd_add_one {n : ℕ} (h : 3 ∣ n + 1) : n % 3 = 2 := by
  have hz : ((n + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff (n + 1) 3).2 h
  push_cast at hz
  have hc : ((n : ℕ) : ZMod 3) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    simpa using hz
  have h2 : ((n : ℕ) : ZMod 3) = (2 : ZMod 3) := by
    rw [hc]
    decide
  have h := (ZMod.natCast_eq_natCast_iff' n 2 3).1 h2
  simpa using h

private theorem pRank_le_six_E6_of_three_dvd {S : Type} [Group S] [Finite S] {n : ℕ}
    (hM : CFSG.Blueprint.LieModel S .E6 0 2 n) (h3 : 3 ∣ 2 ^ n - 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 6 :=
  (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.e6RankUpper S .E6 0 2 n hM
    (Or.inl ⟨rfl, h3⟩)).1

private theorem pRank_le_six_twE6_of_three_dvd {S : Type} [Group S] [Finite S] {n : ℕ}
    (hM : CFSG.Blueprint.LieModel S .twistedE6 0 2 n) (h3 : 3 ∣ 2 ^ n + 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 6 :=
  (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.e6RankUpper S .twistedE6 0 2 n hM
    (Or.inr ⟨rfl, h3⟩)).1

private theorem exists_adjointGroup_E6_of_marked {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hM : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 lab.n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ lab.n ∧
      Nonempty (K ⧸ Subgroup.center K ≃* adjointGroup Tag.E6 F) := by
  obtain ⟨-, -, hU⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedModel_of_lieModel_E6 hM
  exact CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup Tag.E6 hU

theorem exists_twistedE6RootGroup_of_marked {K : Type} [Group K] [Finite K]
    {lab : GLALabel}
    (hM : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F ≃+* F),
      Nat.card F = (2 ^ lab.n) ^ 2 ∧ (∀ c, σ c = c ^ (2 ^ lab.n)) ∧
        Nonempty (K ⧸ Subgroup.center K ≃* twistedE6RootGroup F σ) := by
  obtain ⟨-, hf1, hT⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedChevalleyModel_of_lieModel hM
  have hn1 : 1 ≤ lab.n := hf1
  obtain ⟨F, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hT
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hn1 F hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  rw [← hσσ'] at e
  have hσ'' : ∀ c, σ'.toRingHom c = c ^ (2 ^ lab.n) := fun c => hσ' c
  have hc' : Subgroup.center ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived
      σ'.toRingHom) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.center_twDerived_eq_bot σ'.toRingHom
      Nat.prime_two hn1 hcard hσ''
  obtain ⟨-, -, hΓ, -, -⟩ := finite_fixed_root_group_perfect .E6 Nat.prime_two hn1 F hcard
    σ'.toRingHom hσ''
  let e2 : CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .E6 F σ'.toRingHom) ≃*
      ↥(twistedE6RootGroup F σ') :=
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.derivedCentralQuotientEquiv σ'.toRingHom
      hc').trans (MulEquiv.subgroupCongr hΓ)
  exact ⟨F, inferInstance, inferInstance, σ', hcard, hσ', ⟨e.trans e2⟩⟩

private theorem pRank_adjoint_E6_le_of_mem {K : Type} [Field K] [Finite K] {lab : GLALabel}
    {p m : ℕ} (htag : lab.tag = .E6) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hm : m ∈ [2, 3, 4, 5, 6, 8, 9, 12])
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = m) :
    CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ rk2Mult lab m := by
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    have hle : p ≤ 4 := by omega
    interval_cases p
    · exact absurd rfl hp2
    · exact absurd rfl hp3
    · exact absurd hp (by norm_num)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · calc CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 4 :=
        pRank_le_of_sylowTorusDatum
          (CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E6_two K hp (by omega) he) hp
      _ = rk2Mult lab 2 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 3 :=
        pRank_le_of_sylowTorusDatum
          (CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E6_three K hp (by omega) he) hp
      _ = rk2Mult lab 3 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 2 :=
        pRank_le_of_sylowTorusDatum (sylowTorus_E6_four K hp he) hp
      _ = rk2Mult lab 4 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 1 :=
        pRank_le_of_sylowTorusDatum (sylowTorus_E6_five K hp he) hp
      _ = rk2Mult lab 5 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 2 :=
        pRank_le_of_sylowTorusDatum (sylowTorus_E6_six K hp he) hp
      _ = rk2Mult lab 6 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 1 :=
        pRank_le_of_sylowTorusDatum (sylowTorus_E6_eight K hp he) hp
      _ = rk2Mult lab 8 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 1 :=
        pRank_le_of_sylowTorusDatum (sylowTorus_E6_nine K hp he) hp
      _ = rk2Mult lab 9 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 1 :=
        pRank_le_of_sylowTorusDatum (sylowTorus_E6_twelve K hp he) hp
      _ = rk2Mult lab 12 := by simp [rk2Mult, htag, rk2Cnt]

private theorem pRank_le_of_model_E6 {K : Type} [Group K] [Finite K] {lab : GLALabel} {p : ℕ}
    (htag : lab.tag = .E6)
    (hM : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center K)) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    have hle : p ≤ 4 := by omega
    interval_cases p
    · exact absurd rfl hp2
    · exact absurd rfl hp3
    · exact absurd hp (by norm_num)
  obtain ⟨K', _, _, hcard, ⟨e⟩⟩ := exists_adjointGroup_E6_of_marked hM
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (adjointGroup Tag.E6 K') := generated_group_finite Tag.E6 K'
  have heord : orderOf ((Nat.card K' : ℕ) : ZMod p) = rk2Ord p lab.n := by
    have hcast : (((2 : ZMod p)) ^ lab.n) = (((2 ^ lab.n : ℕ)) : ZMod p) := by
      push_cast
      rfl
    rw [hcard, ← hcast, rk2Ord]
  have hZeq : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
      CFSG.Open.pRank p (⊤ : Subgroup K) :=
    CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hpZ
  have hGeq : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
      CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K')) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  have hKp : CFSG.Open.pRank p (⊤ : Subgroup K) =
      CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K')) := hZeq.symm.trans hGeq
  by_cases hmem : rk2Ord p lab.n ∈ [1, 2, 3, 4, 5, 6, 8, 9, 12]
  · have hb : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K')) ≤
        rk2Mult lab (rk2Ord p lab.n) := by
      by_cases hm1 : rk2Ord p lab.n = 1
      · have he1 : orderOf ((Nat.card K' : ℕ) : ZMod p) = 1 := heord.trans hm1
        by_cases hp5' : p = 5
        · subst hp5'
          have hb5 : CFSG.Open.pRank 5 (⊤ : Subgroup (adjointGroup Tag.E6 K')) ≤ 6 :=
            pRank_adjoint_E6_five_le_six (by simpa using he1)
          calc CFSG.Open.pRank 5 (⊤ : Subgroup (adjointGroup Tag.E6 K')) ≤ 6 := hb5
            _ = rk2Mult lab (rk2Ord 5 lab.n) := by
                rw [hm1]
                simp [rk2Mult, htag, rk2Cnt]
        · have hp7 : 7 ≤ p := by
            have h2 := hp.two_le
            rcases Nat.lt_or_ge p 7 with hlt | hge
            · interval_cases p <;>
                first | exact absurd rfl hp2 | exact absurd rfl hp3 |
                  exact absurd rfl hp5' | exact absurd hp (by norm_num)
            · exact hge
          calc CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K')) ≤ 6 :=
                pRank_le_of_sylowTorusDatum (sylowTorus_E6_one hp hp7 he1) hp
            _ = rk2Mult lab (rk2Ord p lab.n) := by
                rw [hm1]
                simp [rk2Mult, htag, rk2Cnt]
      · have hm : rk2Ord p lab.n ∈ [2, 3, 4, 5, 6, 8, 9, 12] := by
          rcases List.mem_cons.1 hmem with h | h
          · exact absurd h hm1
          · exact h
        exact pRank_adjoint_E6_le_of_mem htag hp hp2 hp3 hm heord
    exact hKp.trans_le hb
  · have h0 : degCount Tag.E6 (rk2Ord p lab.n) = 0 := by
      by_contra hne
      exact hmem (mem_E6_degrees_of_degCount_pos (Nat.pos_of_ne_zero hne))
    have hpq : ¬ p ∣ Nat.card K' := by
      rw [hcard]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
    have hzero : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K')) = 0 := by
      refine le_antisymm ?_ (Nat.zero_le _)
      refine CFSG.SectionRank.pRank_le hp.one_lt ?_
      intro E _ hE
      rw [elemAbelian_card_eq_one_of_degCount_zero (Or.inl rfl) K' hp (by omega) hpq heord h0 hE]
      simp
    calc CFSG.Open.pRank p (⊤ : Subgroup K)
        = CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.E6 K')) := hKp
      _ = 0 := hzero
      _ ≤ rk2Mult lab (rk2Ord p lab.n) := Nat.zero_le _

private theorem pRank_twisted_E6_le_of_mem {K : Type} [Field K] [Finite K] {lab : GLALabel}
    {ℓ f p m : ℕ} (htag : lab.tag = .twE6) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hm : m ∈ [1, 3, 4, 6, 8, 10, 12, 18])
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = m) :
    CFSG.Open.pRank p (⊤ : Subgroup (twistedE6RootGroup K σ)) ≤ rk2Mult lab m := by
  haveI : Fact p.Prime := ⟨hp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hpq : ¬ p ∣ ℓ ^ f := not_dvd_of_orderOf_pos hp he (by norm_num)
    calc CFSG.Open.pRank p (⊤ : Subgroup (twistedE6RootGroup K σ)) ≤ 4 :=
          pRank_le_of_sylowTorusDatum
            (CFSG.StandardType.ExcFrames.sylowTorus_twistedE6_one hℓ hf K hcard σ hσ hp hp5
              hpq he) hp
      _ = rk2Mult lab 1 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (twistedE6RootGroup K σ)) ≤ 2 :=
          pRank_le_of_sylowTorusDatum (sylowTorus_twistedE6_three hℓ hf K hcard σ hσ hp he) hp
      _ = rk2Mult lab 3 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (twistedE6RootGroup K σ)) ≤ 2 :=
          pRank_le_of_sylowTorusDatum (sylowTorus_twistedE6_four hℓ hf K hcard σ hσ hp he) hp
      _ = rk2Mult lab 4 := by simp [rk2Mult, htag, rk2Cnt]
  · have hpq : ¬ p ∣ ℓ ^ f := not_dvd_of_orderOf_pos hp he (by norm_num)
    have h6dvd : 6 ∣ p - 1 := by
      have hq0 : (((ℓ ^ f : ℕ)) : ZMod p) ≠ 0 := fun h =>
        hpq ((ZMod.natCast_eq_zero_iff _ _).1 h)
      rw [← he]
      exact ZMod.orderOf_dvd_card_sub_one hq0
    have hp7 : 7 ≤ p := by
      have hle := Nat.le_of_dvd (by omega) h6dvd
      omega
    calc CFSG.Open.pRank p (⊤ : Subgroup (twistedE6RootGroup K σ)) ≤ 3 :=
          pRank_le_of_sylowTorusDatum
            (CFSG.HardMathSupport.Lang.TwE6Step3.sylowTorus_twistedE6_six hℓ hf K hcard σ hσ hp
              hp7 hpq he) hp
      _ = rk2Mult lab 6 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (twistedE6RootGroup K σ)) ≤ 1 :=
          pRank_le_of_sylowTorusDatum (sylowTorus_twistedE6_eight hℓ hf K hcard σ hσ hp he) hp
      _ = rk2Mult lab 8 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (twistedE6RootGroup K σ)) ≤ 1 :=
          pRank_le_of_sylowTorusDatum (sylowTorus_twistedE6_ten hℓ hf K hcard σ hσ hp he) hp
      _ = rk2Mult lab 10 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (twistedE6RootGroup K σ)) ≤ 1 :=
          pRank_le_of_sylowTorusDatum (sylowTorus_twistedE6_twelve hℓ hf K hcard σ hσ hp he) hp
      _ = rk2Mult lab 12 := by simp [rk2Mult, htag, rk2Cnt]
  · calc CFSG.Open.pRank p (⊤ : Subgroup (twistedE6RootGroup K σ)) ≤ 1 :=
          pRank_le_of_sylowTorusDatum (sylowTorus_twistedE6_eighteen hℓ hf K hcard σ hσ hp he) hp
      _ = rk2Mult lab 18 := by simp [rk2Mult, htag, rk2Cnt]

private theorem pRank_le_of_model_twE6 {K : Type} [Group K] [Finite K] {lab : GLALabel} {p : ℕ}
    (htag : lab.tag = .twE6)
    (hM : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center K)) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  obtain ⟨-, hf1, -⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedChevalleyModel_of_lieModel hM
  have hn1 : 1 ≤ lab.n := hf1
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    have hle : p ≤ 4 := by omega
    interval_cases p
    · exact absurd rfl hp2
    · exact absurd rfl hp3
    · exact absurd hp (by norm_num)
  obtain ⟨F, _, _, σ, hcard, hσ, ⟨e3⟩⟩ := exists_twistedE6RootGroup_of_marked hM
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL TwistTag.E6.tag F) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup F σ) := Subtype.finite
  have heord : orderOf (((2 ^ lab.n : ℕ)) : ZMod p) = rk2Ord p lab.n := by
    rw [rk2Ord]
    push_cast
    rfl
  have hZeq : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
      CFSG.Open.pRank p (⊤ : Subgroup K) :=
    CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hpZ
  have hGeq : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e3
  have hKp : CFSG.Open.pRank p (⊤ : Subgroup K) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) := hZeq.symm.trans hGeq
  by_cases hmem : rk2Ord p lab.n ∈ [1, 2, 3, 4, 6, 8, 10, 12, 18]
  · have hb : CFSG.Open.pRank p (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) ≤
        rk2Mult lab (rk2Ord p lab.n) := by
      by_cases hm2 : rk2Ord p lab.n = 2
      · have he2 : orderOf (((2 ^ lab.n : ℕ)) : ZMod p) = 2 := heord.trans hm2
        by_cases hp5' : p = 5
        · subst hp5'
          have hq2 : ((((2 ^ lab.n : ℕ)) : ZMod 5)) ^ 2 = 1 := by
            have hpow := pow_orderOf_eq_one (((2 ^ lab.n : ℕ)) : ZMod 5)
            have hord : orderOf (((2 ^ lab.n : ℕ)) : ZMod 5) = 2 := by
              simpa using he2
            rwa [hord] at hpow
          have hF1 : orderOf ((Nat.card F : ℕ) : ZMod 5) = 1 := by
            rw [hcard, Nat.cast_pow]
            exact orderOf_eq_one_iff.2 hq2
          have hle : twistedE6RootGroup F σ ≤ adjointGroup Tag.E6 F :=
            (CFSG.LieType.Chevalley.graphFixedRootGroup_le (t := TwistTag.E6) (K := F)
              (σ := σ.toRingHom)).trans
              (CFSG.LieType.Chevalley.twistedFixedGroup_le_adjointGroup (t := TwistTag.E6)
                (K := F) (σ := σ.toRingHom))
          have hmono : CFSG.Open.pRank 5
              (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) ≤
              CFSG.Open.pRank 5 (⊤ : Subgroup (adjointGroup Tag.E6 F)) :=
            CFSG.SectionRank.pRank_top_le_of_injective (p := 5) (by norm_num)
              (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
          calc CFSG.Open.pRank 5 (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) ≤
                CFSG.Open.pRank 5 (⊤ : Subgroup (adjointGroup Tag.E6 F)) := hmono
            _ ≤ 6 := pRank_adjoint_E6_five_le_six hF1
            _ = rk2Mult lab (rk2Ord 5 lab.n) := by
                rw [hm2]
                simp [rk2Mult, htag, rk2Cnt]
        · have hp7 : 7 ≤ p := by
            have h2 := hp.two_le
            rcases Nat.lt_or_ge p 7 with hlt | hge
            · interval_cases p <;>
                first | exact absurd rfl hp2 | exact absurd rfl hp3 |
                  exact absurd rfl hp5' | exact absurd hp (by norm_num)
            · exact hge
          calc CFSG.Open.pRank p (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) ≤ 6 :=
                pRank_le_of_sylowTorusDatum
                  (CFSG.StandardType.ExcFrames.sylowTorus_twistedE6_two Nat.prime_two hn1 F hcard
                    σ hσ hp hp7 (not_dvd_of_orderOf_pos hp he2 (by norm_num)) he2) hp
            _ = rk2Mult lab (rk2Ord p lab.n) := by
                rw [hm2]
                simp [rk2Mult, htag, rk2Cnt]
      · have hm : rk2Ord p lab.n ∈ [1, 3, 4, 6, 8, 10, 12, 18] := by
          rcases List.mem_cons.1 hmem with h1 | hmem'
          · exact List.mem_cons.2 (Or.inl h1)
          · rcases List.mem_cons.1 hmem' with h2 | hmem''
            · exact absurd h2 hm2
            · exact List.mem_cons.2 (Or.inr hmem'')
        exact pRank_twisted_E6_le_of_mem htag Nat.prime_two hn1 hcard σ hσ hp hp5 hm heord
    exact hKp.trans_le hb
  · have h0 : degCountTw (rk2Ord p lab.n) = 0 := by
      by_contra hne
      exact hmem (mem_twE6_orders_of_degCountTw_pos (Nat.pos_of_ne_zero hne))
    have hpq : ¬ p ∣ 2 ^ lab.n :=
      not_dvd_of_orderOf_pos hp (by simpa using heord) (rk2Ord_pos hp hp2 lab.n).ne'
    have hzero : CFSG.Open.pRank p (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) = 0 := by
      refine le_antisymm ?_ (Nat.zero_le _)
      refine CFSG.SectionRank.pRank_le hp.one_lt ?_
      intro E _ hE
      rw [elemAbelian_card_eq_one_of_degCountTw_zero Nat.prime_two hn1 F hcard σ hσ hp
        (by omega) hpq heord h0 hE]
      simp
    calc CFSG.Open.pRank p (⊤ : Subgroup K)
        = CFSG.Open.pRank p (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) := hKp
      _ = 0 := hzero
      _ ≤ rk2Mult lab (rk2Ord p lab.n) := Nat.zero_le _

theorem rk2E6ThreeTwoFrontier :
    ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 2 ^ n → rk2Ord 3 n = 2 →
      CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup Tag.E6 K)) ≤ 4 := by
  intro K _ _ n hcard hm2
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hm2
    norm_num [rk2Ord] at hm2
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn hcard
  have h3 : 3 ∣ 2 ^ n + 1 := three_dvd_two_pow_add_one_of_rk2Ord_eq_two hm2
  have hmod : Nat.card K % 3 = 2 := by
    rw [hcard]
    exact mod_three_eq_two_of_dvd_add_one h3
  have hnot : ¬ 3 ∣ (CFSG.LieType.SeitzGeneration.ExcHighThree.e6FixedF4 K).index :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.not_dvd_three_index_e6FixedF4 K hmod
  calc CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup Tag.E6 K))
      ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup Tag.F4 K)) :=
        CFSG.SectionRank.pRank_top_le_of_mulEquiv_subgroup Nat.prime_three
          (CFSG.LieType.SeitzGeneration.ExcHighThree.e6FixedF4 K)
          (CFSG.LieType.SeitzGeneration.ExcHighThree.e6FixedF4Equiv K) hnot
    _ ≤ 4 := rk2_pRank_three_adjointF4_le K n hcard

theorem rk2TwE6ThreeOneFrontier :
    ∀ (K : Type) [Field K] [Finite K] (n : ℕ) (σ : K ≃+* K),
      Nat.card K = (2 ^ n) ^ 2 → (∀ c, σ c = c ^ (2 ^ n)) → rk2Ord 3 n = 1 →
        CFSG.Open.pRank 3 (⊤ : Subgroup (twistedE6RootGroup K σ)) ≤ 4 := by
  intro K _ _ n σ hcard hσ hm1
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hcard
    have := Finite.one_lt_card (α := K)
    omega
  haveI : CharP (GaloisField 2 n) 2 := inferInstance
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn
  have hq : ((2 : ZMod 3) ^ n) = 1 :=
    orderOf_eq_one_iff.1 (by simpa [rk2Ord] using hm1)
  have hq3 : (2 ^ n) % 3 = 1 := by
    have hcast : (((2 ^ n : ℕ)) : ZMod 3) = 1 := by
      rw [Nat.cast_pow]
      exact hq
    have h := (ZMod.natCast_eq_natCast_iff' (2 ^ n) 1 3).1 hcast
    simpa using h
  obtain ⟨H, ⟨eH⟩, hnotrel⟩ :=
    CFSG.HardMathSupport.Lang.AnisoE6.exists_f4_in_twistedE6
      (F := GaloisField 2 n) (K := K) (q := 2 ^ n) hF hcard σ hσ hq3
  have hnot : ¬ 3 ∣ H.index := by
    rwa [Subgroup.relIndex_top_right] at hnotrel
  calc CFSG.Open.pRank 3 (⊤ : Subgroup ↥(twistedE6RootGroup K σ))
      ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup Tag.F4 (GaloisField 2 n))) :=
        CFSG.SectionRank.pRank_top_le_of_mulEquiv_subgroup Nat.prime_three H eH hnot
    _ ≤ 4 := rk2_pRank_three_adjointF4_le (GaloisField 2 n) n hF

theorem rk2_pRank_le_E6 (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E6 ∨ lab.tag = .twE6)
    (hp : p.Prime) (hp2 : p ≠ 2) (hcov : Rk2E6Covered K lab p) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2 hQ
  rcases hcov with hp3 | ⟨hp3, hpZ3, hcases3⟩
  · rcases htag with hE6 | hTw
    · have hM6 : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 lab.n := by
        simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
          CFSG.StandardType.markRank, CFSG.StandardType.markChar,
          CFSG.StandardType.markDeg, hE6] using hM
      have hpZ : ¬ p ∣ Nat.card (Subgroup.center K) :=
        not_dvd_card_center_of_markedModel_E6 hQ' hM hE6 hp hp3
      exact pRank_le_of_model_E6 hE6 hM6 hp hp2 hp3 hpZ
    · have hMt : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n := by
        simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
          CFSG.StandardType.markRank, CFSG.StandardType.markChar,
          CFSG.StandardType.markDeg, hTw] using hM
      have hpZ : ¬ p ∣ Nat.card (Subgroup.center K) :=
        rk2_not_dvd_card_center_twE6 hQ' hM hTw hp hp2 hp3
      exact pRank_le_of_model_twE6 hTw hMt hp hp2 hp3 hpZ
  · subst hp3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases hcases3 with ⟨hE6, hm1⟩ | ⟨hTw, hm2⟩
    · have hM6 : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 lab.n := by
        simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
          CFSG.StandardType.markRank, CFSG.StandardType.markChar,
          CFSG.StandardType.markDeg, hE6] using hM
      have h3 : 3 ∣ 2 ^ lab.n - 1 := three_dvd_two_pow_sub_one_of_rk2Ord_eq_one hm1
      have hZeq : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
          CFSG.Open.pRank 3 (⊤ : Subgroup K) :=
        CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hpZ3
      calc CFSG.Open.pRank 3 (⊤ : Subgroup K)
          = CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) := hZeq.symm
        _ ≤ 6 := pRank_le_six_E6_of_three_dvd hM6 h3
        _ = rk2Mult lab (rk2Ord 3 lab.n) := by
            rw [hm1]
            simp [rk2Mult, hE6, rk2Cnt]
    · have hMt : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n := by
        simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
          CFSG.StandardType.markRank, CFSG.StandardType.markChar,
          CFSG.StandardType.markDeg, hTw] using hM
      have h3 : 3 ∣ 2 ^ lab.n + 1 := three_dvd_two_pow_add_one_of_rk2Ord_eq_two hm2
      have hZeq : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
          CFSG.Open.pRank 3 (⊤ : Subgroup K) :=
        CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hpZ3
      calc CFSG.Open.pRank 3 (⊤ : Subgroup K)
          = CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) := hZeq.symm
        _ ≤ 6 := pRank_le_six_twE6_of_three_dvd hMt h3
        _ = rk2Mult lab (rk2Ord 3 lab.n) := by
            rw [hm2]
            simp [rk2Mult, hTw, rk2Cnt]

theorem rk2_pRank_le_E6_of_frontier (h : Rk2E6Frontier) (K : Type) [Group K] [Finite K]
    (lab : GLALabel) (p : ℕ) (hK : Rk2IsLabel K lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6) (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  by_cases hcov : Rk2E6Covered K lab p
  · exact rk2_pRank_le_E6 K lab p hK htag hp hp2 hcov
  · have hp3 : p = 3 := by
      by_contra hne
      exact hcov (Or.inl hne)
    subst p
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨-, -, hM⟩ := rk2_model_of_isLabel hK
    by_cases hZ : 3 ∣ Nat.card (Subgroup.center K)
    · rcases htag with hE6 | hTw
      · exact h.coverE6 K lab 3 hK hE6 rfl hZ
      · exact h.coverTwE6 K lab 3 hK hTw rfl hZ
    · have hord := rk2Ord_three_eq_one_or_two lab.n
      rcases htag with hE6 | hTw
      · by_cases hm1 : rk2Ord 3 lab.n = 1
        · exfalso
          exact hcov (Or.inr ⟨rfl, hZ, Or.inl ⟨hE6, hm1⟩⟩)
        · have hm2 : rk2Ord 3 lab.n = 2 := by
            rcases hord with h' | h'
            · exact absurd h' hm1
            · exact h'
          have hM6 : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 lab.n := by
            simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
              CFSG.StandardType.markRank, CFSG.StandardType.markChar,
              CFSG.StandardType.markDeg, hE6] using hM
          obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := exists_adjointGroup_E6_of_marked hM6
          haveI : Finite (adjointGroup Tag.E6 F) := generated_group_finite Tag.E6 F
          have heord : orderOf ((Nat.card F : ℕ) : ZMod 3) = rk2Ord 3 lab.n := by
            have hcast : (((2 : ZMod 3)) ^ lab.n) = (((2 ^ lab.n : ℕ)) : ZMod 3) := by
              push_cast
              rfl
            rw [hcard, ← hcast, rk2Ord]
          have hZeq : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
              CFSG.Open.pRank 3 (⊤ : Subgroup K) :=
            CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ
          have hGeq : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
              CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup Tag.E6 F)) :=
            CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
          have hKp : CFSG.Open.pRank 3 (⊤ : Subgroup K) =
              CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup Tag.E6 F)) :=
            hZeq.symm.trans hGeq
          calc CFSG.Open.pRank 3 (⊤ : Subgroup K)
              = CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup Tag.E6 F)) := hKp
            _ ≤ 4 := rk2E6ThreeTwoFrontier F lab.n hcard hm2
            _ = rk2Mult lab (rk2Ord 3 lab.n) := by
                rw [hm2]
                simp [rk2Mult, hE6, rk2Cnt]
      · by_cases hm2 : rk2Ord 3 lab.n = 2
        · exfalso
          exact hcov (Or.inr ⟨rfl, hZ, Or.inr ⟨hTw, hm2⟩⟩)
        · have hm1 : rk2Ord 3 lab.n = 1 := by
            rcases hord with h' | h'
            · exact h'
            · exact absurd h' hm2
          have hMt : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 lab.n := by
            simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
              CFSG.StandardType.markRank, CFSG.StandardType.markChar,
              CFSG.StandardType.markDeg, hTw] using hM
          obtain ⟨F, _, _, σ, hcard, hσ, ⟨e3⟩⟩ := exists_twistedE6RootGroup_of_marked hMt
          haveI : Finite (ModGL TwistTag.E6.tag F) := finite_modGL
          haveI : Finite ↥(twistedE6RootGroup F σ) := Subtype.finite
          have heord : orderOf (((2 ^ lab.n : ℕ)) : ZMod 3) = rk2Ord 3 lab.n := by
            rw [rk2Ord]
            push_cast
            rfl
          have hZeq : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
              CFSG.Open.pRank 3 (⊤ : Subgroup K) :=
            CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ
          have hGeq : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) =
              CFSG.Open.pRank 3 (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) :=
            CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e3
          have hKp : CFSG.Open.pRank 3 (⊤ : Subgroup K) =
              CFSG.Open.pRank 3 (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) :=
            hZeq.symm.trans hGeq
          calc CFSG.Open.pRank 3 (⊤ : Subgroup K)
              = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(twistedE6RootGroup F σ)) := hKp
            _ ≤ 4 := rk2TwE6ThreeOneFrontier F lab.n σ hcard hσ hm1
            _ = rk2Mult lab (rk2Ord 3 lab.n) := by
                rw [hm1]
                simp [rk2Mult, hTw, rk2Cnt]

