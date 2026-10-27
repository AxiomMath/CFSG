module

public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.Level
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I112CtxExt
public import CFSG.LocalAnalysis.GLTheoremA.PartI.ExcBridge
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Timmesfeld.Tables.Census

section I113Rank

variable {G : Type} [Group G] [Finite G]

private theorem i113_card_le_three_of_isL2 {L : Subgroup G} (hL2 : IsLTwoOddPow (barOf 3 L))
    {W : Subgroup G} (hWL : W ≤ L) (hW : IsElemAbelian 3 W) : Nat.card W ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL2' : IsL2TwoPowOdd (barOf 3 L) := isL2TwoPowOdd_of_isLTwoOddPow hL2
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hW
  have hWsub : Nat.card ↥(W.subgroupOf L) = 3 ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv, hk]
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥L)) := CFSG.pPrimeCore_coprime_card
  have hdisj : Disjoint (W.subgroupOf L) (GLAPPrimeCore 3 ↥L) := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hWsub]
    exact Nat.Coprime.pow_left k hcop
  let f : ↥L →* barOf 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)
  let g : ↥W →* barOf 3 L := f.comp (Subgroup.inclusion hWL)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hmem : (Subgroup.inclusion hWL w : ↥L) ∈ GLAPPrimeCore 3 ↥L :=
      (QuotientGroup.eq_one_iff _).1 hw
    have hmemW : (Subgroup.inclusion hWL w : ↥L) ∈ W.subgroupOf L :=
      Subgroup.mem_subgroupOf.2 w.2
    have hinf : W.subgroupOf L ⊓ GLAPPrimeCore 3 ↥L = ⊥ := disjoint_iff.1 hdisj
    have h1 : (Subgroup.inclusion hWL w : ↥L) = 1 := by
      have hmem' : (Subgroup.inclusion hWL w : ↥L) ∈ W.subgroupOf L ⊓ GLAPPrimeCore 3 ↥L := ⟨hmemW, hmem⟩
      rw [hinf] at hmem'
      exact Subgroup.mem_bot.1 hmem'
    exact Subtype.ext (by simpa using congrArg Subtype.val h1)
  have hpR : CFSG.Open.pRank 3 (⊤ : Subgroup (barOf 3 L)) ≤ 1 :=
    pRank_three_le_one_of_isL2TwoPowOdd hL2'
  have hcomm : ∀ a b : ↥W, a * b = b * a := fun a b => Subtype.ext (isElemAbelian_commute hW a.2 b.2)
  have hpow : ∀ a : ↥W, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hW.2 a a.2)
  have hk1 : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (barOf 3 L)) :=
    CFSG.SectionRank.le_pRank_of_injective (by norm_num) hcomm hpow hk g hg le_top
  calc Nat.card W = 3 ^ k := hk
    _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (hk1.trans hpR)
    _ = 3 := by norm_num

private theorem i113_card_le_nine_of_max {L : Subgroup G}
    (hmax : ∀ R : Subgroup G, R ≤ L → IsPGroup 3 ↥R →
      (∀ S : Subgroup G, S ≤ L → IsPGroup 3 ↥S → R ≤ S → S = R) → IsThreeOnePlusTwo R)
    {W : Subgroup G} (hWL : W ≤ L) (hW : IsElemAbelian 3 W) : Nat.card W ≤ 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW3 : IsPGroup 3 ↥W := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hW.2 g.1 g.2)⟩
  obtain ⟨S, hSmem, hSmax⟩ := Set.Finite.exists_maximal
    (s := {S : Subgroup G | S ≤ L ∧ IsPGroup 3 ↥S ∧ W ≤ S}) (Set.toFinite _) ⟨W, hWL, hW3, le_rfl⟩
  obtain ⟨hSL, hS3, hWS⟩ := hSmem
  have hmaxS : ∀ S' : Subgroup G, S' ≤ L → IsPGroup 3 ↥S' → S ≤ S' → S' = S := fun S' h1 h2 h3 =>
    le_antisymm (hSmax ⟨h1, h2, hWS.trans h3⟩ h3) h3
  obtain ⟨⟨r, hr, s, hs, hrs⟩, hcard, -⟩ := hmax S hSL hS3 hmaxS
  have hdvd : Nat.card W ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le hWS
    rw [hcard] at this
    exact this
  obtain ⟨i, hi, hWi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  by_contra hgt
  have hi3 : i = 3 := by
    by_contra hne
    have : i ≤ 2 := by omega
    have : Nat.card W ≤ 3 ^ 2 := by
      rw [hWi]
      exact Nat.pow_le_pow_right (by norm_num) this
    exact hgt this
  have hWS' : W = S := Subgroup.eq_of_le_of_card_ge hWS (by rw [hcard, hWi, hi3]; norm_num)
  have hr' : r ∈ W := by rw [hWS']; exact hr
  have hs' : s ∈ W := by rw [hWS']; exact hs
  exact hrs (isElemAbelian_commute hW hr' hs')

private theorem i113_card_le_nine {L : Subgroup G}
    (hcase : IsLTwoOddPow (barOf 3 L) ∨
      (∀ R : Subgroup G, R ≤ L → IsPGroup 3 ↥R →
        (∀ S : Subgroup G, S ≤ L → IsPGroup 3 ↥S → R ≤ S → S = R) → IsThreeOnePlusTwo R))
    {W : Subgroup G} (hWL : W ≤ L) (hW : IsElemAbelian 3 W) : Nat.card W ≤ 3 ^ 2 := by
  rcases hcase with h | h
  · exact (i113_card_le_three_of_isL2 h hWL hW).trans (by norm_num)
  · exact i113_card_le_nine_of_max h hWL hW

end I113Rank

section LevelU38



private theorem k2_three_of_isU3eight (i : TauCeti.CFSGIndex) (h : S9.isU3eight i) : k2 3 i := by
  cases i with
  | cyclic p hp => simp [S9.isU3eight, onLie] at h
  | alternating n hn => simp [S9.isU3eight, onLie] at h
  | sporadic s => simp [S9.isU3eight, onLie] at h
  | lie j =>
    obtain ⟨d, hv⟩ := j
    simp only [S9.isU3eight, onLie] at h
    split at h
    · rename_i q
      have hdvd : q.p ∣ q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact dvd_pow_self q.p q.exponent_pos.ne'
      rw [h] at hdvd
      have hp2 : q.p = 2 :=
        (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
          (q.prime_p.dvd_of_dvd_pow (n := 3) (by norm_num; exact hdvd))
      have hc : q.p ^ q.exponent = 8 := (TauCeti.PrimePower.card_def q).symm.trans h
      have hpow : 2 ^ q.exponent = 2 ^ 3 := by
        rw [hp2] at hc
        rw [hc]
        norm_num
      have he : q.exponent = 3 := Nat.pow_right_injective (le_refl 2) hpow
      show 3 = 3 ∧ q.p = 2 ∧ Odd q.exponent ∧ 1 < q.exponent
      exact ⟨rfl, hp2, by rw [he]; decide, by rw [he]; norm_num⟩
    · exact absurd h id

theorem levelU38At_holds (G : Type) [Group G] [Finite G] : LevelU38At G := by
  intro X L hL hU
  have hM : ListedMultiplierBound 3 :=
    listedMultiplierBound_of_tables CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      sporadicMultiplierTable_holds 3
  have hH : HatOddMultiplierBound := hatOddMultiplierBound_of_tables sporadicMultiplierTable_holds
  rw [fullCoverLevel_pQuot_eq hM hH Nat.prime_three (by norm_num) hL]
  have hk2 : catalogIs (PSimple 3 L) (k2 3) := S10.catalogIs_imp k2_three_of_isU3eight hU
  unfold kLevel
  by_cases h1 : IsChevSimple 3 (PSimple 3 L)
  · rw [if_pos h1] <;> norm_num
  · rw [if_neg h1, if_pos hk2] <;> norm_num

end LevelU38

section I112Inputs



theorem i113NormAt_holds
    (G : Type) [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hKP : CFSG.Open.IsKProper G) : I113NormAt G := by
  intro X B L _hXK hBX hB hr0 _hU hL hE
  obtain ⟨E, hEL, hE', hE3⟩ := hE
  by_contra hnL
  have hr : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B :=
    CFSG.AGLEmbedding.le_pRank_of_pow_le_card Nat.prime_three le_rfl hB hr0
  obtain ⟨-, -, -, -, hcase⟩ := i112c_ext
    CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds tableL2_unconditional
    tables112Types_holds tables112More_holds hsimple hKP Nat.prime_three (by norm_num) hB hBX hr hL hnL
  have hcase' : IsLTwoOddPow (barOf 3 L) ∨
      (∀ R : Subgroup G, R ≤ L → IsPGroup 3 ↥R →
        (∀ S : Subgroup G, S ≤ L → IsPGroup 3 ↥S → R ≤ S → S = R) → IsThreeOnePlusTwo R) := by
    rcases hcase with h | ⟨-, -, hR⟩
    · exact Or.inl h
    · exact Or.inr fun R h1 h2 h3 => (hR R h1 h2 h3).1
  have hle := i113_card_le_nine hcase' hEL hE'
  rw [hE3] at hle
  norm_num at hle

theorem i112OneAt_holds
    (G : Type) [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hKP : CFSG.Open.IsKProper G) : I112OneAt G := by
  intro p hp hp2 X L B _hXK hL hB hBX hr0 hnL
  have hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B :=
    CFSG.AGLEmbedding.le_pRank_of_pow_le_card hp le_rfl hB hr0
  obtain ⟨-, h3, hrel, -, -, -⟩ := i112c_full
    CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds tableL2_unconditional
    tables112Types_holds hsimple hKP hp hp2 hB hBX hr hL hnL
  refine ⟨h3, ?_⟩
  have hm := Subgroup.relIndex_mul_card (Subgroup.normalizer (L : Set G)) B
  rw [hrel, inf_comm] at hm
  exact hm.symm

end I112Inputs

end CFSG.LocalAnalysis.GLTheoremA
