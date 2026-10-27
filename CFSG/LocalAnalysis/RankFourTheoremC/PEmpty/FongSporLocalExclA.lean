module

public import CFSG.Sporadic.Bridge.J1
public import CFSG.Sporadic.J1
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1
public import CFSG.Sporadic.Bridge.Co1Surj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open Subgroup

theorem false_of_J1 {A : Type} [Group A] [Finite A] (L : Subgroup A)
    (hL : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .J1).Group))
    (h2 : 2 ≤ CFSG.Open.pRank 3 L) : False := by
  obtain ⟨e⟩ := hL
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have hLc : Nat.card ↥L = 175560 := by
    rw [Nat.card_congr (e.trans f.symm).toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  obtain ⟨E, hEL, -, hEc⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained 3 L (by omega)
  have hdvd : Nat.card E ∣ Nat.card L := Subgroup.card_dvd_of_le hEL
  rw [hEc, hLc] at hdvd
  have h9 : 3 ^ 2 ∣ 3 ^ CFSG.Open.pRank 3 L := pow_dvd_pow 3 h2
  have := h9.trans hdvd
  norm_num at this

theorem false_of_localRank_four {A : Type} [Group A] [Finite A] (L : Subgroup A)
    (h4 : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 ↥L)
    (hloc : ∀ U : Subgroup A, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank 3 (normalizer (U : Set A) ⊓ L) ≤ 3) : False := by
  have h4' : 4 ≤ sSup {k : ℕ | ∃ H : Subgroup ↥L, CFSG.Open.IsTwoLocal H ∧
      CFSG.Open.pRank 3 H = k} := h4
  have hpos : 0 < sSup {k : ℕ | ∃ H : Subgroup ↥L, CFSG.Open.IsTwoLocal H ∧
      CFSG.Open.pRank 3 H = k} := lt_of_lt_of_le (by norm_num) h4'
  obtain ⟨H, hHloc, hHk⟩ := CFSG.RankThreeCoreUniqueness.Helpers.nat_sSup_mem_of_pos _ hpos
  have hH4 : 4 ≤ CFSG.Open.pRank 3 H := by rw [hHk]; exact h4'
  obtain ⟨P, hP0, hPp, rfl⟩ := hHloc
  have hPL : P.map L.subtype ≤ L := Subgroup.map_subtype_le P
  have hU0 : P.map L.subtype ≠ ⊥ := fun hbot =>
    hP0 ((Subgroup.map_eq_bot_iff_of_injective P L.subtype_injective).mp hbot)
  have hUp : IsPGroup 2 (P.map L.subtype) := hPp.map L.subtype
  have hbound := hloc (P.map L.subtype) hPL hU0 hUp
  have hPsub : (P.map L.subtype).subgroupOf L = P :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective P
  have hsub : (normalizer ((P.map L.subtype : Subgroup A) : Set A)).subgroupOf L =
      normalizer (P : Set ↥L) := by
    rw [Subgroup.subgroupOf_normalizer_eq hPL, hPsub]
  have hmapN : (normalizer (P : Set ↥L)).map L.subtype ≤
      normalizer ((P.map L.subtype : Subgroup A) : Set A) ⊓ L := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, x.2⟩
    have hx' : x ∈ (normalizer ((P.map L.subtype : Subgroup A) : Set A)).subgroupOf L := by
      rw [hsub]; exact hx
    exact Subgroup.mem_subgroupOf.mp hx'
  have hle1 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
    Nat.prime_three L.subtype L.subtype_injective (normalizer (P : Set ↥L))
  have hle2 := CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) hmapN
  have hfin := hH4.trans (hle1.trans (hle2.trans hbound))
  omega

theorem false_of_Co1
    {A : Type} [Group A] [Finite A]
    (L : Subgroup A)
    (hL : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group))
    (hloc : ∀ U : Subgroup A, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank 3 (normalizer (U : Set A) ⊓ L) ≤ 3) : False := by
  obtain ⟨e⟩ := hL
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  have hg : ↥L ≃* CFSG.Blueprint.NativeSporadic.Co1 := e.trans f.symm
  haveI : Finite CFSG.Blueprint.NativeSporadic.Co1 := Finite.of_equiv ↥L hg.toEquiv
  have hT : CFSG.Assembly.RankThreeEven.localRank 3 ↥L =
      CFSG.Assembly.RankThreeEven.localRank 3 CFSG.Blueprint.NativeSporadic.Co1 :=
    @CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv ↥L CFSG.Blueprint.NativeSporadic.Co1
      (inferInstance) (inferInstance) (inferInstance) (inferInstance) hg 3 Nat.prime_three
  have h4c : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 CFSG.Blueprint.NativeSporadic.Co1 :=
    CFSG.RankThree.PartTwo.Census.four_le_localRank_three_Co1
  have h4 : 4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 ↥L := by
    rw [hT]
    exact h4c
  exact false_of_localRank_four L h4 hloc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
