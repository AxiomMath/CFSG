module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.NormalizerEscape
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.StrongRestrict
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.StrongThreeSolv
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairTRFrontier

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

theorem three_dvd_card_of_two_le_pRank {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (h : 2 ≤ Open.pRank 3 X) : 3 ∣ Nat.card X := by
  set S := {k | ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} with hS
  have hne : S.Nonempty := by
    refine ⟨0, ⊥, bot_le, ?_, by simp⟩
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have ha : (a : G) = 1 := Subgroup.mem_bot.mp a.2
      have hb : (b : G) = 1 := Subgroup.mem_bot.mp b.2
      exact Subtype.ext (by simp [ha, hb])
    · rw [Subgroup.mem_bot] at hx
      simp [hx]
  have hbdd : BddAbove S := by
    refine ⟨Nat.card X, ?_⟩
    rintro k ⟨E, hE, -, hcard⟩
    have h1 : 3 ^ k ≤ Nat.card X := by
      rw [← hcard]
      exact Subgroup.card_le_of_le hE
    exact ((Nat.lt_pow_self (by norm_num : 1 < 3)).trans_le h1).le
  obtain ⟨E, hEX, -, hEcard⟩ := Nat.sSup_mem hne hbdd
  have hsup : sSup S ≠ 0 := by
    have : Open.pRank 3 X = sSup S := rfl
    omega
  have h3 : 3 ∣ Nat.card E := by
    rw [hEcard]
    exact dvd_pow_self 3 hsup
  exact h3.trans (Subgroup.card_dvd_of_le hEX)

theorem normalizer_ne_top_of_twoGroup {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {C : Subgroup G} (hC : C ≠ ⊥) (hC2 : IsPGroup 2 C) :
    Subgroup.normalizer (C : Set G) ≠ ⊤ := by
  intro htop
  have hnormal : C.Normal := ⟨fun n hn g => by
    have hg : g ∈ Subgroup.normalizer (C : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn⟩
  have := hs
  have hCtop : C = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal C).resolve_left hC
  have hG2 : IsPGroup 2 G := by
    have h := hC2
    rw [hCtop] at h
    exact h.of_equiv Subgroup.topEquiv
  have : Nontrivial G := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨⟨a, b, fun h => hab (h ▸ rfl)⟩⟩
  have hZ : Nontrivial (Subgroup.center G) := IsPGroup.center_nontrivial hG2
  have hZtop : Subgroup.center G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exfalso
      obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center G)
      have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
        rw [← h]
        exact z.2
      have hz1 : (z : G) = 1 := Subgroup.mem_bot.mp hzbot
      exact hz (Subtype.ext (by simpa using hz1))
    · exact h
  obtain ⟨a, b, hab⟩ := hnonab
  have ha : a ∈ Subgroup.center G := hZtop ▸ Subgroup.mem_top a
  exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem PairStrongCtx.normalizer_char_facts {G : Type} [Group G] [Finite G]
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R)
    (hK : KFactStrongThreeSolv) {T C : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTM : ¬ Subgroup.normalizer (T : Set G) ≤ M) (hC : C ≠ ⊥) (hCT : C ≤ T)
    (hNC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G)) :
    Open.pRank 3 (Subgroup.normalizer (C : Set G) ⊓ M) ≤ 2 ∧
    (2 ≤ Open.pRank 3 (Subgroup.normalizer (C : Set G) ⊓ M) →
      D2PerfectThreePrime (Subgroup.normalizer (C : Set G)) M) := by
  have hC2 : IsPGroup 2 C := by
    intro g
    obtain ⟨k, hk⟩ := hT2 ⟨(g : G), hCT g.2⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hNCM : ¬ Subgroup.normalizer (C : Set G) ≤ M := fun hle => hTM (hNC.trans hle)
  refine ⟨D2Escape.pRank_normalizer_inf_le_two hctx.esc hctx.d1 hctx.beta hC hC2 hNCM,
    fun h2 => ?_⟩
  have hNtop : Subgroup.normalizer (C : Set G) ≠ ⊤ :=
    normalizer_ne_top_of_twoGroup hctx.glob.simple hctx.glob.nonab hC hC2
  have hp : 3 ∣ Nat.card (Subgroup.normalizer (C : Set G) ⊓ M : Subgroup G) :=
    three_dvd_card_of_two_le_pRank h2
  have hstr := glbStronglyEmbedded_subgroupOf_inf hctx.strong hNCM hp
  exact d2PerfectThreePrime_of_strongly hK hctx.glob.kProper hNtop hstr h2

theorem PairStrongCtx.exists_twoGroup_of_evenIndex {G : Type} [Group G] [Finite G]
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R)
    (hev : PairEvenIndex M H) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ pCoreOf 2 M ≤ T ∧
      ¬ Subgroup.normalizer (T : Set G) ≤ M ∧ IsSylowTwoOf T (H ⊓ M) :=
  hctx.pair.exists_twoGroup_of_evenIndex hev

end CFSG.AGLEmbeddingD2.McLaughlin
