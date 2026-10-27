module

public import CFSG.Assembly.LargeEvenGLABridge
import CFSG.Milestones.LC_GL_local_rank_bounds
public import CFSG.Assembly.OpenBridges

public section

namespace CFSG.Assembly.LargeEven

theorem glaBeta_subset_of_le {G : Type*} [Group G] [Finite G] {k m : ℕ} (h : k ≤ m) :
    CFSG.Open.GLABeta m G ⊆ CFSG.Open.GLABeta k G :=
  fun _ hp => ⟨hp.1, hp.2.1, hp.2.2.1, h.trans hp.2.2.2⟩

theorem glaTwoLocalRank_le_evenRank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.GLATwoLocalRank p G ≤ CFSG.Open.evenRank G :=
  ((CFSG.Milestones.lc_gl_local_rank_bounds G).1 p hp hp2).2

theorem pretrichotomy_rank_reduction_of_theorem_b
    (hB : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G →
        4 ≤ CFSG.Open.evenRank G → ∀ m : ℕ, 4 ≤ m →
          (∀ q ∈ CFSG.Open.GLABeta (m + 1) G, CFSG.Open.GLAWeakCoreLocal G q) →
            ∀ p ∈ CFSG.Open.GLABeta m G,
              CFSG.Open.GLAWeakCoreLocal G p ∨ CFSG.Open.GLADeltaZero G p)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Open.IsKProper G)
    (hchar : CFSG.Open.IsCharTwoType G) (he : 4 ≤ CFSG.Open.evenRank G) :
    (∀ p ∈ CFSG.Open.GLABeta 4 G, CFSG.Open.GLAWeakCoreLocal G p) ∨
      ∃ m : ℕ, 4 ≤ m ∧ m ≤ CFSG.Open.evenRank G ∧ ∃ p ∈ CFSG.Open.GLABeta m G,
        (∀ q ∈ CFSG.Open.GLABeta (m + 1) G, CFSG.Open.GLAWeakCoreLocal G q) ∧
        (∀ q ∈ CFSG.Open.GLABeta m G,
          CFSG.Open.GLAWeakCoreLocal G q ∨ CFSG.Open.GLADeltaZero G q) ∧
        CFSG.Open.GLATwoLocalRank p G = m ∧ CFSG.Open.GLADeltaZero G p ∧
          ¬ CFSG.Open.GLAWeakCoreLocal G p := by
  classical
  by_cases hall : ∀ p ∈ CFSG.Open.GLABeta 4 G, CFSG.Open.GLAWeakCoreLocal G p
  · exact Or.inl hall
  refine Or.inr ?_
  obtain ⟨p₀, hp₀, hp₀w⟩ := not_forall₂.mp hall
  have hbound (p : ℕ) (hp : p ∈ CFSG.Open.GLABeta 4 G) :
      CFSG.Open.GLATwoLocalRank p G ≤ CFSG.Open.evenRank G :=
    glaTwoLocalRank_le_evenRank hp.1 hp.2.1
  let P : ℕ → Prop := fun k => ∃ p ∈ CFSG.Open.GLABeta 4 G, ¬ CFSG.Open.GLAWeakCoreLocal G p ∧
    CFSG.Open.GLATwoLocalRank p G = k
  obtain ⟨m, ⟨p, hp, hpw, hpm⟩, hmax⟩ : ∃ m : ℕ, P m ∧
      ∀ p ∈ CFSG.Open.GLABeta 4 G, ¬ CFSG.Open.GLAWeakCoreLocal G p →
        CFSG.Open.GLATwoLocalRank p G ≤ m :=
    ⟨Nat.findGreatest P (CFSG.Open.evenRank G),
      Nat.findGreatest_spec (P := P) (hbound p₀ hp₀) ⟨p₀, hp₀, hp₀w, rfl⟩,
      fun p hp hpw => Nat.le_findGreatest (P := P) (hbound p hp) ⟨p, hp, hpw, rfl⟩⟩
  have h4m : 4 ≤ m := hp.2.2.2.trans_eq hpm
  have ha (q : ℕ) (hq : q ∈ CFSG.Open.GLABeta (m + 1) G) : CFSG.Open.GLAWeakCoreLocal G q := by
    by_contra hqw
    have hle := hmax q (glaBeta_subset_of_le (by omega) hq) hqw
    have hgt := hq.2.2.2
    omega
  have hb := hB G hnonab hK hchar he m h4m ha
  have hpm' : p ∈ CFSG.Open.GLABeta m G := ⟨hp.1, hp.2.1, hp.2.2.1, hpm.ge⟩
  exact ⟨m, h4m, hpm ▸ hbound p hp, p, hpm', ha, hb, hpm, (hb p hpm').resolve_left hpw, hpw⟩

theorem constructed_pretrichotomy_rank_four_of_theorem_a_of_theorem_b
    (hA : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G →
        4 ≤ CFSG.Open.evenRank G → ∀ m : ℕ, 4 ≤ m →
          (∀ q ∈ CFSG.Open.GLABeta (m + 1) G, CFSG.Open.GLAWeakCoreLocal G q) →
          (∀ q ∈ CFSG.Open.GLABeta m G,
            CFSG.Open.GLAWeakCoreLocal G q ∨ CFSG.Open.GLADeltaZero G q) →
          (∃ q ∈ CFSG.Open.GLABeta m G,
            CFSG.Open.GLATwoLocalRank q G = m ∧ CFSG.Open.GLADeltaZero G q) →
          ∃ p ∈ CFSG.Open.GLABeta m G, CFSG.Open.GLATwoLocalRank p G = m ∧
            CFSG.Open.GLADeltaZero G p ∧
            ((p = 3 ∧ CFSG.Open.GLAGF2Type G) ∨
              ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
                CFSG.Open.GLASStar p B x L ∧ CFSG.Open.GLAStandardType p B x L))
    (hB : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G →
        4 ≤ CFSG.Open.evenRank G → ∀ m : ℕ, 4 ≤ m →
          (∀ q ∈ CFSG.Open.GLABeta (m + 1) G, CFSG.Open.GLAWeakCoreLocal G q) →
            ∀ p ∈ CFSG.Open.GLABeta m G,
              CFSG.Open.GLAWeakCoreLocal G p ∨ CFSG.Open.GLADeltaZero G p)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) :
    (∀ p ∈ LargeEvenBeta 4 G, LargeEvenWeakCoreLocal G p) ∨ LargeEvenGF2Type G ∨
      ∃ p ∈ LargeEvenBeta 4 G, ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
        LargeEvenSStar p B x L ∧ LargeEvenStandardType p B x L := by
  have hK' := (kProper_inCatalog_iff_isKProper G).1 hK
  have hchar' := (isCharTwoType_iff_open G).1 hchar
  have he' : 4 ≤ CFSG.Open.evenRank G := he.trans_eq (evenRank_eq_open G)
  rcases pretrichotomy_rank_reduction_of_theorem_b hB G hnonab hK' hchar' he' with
    hI | ⟨m, hm, -, p, hp, ha, hb, hrank, hdelta, -⟩
  · refine Or.inl fun p hp => (largeEvenWeakCoreLocal_iff_glaWeakCoreLocal G p).2 (hI p ?_)
    rwa [largeEvenBeta_eq_glaBeta] at hp
  obtain ⟨p', hp', -, -, ⟨-, hgf2⟩ | ⟨B, x, L, hS, hst⟩⟩ :=
    hA G hnonab hK' hchar' he' m hm ha hb ⟨p, hp, hrank, hdelta⟩
  · exact Or.inr (Or.inl ((largeEvenGF2Type_iff_glaGF2Type G).2 hgf2))
  · refine Or.inr (Or.inr ⟨p', ?_, B, x, L, (largeEvenSStar_iff_glaSStar p' B x L).2 hS,
      (largeEvenStandardType_iff_glaStandardType p' B x L).2 hst⟩)
    rw [largeEvenBeta_eq_glaBeta]
    exact glaBeta_subset_of_le hm hp'

end CFSG.Assembly.LargeEven
