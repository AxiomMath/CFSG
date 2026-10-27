module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2E6Seven
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma47
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.KRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def i165TorusRank (lab : GLALabel) : ℕ :=
  match lab.tag with
  | .B | .C | .D => lab.rank
  | .F4 => 4
  | .E7 => 7
  | .E8 => 8
  | _ => 0

@[expose] def I165TorusRankLower : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ), Rk2IsLabel K lab →
    p.Prime → p ≠ 2 → ¬ p ∣ Nat.card (Subgroup.center K) → p ∣ 2 ^ lab.n + 1 →
    2 ≤ lab.n →
    (lab.tag = .B ∨ lab.tag = .C ∨ (lab.tag = .D ∧ Even lab.rank) ∨
      lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) →
    i165TorusRank lab ≤ CFSG.Open.pRank p (⊤ : Subgroup K)

theorem i165_false_of_split {K : Type} [Group K] {lab : GLALabel} {p : ℕ}
    (hK : HasLabel K (fun l : GLALabel => l = lab))
    (hns : ∀ lab' : GLALabel, HasLabel K (fun l : GLALabel => l = lab') → ¬ GLASplit16 p lab')
    (hs : GLASplit16 p lab) : False :=
  hns lab hK hs

theorem i165_false_of_rank_le_pRank {K : Type} [Group K] [Finite K] {p B : ℕ} {A : Subgroup K}
    (hp : p.Prime) (hlow : B ≤ CFSG.Open.pRank p (⊤ : Subgroup K))
    (hup : CFSG.Open.evenRank K ≤ B)
    (hA : 3 ≤ CFSG.Open.pRank p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A)
    (he : CFSG.Open.pRank p A + 1 ≤ CFSG.Open.evenRank K) : False := by
  have hmono : CFSG.Open.pRank p A ≤ CFSG.Open.pRank p (⊤ : Subgroup K) :=
    CFSG.SectionRank.pRank_mono hp.one_lt le_top
  omega

theorem rk2Mult_A_le_two {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm1 : rk2Ord p n ≠ 1) (h : ¬ 3 * rk2Ord p n ≤ l + 1) :
    rk2Mult ⟨.A, l, n⟩ (rk2Ord p n) ≤ 2 := by
  have hmpos := rk2Ord_pos hp hp2 n
  have hcalc : rk2Mult ⟨.A, l, n⟩ (rk2Ord p n) = (l + 1) / rk2Ord p n := by
    simp only [rk2Mult]
    rw [if_neg hm1]
  rw [hcalc]
  have hlt : (l + 1) / rk2Ord p n < 3 := by
    rw [Nat.div_lt_iff_lt_mul hmpos]
    omega
  omega

theorem rk2Mult_E6_le_two {n p : ℕ} (h1 : rk2Ord p n ≠ 1) (h2 : rk2Ord p n ≠ 2)
    (h3 : rk2Ord p n ≠ 3) : rk2Mult ⟨.E6, 0, n⟩ (rk2Ord p n) ≤ 2 := by
  have hc : rk2Mult ⟨.E6, 0, n⟩ (rk2Ord p n) =
      rk2Cnt [(2, true), (5, true), (6, true), (8, true), (9, true), (12, true)]
        (rk2Ord p n) := by
    simp [rk2Mult]
  rw [hc]
  by_contra hle
  push Not at hle
  rcases rk2_E6_ge3 hle with h | h | h <;> omega

theorem rk2Mult_E7_le_two {n p : ℕ} (h1 : rk2Ord p n ≠ 1) (h2 : rk2Ord p n ≠ 2)
    (h3 : rk2Ord p n ≠ 3) (h6 : rk2Ord p n ≠ 6) :
    rk2Mult ⟨.E7, 0, n⟩ (rk2Ord p n) ≤ 2 := by
  have hc : rk2Mult ⟨.E7, 0, n⟩ (rk2Ord p n) =
      rk2Cnt [(2, true), (6, true), (8, true), (10, true), (12, true), (14, true), (18, true)]
        (rk2Ord p n) := by
    simp [rk2Mult]
  rw [hc]
  by_contra hle
  push Not at hle
  rcases rk2_E7_ge3 hle with h | h | h | h <;> omega

theorem rk2Mult_E8_le_two {n p : ℕ} (h1 : rk2Ord p n ≠ 1) (h2 : rk2Ord p n ≠ 2)
    (h3 : rk2Ord p n ≠ 3) (h4 : rk2Ord p n ≠ 4) (h6 : rk2Ord p n ≠ 6) :
    rk2Mult ⟨.E8, 0, n⟩ (rk2Ord p n) ≤ 2 := by
  have hc : rk2Mult ⟨.E8, 0, n⟩ (rk2Ord p n) =
      rk2Cnt [(2, true), (8, true), (12, true), (14, true), (18, true), (20, true), (24, true),
        (30, true)] (rk2Ord p n) := by
    simp [rk2Mult]
  rw [hc]
  by_contra hle
  push Not at hle
  rcases rk2_E8_ge3 hle with h | h | h | h | h <;> omega

theorem rk2Mult_F4_le_two {n p : ℕ} (h1 : rk2Ord p n ≠ 1) (h2 : rk2Ord p n ≠ 2) :
    rk2Mult ⟨.F4, 0, n⟩ (rk2Ord p n) ≤ 2 := by
  have hc : rk2Mult ⟨.F4, 0, n⟩ (rk2Ord p n) =
      rk2Cnt [(2, true), (6, true), (8, true), (12, true)] (rk2Ord p n) := by
    simp [rk2Mult]
  rw [hc]
  by_contra hle
  push Not at hle
  rcases rk2_F4_ge3 hle with h | h <;> omega

theorem rk2Mult_twE6_le_two {n p : ℕ} (h1 : rk2Ord p n ≠ 1) (h2 : rk2Ord p n ≠ 2)
    (h6 : rk2Ord p n ≠ 6) : rk2Mult ⟨.twE6, 0, n⟩ (rk2Ord p n) ≤ 2 := by
  have hc : rk2Mult ⟨.twE6, 0, n⟩ (rk2Ord p n) =
      rk2Cnt [(2, true), (5, false), (6, true), (8, true), (9, false), (12, true)]
        (rk2Ord p n) := by
    simp [rk2Mult]
  rw [hc]
  by_contra hle
  push Not at hle
  rcases rk2_twE6_ge3 hle with h | h | h <;> omega

theorem rk2Mult_D_three_two {n : ℕ} : rk2Mult ⟨.D, 3, n⟩ 2 ≤ 2 := by
  norm_num [rk2Mult]


theorem i165_false_of_rk2Mult_le_two {K : Type} [Group K] [Finite K] {lab : GLALabel} {p : ℕ}
    {A : Subgroup K} (hK : Rk2IsLabel K lab) (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : rk2Mult lab (rk2Ord p lab.n) ≤ 2)
    (hA : 3 ≤ CFSG.Open.pRank p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A) : False := by
  have hkr : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) :=
    rk2KRank K lab p hK hp hp2
  have hmono : CFSG.Open.pRank p A ≤ CFSG.Open.pRank p (⊤ : Subgroup K) :=
    CFSG.SectionRank.pRank_mono hp.one_lt le_top
  omega

theorem i165_false_E6_two {K : Type} [Group K] [Finite K] {A : Subgroup K} {p : ℕ}
    (hK : Rk2IsLabel K ⟨.E6, 0, 1⟩) (hp : p.Prime) (hp7 : p = 7)
    (h3 : 3 ≤ CFSG.Open.pRank p A)
    (he4 : CFSG.Open.evenRank K ≤ 4)
    (hb : (⁅A, nGen A (⊤ : Subgroup K)⁆ ≠ ⊥ ∨ CFSG.Open.pRank p A + 2 ≤ CFSG.Open.evenRank K)) :
    False := by
  subst hp7
  have hcomm : (⁅A, nGen A (⊤ : Subgroup K)⁆ : Subgroup K) ≠ ⊥ := by
    rcases hb with h | h
    · exact h
    · omega
  have hne : nGen A (⊤ : Subgroup K) ≠ ⊥ := by
    intro h
    exact hcomm (by rw [h, Subgroup.commutator_bot_right])
  have hntop : ¬ nGen A (⊤ : Subgroup K) ≤ (⊥ : Subgroup K) := by simpa using hne
  have hforall : ¬ ∀ T : Subgroup K, T ≤ ⊤ → IsPGroup 2 T →
      A ≤ Subgroup.normalizer (T : Set K) → T ≤ (⊥ : Subgroup K) := by
    intro h
    exact hntop (nGen_le_iff.2 h)
  push Not at hforall
  obtain ⟨T, -, hT2, hAT, hTbot⟩ := hforall
  have hTne : T ≠ ⊥ := fun h => hTbot (le_of_eq h)
  have hle := CFSG.HardMathSupport.Solomon.LocalBalance.pRank_le_glaTwoLocalRank_of_normalizes
    (G := K) Nat.prime_seven hTne hT2 hAT
  have hK' : LabelOf (⊤ : Subgroup K) ⟨.E6, 0, 1⟩ :=
    (hasLabel_congr (Subgroup.topEquiv (G := K)) (fun l => l = ⟨.E6, 0, 1⟩)).2 hK
  have h2 := rk2_twoLocal7_E6two hK'
  rw [← CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr
    (by norm_num : 1 < 7) (Subgroup.topEquiv (G := K))] at h2
  omega


end CFSG.LocalAnalysis.GLTheoremA.Y10F
