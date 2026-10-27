module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A520l

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lemma14_5_20_of_F4 (h331 : Stmt3_3_1_F4) (hThm : Thm14_5_3_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) : Lemma14_5_20_F4 := by
  intro G _ _ T L V H S Y p hp hYH hHY hYp
  rcases lemma14_5_20A_F4 h1222 h1332 h1334 S hp hYH hHY hYp with h1 | ⟨rfl, hL₁Y⟩
  · exact Or.inl h1
  refine Or.inr ⟨rfl, hL₁Y, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hl1two⟩ := l1_facts_F4 h1222 h1332 h1334 S hYH hHY
  set N := (pCoreOf 2 Y).subgroupOf Y with hN

  have hexp : ∀ q : ↥Y ⧸ N, q ^ 3 = 1 := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hYp y y.2)
  have hnt : Nontrivial (↥Y ⧸ N) := by
    obtain ⟨y, hy, hyO⟩ : ∃ y ∈ l1 T L V, y ∉ pCoreOf 2 Y := by
      by_contra h
      push Not at h
      exact hl1two _ (pCoreOf_isPGroup 2 Y) h
    refine ⟨⟨QuotientGroup.mk' N ⟨y, hL₁Y hy⟩, 1, fun h => hyO ?_⟩⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup (↥Y ⧸ N)) ≤ 2 := by
    have hN3 : ¬ 3 ∣ Nat.card N := by
      obtain ⟨k, hk⟩ := ((pCoreOf_isPGroup 2 Y).of_equiv
        (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 Y)).symm).exists_card_eq
      rw [hk]
      intro h
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
      omega
    rw [CFSG.SectionRank.pRank_quotient_eq N hN3]
    refine (CFSG.SectionRank.pRank_top_le_of_injective Nat.prime_three.one_lt
      (Subgroup.inclusion hYH) (Subgroup.inclusion_injective hYH)).trans ?_
    exact stronglyQuasithin_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hz.1.2 3 Nat.prime_three
      (by norm_num)
  rcases exp_three_cases hexp hr with hc | hE | hP
  · exact Or.inl (lemma14_5_20_i_F4 h1222 h1332 h1334 S hYH hHY hL₁Y hc)
  · obtain ⟨Y₀, h₁, h₂, h₃, h₄, h₅⟩ :=
      lemma14_5_20E9_of_F4 h331 hThm h1222 h1332 h1334 G T L V H S Y hYH hHY hYp hL₁Y hE
    exact Or.inr (Or.inr ⟨hE, Y₀, h₁, h₂, h₃, h₄, h₅⟩)
  · obtain ⟨h₁, h₂, h₃⟩ := lemma14_5_20_ii_F4 h331 hThm h1222 h1332 h1334 S hYH hHY hYp hL₁Y hP
    exact Or.inr (Or.inl ⟨hP, h₁, h₂, h₃⟩)

end CFSG.Quasithin.H13.L32A
