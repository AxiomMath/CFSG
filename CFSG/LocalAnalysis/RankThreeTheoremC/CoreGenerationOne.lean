module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2MathieuBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open Subgroup CFSG.AGLEmbedding.CoreD2

@[expose] def CoreGenerationOneOf (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∃ E : Subgroup G, Nat.card E = p ^ 3 ∧ (∀ x ∈ E, x ^ p = 1) ∧
    (∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) ∧
    ∀ A : Subgroup G, A ≤ E → IsElemAbelian p A → Nat.card A = p ^ 2 →
      ∃ Γ : Set G, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ,
        ∃ Q : Subgroup G, Q ≤ A ∧ 1 ≤ CFSG.Open.pRank p Q ∧ g ∈ normalizer (Q : Set G)

variable {X : Type*} [Group X]

theorem coreGenerationOneOf_of_gens [Finite X] {G : Subgroup X} {p : ℕ} (hp : p.Prime)
    {S : Set X} (hS : G = Subgroup.closure S) {E : Subgroup X} (hEc : Nat.card E = p ^ 3)
    (hEexp : ∀ x ∈ E, x ^ p = 1) (hEnab : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) (hEG : E ≤ G)
    (hΓ : ∀ A : Subgroup X, A ≤ E → IsElemAbelian p A → Nat.card A = p ^ 2 →
      ∃ Γ : Set X, Γ ⊆ G ∧ S ⊆ Subgroup.closure Γ ∧ ∀ g ∈ Γ,
        (∃ u v : X, u ∈ A ∧ v ∈ A ∧ u ^ p = 1 ∧ v ^ p = 1 ∧ u * v = v * u ∧ u ≠ 1 ∧
          (∀ j < p, v ≠ u ^ j) ∧ ∃ α β γ δ : ℕ,
            g * u = (u ^ α * v ^ β) * g ∧ g * v = (u ^ γ * v ^ δ) * g) ∨
        (∃ y ∈ A, y ≠ 1 ∧ y ^ p = 1 ∧ ∃ α : ℕ, g * y = y ^ α * g)) :
    CoreGenerationOneOf ↥G p := by
  refine ⟨E.subgroupOf G, ?_, fun x hx => Subtype.ext (by simpa using hEexp _ hx), ?_, ?_⟩
  · rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv
  · obtain ⟨x, hx, y, hy, hxy⟩ := hEnab
    exact ⟨⟨x, hEG hx⟩, Subgroup.mem_subgroupOf.2 hx, ⟨y, hEG hy⟩, Subgroup.mem_subgroupOf.2 hy,
      fun h => hxy (congrArg Subtype.val h)⟩
  · intro A' hA'E hA'e hA'c
    set A : Subgroup X := A'.map G.subtype with hAdef
    have hAE : A ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hA'E hx)
    have hAe : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hA'e _
    have hAc : Nat.card A = p ^ 2 := by
      rw [hAdef, Subgroup.card_map_of_injective G.subtype_injective, hA'c]
    have hmemA : ∀ {x : X} (hx : x ∈ A), (⟨x, hEG (hAE hx)⟩ : ↥G) ∈ A' := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
      rwa [show y = ⟨x, hEG (hAE hx)⟩ from Subtype.ext hyx] at hy
    obtain ⟨Γ, hΓG, hgen, hnorm⟩ := hΓ A hAE hAe hAc
    refine ⟨{g : ↥G | (g : X) ∈ Γ}, ?_, ?_⟩
    · rw [eq_top_iff]
      intro h _
      have hmap : (Subgroup.closure {g : ↥G | (g : X) ∈ Γ}).map G.subtype =
          Subgroup.closure Γ := by
        rw [MonoidHom.map_closure]
        congr 1
        ext z
        constructor
        · rintro ⟨g, hg, rfl⟩
          exact hg
        · intro hz
          exact ⟨⟨z, hΓG hz⟩, hz, rfl⟩
      have hle : G ≤ (Subgroup.closure {g : ↥G | (g : X) ∈ Γ}).map G.subtype := by
        rw [hmap, hS, Subgroup.closure_le]
        exact hgen
      obtain ⟨k, hk, hkh⟩ := hle h.2
      have : k = h := Subtype.ext hkh
      rwa [← this]
    · intro g hg
      rcases hnorm _ hg with ⟨u, v, huA, hvA, hu, hv, huv, hu1, hvu, α, β, γ, δ, h1, h2⟩ |
        ⟨y, hyA, hy1, hy, α, h1⟩
      · set u' : ↥G := ⟨u, hEG (hAE huA)⟩ with hu'
        set v' : ↥G := ⟨v, hEG (hAE hvA)⟩ with hv'
        refine ⟨Subgroup.closure ({u', v'} : Set ↥G), ?_, ?_, ?_⟩
        · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
          exact ⟨hmemA huA, hmemA hvA⟩
        · refine le_trans (by norm_num) (two_le_pRank_closure_pair hp ?_ ?_ ?_ ?_ ?_)
          · exact Subtype.ext (by simpa [hu'] using hu)
          · exact Subtype.ext (by simpa [hv'] using hv)
          · exact Subtype.ext (by simpa [hu', hv'] using huv)
          · exact fun h => hu1 (congrArg Subtype.val h)
          · intro j hj h
            exact hvu j hj (by simpa [hu', hv'] using congrArg Subtype.val h)
        · exact mem_normalizer_closure_pair (α := α) (β := β) (γ := γ) (δ := δ)
            (Subtype.ext (by simpa [hu', hv'] using h1))
            (Subtype.ext (by simpa [hu', hv'] using h2))
      · obtain ⟨y', hy'A, rfl⟩ := Subgroup.mem_map.1 hyA
        have hy'p : y' ^ p = 1 := Subtype.ext (by simpa using hy)
        have hy'1 : y' ≠ 1 := fun h => hy1 (by simpa using congrArg Subtype.val h)
        have : Fact p.Prime := ⟨hp⟩
        have hord : orderOf y' = p := orderOf_eq_prime hy'p hy'1
        refine ⟨Subgroup.zpowers y', Subgroup.zpowers_le.2 hy'A, ?_,
          mem_normalizer_zpowers_of_mul_eq (α := α) (Subtype.ext (by simpa using h1))⟩
        exact CFSG.SectionRank.le_pRank hp.one_lt le_rfl (isElemAbelian_zpowers hy'p)
          (by rw [Nat.card_zpowers, hord, pow_one])

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
