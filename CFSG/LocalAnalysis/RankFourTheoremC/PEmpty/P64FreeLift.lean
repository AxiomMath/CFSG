module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreePrimeCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {A : Type} [Group A] [Finite A] {p : ℕ}

theorem exists_normalizer_conj_mem_zpowers_of_quotient (hp : p.Prime) {X Q₀ : Subgroup A}
    (hQ₀X : Q₀ ≤ X) (hQ₀ : IsPGroup p Q₀)
    (htr : ∀ a b : X, (a : A) ∈ Q₀ → a ≠ 1 → (b : A) ∈ Q₀ → b ≠ 1 →
      ∃ g ∈ normalizer (((Q₀.subgroupOf X).map
          (QuotientGroup.mk' (primeComplementCore (G := X) p)) :
            Subgroup (X ⧸ primeComplementCore (G := X) p)) : Set (X ⧸ primeComplementCore (G := X) p)),
        g * QuotientGroup.mk' (primeComplementCore (G := X) p) a * g⁻¹ ∈
          zpowers (QuotientGroup.mk' (primeComplementCore (G := X) p) b)) :
    ∀ a ∈ Q₀, a ≠ 1 → ∀ b ∈ Q₀, b ≠ 1 →
      ∃ g ∈ X ⊓ normalizer (Q₀ : Set A), g * a * g⁻¹ ∈ zpowers b := by
  have : Fact p.Prime := ⟨hp⟩
  intro a ha ha1 b hb hb1
  set O := primeComplementCore (G := X) p
  set π := QuotientGroup.mk' O
  have hQ' : IsPGroup p (Q₀.subgroupOf X) := hQ₀.comap_subtype
  have : Fact (IsPGroup p (Q₀.subgroupOf X)) := ⟨hQ'⟩
  set a' : X := ⟨a, hQ₀X ha⟩
  set b' : X := ⟨b, hQ₀X hb⟩
  have ha' : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hb' : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨gb, hgb, hgbab⟩ := htr a' b' ha ha' hb hb'
  have hN := CFSG.normalizer_map_quotient_eq_map_normalizer p (Q₀.subgroupOf X) O inferInstance
    (primeComplementCore_coprime p)
  have hgb' : gb ∈ (normalizer ((Q₀.subgroupOf X : Subgroup X) : Set X)).map π := by
    rw [← hN]
    exact hgb
  obtain ⟨g, hg, rfl⟩ := hgb'
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hgbab
  have h1 : g * a' * g⁻¹ ∈ Q₀.subgroupOf X :=
    (mem_normalizer_iff.mp hg a').mp (mem_subgroupOf.mpr ha)
  have h2 : b' ^ k ∈ Q₀.subgroupOf X := (Q₀.subgroupOf X).zpow_mem (mem_subgroupOf.mpr hb) k
  have h3 : π (g * a' * g⁻¹) = π (b' ^ k) := by
    rw [map_zpow, hk, map_mul, map_mul, map_inv]
  have h4 : (g * a' * g⁻¹)⁻¹ * b' ^ k ∈ Q₀.subgroupOf X ⊓ O :=
    ⟨(Q₀.subgroupOf X).mul_mem ((Q₀.subgroupOf X).inv_mem h1) h2, QuotientGroup.eq.mp h3⟩
  rw [CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup hp hQ' (primeComplementCore_coprime p),
    mem_bot, inv_mul_eq_one] at h4
  refine ⟨g, ⟨g.2, mem_normalizer_of_mem_normalizer_subgroupOf hQ₀X hg⟩, ?_⟩
  have h5 := congrArg Subtype.val h4
  simp only [coe_mul, coe_inv, coe_zpow] at h5
  rw [h5]
  exact zpow_mem (mem_zpowers b) k

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free
