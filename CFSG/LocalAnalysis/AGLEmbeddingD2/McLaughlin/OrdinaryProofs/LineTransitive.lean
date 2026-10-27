module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Irr

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open CFSG.AGLEmbedding

theorem false_of_transitive_of_pair {G : Type*} [Group G] [Finite G] {N R A B : Subgroup G}
    (hR : IsElemAbelian 3 R) (h9 : Nat.card R = 9) (hNR : N ≤ Subgroup.normalizer (R : Set G))
    (htr : TransitiveOnNonidentity N R)
    (hA : A ≤ R) (hA3 : Nat.card A = 3) (hB : B ≤ R) (hB3 : Nat.card B = 3)
    (hinv : ∀ n ∈ N, A.map (MulAut.conj n).toMonoidHom = A ∨
      A.map (MulAut.conj n).toMonoidHom = B) : False := by
  have hAncard : (A : Set G).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]; exact hA3
  have hBncard : (B : Set G).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]; exact hB3
  have hRncard : (R : Set G).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]; exact h9
  obtain ⟨x, hxR, hxU⟩ : ∃ x ∈ (R : Set G), x ∉ (A : Set G) ∪ (B : Set G) := by
    by_contra hcon
    have hsub : (R : Set G) ⊆ (A : Set G) ∪ (B : Set G) :=
      fun x hx => by_contra fun hn => hcon ⟨x, hx, hn⟩
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_union_le (A : Set G) (B : Set G)
    omega
  have hxne : x ≠ 1 := by
    rintro rfl
    exact hxU (Or.inl A.one_mem)
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    have hsub : (A : Set G) ⊆ {1} :=
      fun a ha => by_contra fun h => hcon ⟨a, ha, fun h' => h (Set.mem_singleton_iff.mpr h')⟩
    have h1 := Set.ncard_le_ncard hsub
    rw [Set.ncard_singleton] at h1
    omega
  obtain ⟨n, hn, hnax⟩ := htr a (hA haA) x hxR ha1 hxne
  have hmem : x ∈ A.map (MulAut.conj n).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨a, haA, by simpa [MulAut.conj_apply] using hnax⟩
  rcases hinv n hn with h | h
  · rw [h] at hmem
    exact hxU (Or.inl hmem)
  · rw [h] at hmem
    exact hxU (Or.inr hmem)

end CFSG.AGLEmbeddingD2.McLaughlin

end
