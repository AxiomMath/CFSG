module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFPreimage
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.NormalIndexSix
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G}

theorem exists_normal_order_three_of_single_factor (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) {L : Subgroup (MulAut (IntMod V hV))}
    (hL6 : Nat.card L = 6) (hLM : L ≤ autI hV M)
    (hLn : ∀ g ∈ autI hV M, ∀ φ ∈ L, g * φ * g⁻¹ ∈ L)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M)) :
    ∃ P₀ : Subgroup G, P₀ ≤ M ∧ Nat.card P₀ = 3 ∧
      ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal := by
  obtain ⟨P₀, hP₀Y, hP₀, hnorm⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_normal_order_three_of_index_six
      (M := M) (C := Subgroup.centralizer (V : Set G) ⊓ M) (L := preAutM hV hM L)
      (centralizer_inf_le_preAutM hV hM L) (preAutM_le hV hM L) (preAutM_normal hV hM hLn)
      (centralizer_inf_subgroupOf_normal hV hM) hC3
      (by rw [card_preAutM_of_le hV hM hLM, hL6])
  exact ⟨P₀, hP₀Y.trans (preAutM_le hV hM L), hP₀, hnorm⟩

theorem exists_normal_order_three_of_family_card_one (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) {I : Finset (Subgroup (MulAut (IntMod V hV)))}
    (hcard : ∀ L ∈ I, Nat.card L = 6) (hJ : autI hV (thompsonJ M) = ⨆ L ∈ I, L)
    (hperm : ∀ g ∈ autI hV M, ∀ L ∈ I, B1.conjAut g L ∈ I) (hI1 : I.card = 1)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M)) :
    ∃ P₀ : Subgroup G, P₀ ≤ M ∧ Nat.card P₀ = 3 ∧
      ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal := by
  obtain ⟨L, rfl⟩ := Finset.card_eq_one.1 hI1
  have hJL : autI hV (thompsonJ M) = L := by simpa using hJ
  refine exists_normal_order_three_of_single_factor hV hM (hcard L (Finset.mem_singleton_self L))
    ?_ ?_ hC3
  · rw [← hJL]
    exact autI_mono hV (thompsonJ_le_self M)
  · intro g hg φ hφ
    have h := hperm g hg L (Finset.mem_singleton_self L)
    rw [Finset.mem_singleton] at h
    have : g * φ * g⁻¹ ∈ B1.conjAut g L := by
      rw [B1.mem_conjAut]
      simpa [mul_assoc] using hφ
    rwa [h] at this

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
