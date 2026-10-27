module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUEight
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCNotOne
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools CFSG.Blueprint

section RHKS


variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K} {φ : G → K × K × K} {γ c : K}

theorem SzRCoords2.exists_szU (hKP : Assembly.KProper Catalog G)
    (hG : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2)
    (hS : SzR2 T₁ R₂ t d) (h : SzRCoords2 T₁ R₂ t a u v φ γ c) (hc : SzRootCoords T₁ a d u v κ)
    (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hCt : ∀ P : Sylow 2 (centralizer ({t} : Set G)), Nat.card P = 2 * Nat.card T₁)
    (hCA : centralizer ((szA₁ T₁ ⊔ zpowers t : Subgroup G) : Set G) ≤ T₁ ⊔ zpowers t)
    (hd : Odd (orderOf d)) (hY : normalizer (szR T₁ R₂ t : Set G) ≠ ⊤)
    (hodd : Odd (Nat.card ((gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).range ⊓
      MulAction.stabilizer (Equiv.Perm (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)))
        (⟨szA₁ T₁ ⊔ zpowers t, szA_mem_gmsRootConjugates T₁ R₂ t⟩ :
          gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) :
      Subgroup (Equiv.Perm (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t))))))
    (hdvd : Nat.card ((gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)).range ⊓
      MulAction.stabilizer (Equiv.Perm (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)))
        (⟨szA₁ T₁ ⊔ zpowers t, szA_mem_gmsRootConjugates T₁ R₂ t⟩ :
          gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) :
      Subgroup (Equiv.Perm (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)))) ∣
        (2 ^ (2 * a + 1) - 1) * (2 * a + 1)) :
    ∃ U U₁ : Subgroup G, SzU T₁ R₂ t d (Fintype.card K) U U₁ := by
  have hΩ : Nat.card (gmsRootConjugates (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) = 2 ^ (2 * a + 1) := by
    rw [Nat.card_coe_set_eq, h.ncard_gmsRootConjugates hG hS hc ha hK hμ hCt, hK]
  rcases odd_stabilizer_two_transitive_kProper_of_dvd hKP hY
      (gmsRootConjugateAction (szR T₁ R₂ t) (szA₁ T₁ ⊔ zpowers t)) _ le_rfl
      (h.two_transitive_gmsRootConjugates hG hS hc ha hK hμ hCt) (by omega : 1 ≤ 2 * a + 1) hΩ
      ⟨szA₁ T₁ ⊔ zpowers t, szA_mem_gmsRootConjugates T₁ R₂ t⟩ hodd hdvd with
    ⟨E, hE, hEn, hEab, hE2, hEc, hreg⟩ | ⟨hn3, -, h168, hs, -, hperf, -⟩
  · exact h.exists_szU_of_regular hG hS hc ha hK hμ hCt hCA hd hodd hE hEn hEab hE2
      (by rw [hEc, hK]) hreg
  · exact (h.false_of_card_range_eq_168 hG hS hc ha hK (by omega) hμ hCt hCA h168 hs hperf).elim

namespace SzStart

variable {L : Subgroup G} {f : ℕ} {T : Subgroup G}

theorem normalizer_szR_ne_top_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (ha : 1 ≤ a) (hfa : f = 2 * a + 1) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hR : SzR2 (szT₁ L T) R₂ t d) :
    normalizer (szR (szT₁ L T) R₂ t : Set G) ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKa : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨φ, γ, c, hφ⟩ := hR.exists_coords hc ha hKa hμ
  intro htop
  have hnorm : (szR (szT₁ L T) R₂ t).Normal := normalizer_eq_top_iff.mp htop
  have : IsSimpleGroup G := h.setting.1
  rcases Subgroup.Normal.eq_bot_or_eq_top (szR (szT₁ L T) R₂ t) with hbot | htop'
  · have ht := mem_szR_right (szT₁ L T) R₂ t
    rw [hbot, mem_bot] at ht
    have h2 := h.inv
    rw [ht, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · have hp := hφ.isPGroup_szR hc ha hKa
    have hidx : ¬ 2 ∣ (szR (szT₁ L T) R₂ t).index := by
      rw [htop', index_top]
      norm_num
    exact (h.not_isSylow_szR_of_card_sylow hS2 ha hfa hK hc hμ hR).1 ⟨hp.toSylow hidx, rfl⟩

theorem exists_szU_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (ha : 1 ≤ a) (hfa : f = 2 * a + 1) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hR : SzR2 (szT₁ L T) R₂ t d)
    (hNR : normalizer (szA L T t : Set G) ≤
      normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G))
    (hd : Odd (orderOf d)) :
    ∃ U U₁ : Subgroup G, SzU (szT₁ L T) R₂ t d (2 ^ f) U U₁ := by
  have hKa : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hG := h.not_exists_normal_index_two
  have hCt := h.card_sylow_centralizer_of_card_sylow hS2 hc hK
  obtain ⟨φ, γ, c, hφ⟩ := hR.exists_coords hc ha hKa hμ
  obtain ⟨hTeq, -, -, -, -, -, -, hCA, -⟩ := h.facts_of_card_sylow hS2
  have hCA' : centralizer ((szA₁ (szT₁ L T) ⊔ zpowers t : Subgroup G) : Set G) ≤
      szT₁ L T ⊔ zpowers t := by
    have e : centralizer ((szA₁ (szT₁ L T) ⊔ zpowers t : Subgroup G) : Set G) = T := hCA
    rw [e, ← hTeq]
  obtain ⟨hodd, hdvd⟩ := h.card_range_inf_stabilizer_of_card_sylow hS2 ha hfa hK hc hμ hR hNR
  have hdvd' := hdvd
  rw [hfa] at hdvd'
  obtain ⟨U, U₁, hU⟩ := hφ.exists_szU h.setting.2.2.1 hG hR hc ha hKa hμ hCt hCA' hd
    (h.normalizer_szR_ne_top_of_card_sylow hS2 ha hfa hK hc hμ hR) hodd hdvd'
  rw [hK] at hU
  exact ⟨U, U₁, hU⟩

theorem sq_eq_one_of_not_inverts_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (ha : 1 ≤ a) (hfa : f = 2 * a + 1) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hR : SzR2 (szT₁ L T) R₂ t d)
    (hNR : normalizer (szA L T t : Set G) ≤
      normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G))
    (hd : Odd (orderOf d)) (hinv : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) :
    ∀ r ∈ R₂, r ^ 2 = 1 := by
  have hKa : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hG := h.not_exists_normal_index_two
  have hCt := h.card_sylow_centralizer_of_card_sylow hS2 hc hK
  obtain ⟨φ, γ, c, hφ⟩ := hR.exists_coords hc ha hKa hμ
  have hγ := hφ.gamma_eq_zero hG hR hc ha hKa hμ hCt
  obtain ⟨U, U₁, hU⟩ := h.exists_szU_of_card_sylow hS2 ha hfa hK hc hμ hR hNR hd
  rw [← hK] at hU
  push Not at hinv
  exact hφ.sq_eq_one_of_not_inverts hR hc ha hKa hγ hU hinv

theorem exists_szU (h : SzStart G L f t T)
    (ha : 1 ≤ a) (hfa : f = 2 * a + 1) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hR : SzR2 (szT₁ L T) R₂ t d)
    (hNR : normalizer (szA L T t : Set G) ≤
      normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G))
    (hd : Odd (orderOf d)) :
    ∃ U U₁ : Subgroup G, SzU (szT₁ L T) R₂ t d (2 ^ f) U U₁ :=
  h.exists_szU_of_card_sylow h.card_sylow ha hfa hK hc hμ hR hNR hd

theorem sq_eq_one_of_not_inverts (h : SzStart G L f t T)
    (ha : 1 ≤ a) (hfa : f = 2 * a + 1) (hK : Fintype.card K = 2 ^ f)
    (hc : SzRootCoords (szT₁ L T) a d u v κ)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
    (hR : SzR2 (szT₁ L T) R₂ t d)
    (hNR : normalizer (szA L T t : Set G) ≤
      normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G))
    (hd : Odd (orderOf d)) (hinv : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) :
    ∀ r ∈ R₂, r ^ 2 = 1 :=
  h.sq_eq_one_of_not_inverts_of_card_sylow h.card_sylow ha hfa hK hc hμ hR hNR hd hinv

end SzStart

end RHKS

namespace SzStart

section Main


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_szR2_szU (h : SzStart G L f t T) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      Fintype.card K = 2 ^ f ∧ ∃ (d : G) (u v : G → K) (κ : K), d ∈ L ∧ Odd (orderOf d) ∧
        SzRootCoords (szT₁ L T) a d u v κ ∧ (∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) ∧
        (∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w) ∧
        ∃ R₂ : Subgroup G, SzR2 (szT₁ L T) R₂ t d ∧
          normalizer (szA L T t : Set G) ≤
            normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ∧
          Nat.card (szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) = 2 * (2 ^ f) ^ 3 ∧
          (szT₁ L T ⊔ R₂ ⊔ zpowers t) ⊓ centralizer ({t} : Set G) = T ∧
          (∀ x ∈ szT₁ L T, ∀ r ∈ R₂, x * r = r * x) ∧
          normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ≤
            normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) ∧
          normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ≤
            normalizer (R₂ : Set G) ∧
          ((¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → ∀ r ∈ R₂, r ^ 2 = 1) ∧
          ∃ U U₁ : Subgroup G, SzU (szT₁ L T) R₂ t d (2 ^ f) U U₁ := by
  obtain ⟨a, ha, hfa, K, _, _, _, hK, d, u, v, κ, hdL, hodd, hc, hκ, hμ, R₂, hR, hNR, hcard, hCR,
    -⟩ := h.exists_szR2_coords
  obtain ⟨h1, h2, h3, -⟩ := h.secondLevel ha hfa hK hc hμ hR hNR
  obtain ⟨U, U₁, hU⟩ := h.exists_szU ha hfa hK hc hμ hR hNR hodd
  exact ⟨a, ha, hfa, K, inferInstance, inferInstance, inferInstance, hK, d, u, v, κ, hdL, hodd, hc,
    hκ, hμ, R₂, hR, hNR, hcard, hCR, h1, h2, h3,
    fun hinv => h.sq_eq_one_of_not_inverts ha hfa hK hc hμ hR hNR hodd hinv, U, U₁, hU⟩

end Main

end SzStart

end CFSG.SeitzReduction.RankOne
