module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRTwoData
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRegular
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRTwoGroup
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRTwoTorus

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint SzPartition

namespace SzStart

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem szRSetup_of_regular (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hT : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T)
    {E : Subgroup (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t)))}
    (hE : E ≤ (gmsRootConjugateAction (szA L T t) (zpowers t)).range)
    (hEn : (E.subgroupOf (gmsRootConjugateAction (szA L T t) (zpowers t)).range).Normal)
    (hEc : Nat.card E = 2 ^ f)
    (hreg : ∀ Q Z, ∃! e : E, (e : Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t))) Q = Z)
    {K : Type*} [Field K] [Fintype K] {a : ℕ} (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {d : G} {u v : G → K} {κ : K} (hdL : d ∈ L) (hc : SzRootCoords (szT₁ L T) a d u v κ)
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w) :
    SzRSetup (szT₁ L T) (szRGroup L T t E) t d a u v κ := by
  have hR := h.szRData_of_regular hS2 hT hE hEn hEc hreg
  have hD := h.partitionData_of_card_sylow hS2 hT
  obtain ⟨hTeq, hdisj, -, -, -, -, -, hCA, -, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨hNA, -⟩ := h.partition_of_card_sylow hS2 hT
  have htT₁ : t ∉ szT₁ L T := by
    intro htT
    have ht1 : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨htT, mem_zpowers t⟩
    rw [hdisj, mem_bot] at ht1
    have h2 := h.inv
    rw [ht1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hNT : normalizer (szA L T t : Set G) ≤
      normalizer ((szT₁ L T ⊔ zpowers t : Subgroup G) : Set G) := by
    have h1 := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (szA L T t)
    rw [hCA] at h1
    exact h1.trans (le_of_eq (congrArg (fun H : Subgroup G => normalizer (H : Set G)) hTeq))
  refine ⟨hc, ha, hK, hμ, h.mem_centralizer_szT₁, h.sq_eq_one, htT₁,
    mem_centralizer_iff.mp h.mem d hdL, hR.le_normalizer, hR.le_normalizer.trans hNT,
    hR.le_normalizer.trans hNA, hR.normalizer_le, (le_of_eq hTeq.symm).trans hR.le,
    hR.isPGroup, hR.inf_centralizer.trans hTeq, fun x hx => ?_, hR.exists_conj,
    hR.mem_of_isPGroup⟩
  obtain ⟨c, hc, hct⟩ := hD.exists_conj_t_eq (hR.le_normalizer hx)
  rw [hct, mul_inv_cancel_right]
  exact hc

theorem exists_szR2_coords_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hT : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T) (h34 : NoStronglyClosedAbelianTwo G)
    {E : Subgroup (Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t)))}
    (hE : E ≤ (gmsRootConjugateAction (szA L T t) (zpowers t)).range)
    (hEn : (E.subgroupOf (gmsRootConjugateAction (szA L T t) (zpowers t)).range).Normal)
    (hEc : Nat.card E = 2 ^ f)
    (hreg : ∀ Q Z, ∃! e : E, (e : Equiv.Perm (gmsRootConjugates (szA L T t) (zpowers t))) Q = Z) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      Fintype.card K = 2 ^ f ∧ ∃ (d : G) (u v : G → K) (κ : K), d ∈ L ∧ Odd (orderOf d) ∧
        SzRootCoords (szT₁ L T) a d u v κ ∧ (∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) ∧
        (∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w) ∧
        ∃ R₂ : Subgroup G, SzR2 (szT₁ L T) R₂ t d ∧
          normalizer (szA L T t : Set G) ≤
            normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ∧
          Nat.card (szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) = 2 * (2 ^ f) ^ 3 ∧
          (szT₁ L T ⊔ R₂ ⊔ zpowers t) ⊓ centralizer ({t} : Set G) = T ∧
          ∀ x ∈ R₂, ∀ y ∈ R₂, x * y = y * x := by
  obtain ⟨a, ha, hfa, K, _, _, _, hK, d, u, v, κ, hdL, -, hc, hκ, hμ⟩ :=
    h.exists_torusCoords_of_card_sylow hS2
  have hKa : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨k, hodd, hck, hκk, hμk⟩ := hc.exists_odd_pow hκ hμ
  have hR := h.szRData_of_regular hS2 hT hE hEn hEc hreg
  have hS := h.szRSetup_of_regular hS2 hT hE hEn hEc hreg ha hKa (pow_mem hdL k) hck hμk
  obtain ⟨R₂, hR₂, hReq, -⟩ := hS.exists_szR2 h34 hodd
  refine ⟨a, ha, hfa, K, inferInstance, inferInstance, inferInstance, hK, d ^ k, u, v, κ ^ k,
    pow_mem hdL k, hodd, hck, hκk, hμk, R₂, hR₂, ?_, ?_, ?_, hR₂.R₂_comm⟩
  · rw [hReq]
    exact hR.normalizer_le
  · rw [hReq]
    exact hR.card
  · rw [hReq]
    exact hR.inf_centralizer

theorem noStronglyClosedAbelianTwo
    (h : SzStart G L f t T) : NoStronglyClosedAbelianTwo G :=
  fun S _ hAS hAab hA1 hcl =>
    false_of_stronglyClosed_abelian h.setting (Or.inr (Or.inr ⟨f, h.model⟩)) S hAS hAab hA1 hcl

section Main

theorem exists_szR2_coords (h : SzStart G L f t T) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      Fintype.card K = 2 ^ f ∧ ∃ (d : G) (u v : G → K) (κ : K), d ∈ L ∧ Odd (orderOf d) ∧
        SzRootCoords (szT₁ L T) a d u v κ ∧ (∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) ∧
        (∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w) ∧
        ∃ R₂ : Subgroup G, SzR2 (szT₁ L T) R₂ t d ∧
          normalizer (szA L T t : Set G) ≤
            normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ∧
          Nat.card (szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) = 2 * (2 ^ f) ^ 3 ∧
          (szT₁ L T ⊔ R₂ ⊔ zpowers t) ⊓ centralizer ({t} : Set G) = T ∧
          ∀ x ∈ R₂, ∀ y ∈ R₂, x * y = y * x := by
  obtain ⟨E, hE, hEn, -, -, hEc, hreg⟩ := h.exists_regular_elementary
  exact h.exists_szR2_coords_of_card_sylow h.card_sylow h.not_sylow h.noStronglyClosedAbelianTwo
    hE hEn hEc hreg

end Main

end SzStart

end CFSG.SeitzReduction.RankOne
