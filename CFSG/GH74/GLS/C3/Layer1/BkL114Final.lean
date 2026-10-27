module

public import CFSG.GH74.GLS.C3.Layer1.BkL114TI
public import CFSG.GH74.GLS.C3.Layer1.BkL114Mod9
public import CFSG.GH74.GLS.C3.Layer1.BkL114Mod11

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

theorem strongly_embedded_of_cent {G : Type} [Group G] [Finite G] (hsimp : IsSimpleGroup G) {x v : G}
    (hxord : orderOf x = 2) (hnc : ¬ IsConj x v)
    (hW : pPrimeCore 2 ↥(centralizer ({x} : Set G)) ≠ ⊥)
    (hfusN : ∀ t ∈ NW x, orderOf t = 2 → (∃ c ∈ NW x, c * x * c⁻¹ = t) ∨
      (∃ c ∈ NW x, c * v * c⁻¹ = t))
    (hCv : centralizer ({v} : Set G) ≤ NW x) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (NW x) := by
  have hCN : centralizer ({x} : Set G) ≤ NW x := centralizer_le_NW x
  have hxN : x ∈ NW x := hCN (mem_centralizer_singleton_iff.2 rfl)
  refine isStronglyEmbeddedOrder_of_involutions ?_ ⟨x, hxN, hxord⟩ ?_
  · intro htop
    have hWnorm : (pPrimeCoreOf 2 (centralizer ({x} : Set G))).Normal := by
      refine ⟨fun w hw g => ?_⟩
      have hg : g ∈ NW x := htop ▸ Subgroup.mem_top g
      exact (mem_normalizer_iff.1 hg w).1 hw
    have := hsimp
    have := hWnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (pPrimeCoreOf 2 (centralizer ({x} : Set G))) with hbot | htop'
    · apply hW
      unfold pPrimeCoreOf at hbot
      exact Subgroup.map_injective (Subgroup.subtype_injective _) (by rw [hbot, Subgroup.map_bot])
    · have hxW : x ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := by rw [htop']; trivial
      have hmem := mem_pPrimeCore_of_mem_W hxW
      have hd := Subgroup.orderOf_dvd_natCard _ hmem
      rw [Subgroup.orderOf_mk, hxord] at hd
      exact absurd (Nat.Coprime.eq_one_of_dvd pPrimeCore_coprime_card hd) (by norm_num)
  · intro t htN ht2 g hg
    have ht2' : orderOf (g⁻¹ * t * g) = 2 := by
      have := orderOf_conj_eq g⁻¹ t
      rw [inv_inv] at this
      rw [this, ht2]
    rcases hfusN t htN ht2 with ⟨c, hcN, hc⟩ | ⟨c, hcN, hc⟩
    · rcases hfusN _ hg ht2' with ⟨d, hdN, hd⟩ | ⟨d, hdN, hd⟩
      · exact mem_of_conj_conj hCN hcN hdN hc hd
      · exfalso
        refine hnc (isConj_iff.2 ⟨d⁻¹ * g⁻¹ * c, ?_⟩)
        calc d⁻¹ * g⁻¹ * c * x * (d⁻¹ * g⁻¹ * c)⁻¹ = d⁻¹ * (g⁻¹ * (c * x * c⁻¹) * g) * d := by
              group
          _ = d⁻¹ * (g⁻¹ * t * g) * d := by rw [hc]
          _ = d⁻¹ * (d * v * d⁻¹) * d := by rw [hd]
          _ = v := by group
    · rcases hfusN _ hg ht2' with ⟨d, hdN, hd⟩ | ⟨d, hdN, hd⟩
      · exfalso
        refine hnc ((isConj_iff.2 ⟨d⁻¹ * g⁻¹ * c, ?_⟩ : IsConj v x).symm)
        calc d⁻¹ * g⁻¹ * c * v * (d⁻¹ * g⁻¹ * c)⁻¹ = d⁻¹ * (g⁻¹ * (c * v * c⁻¹) * g) * d := by
              group
          _ = d⁻¹ * (g⁻¹ * t * g) * d := by rw [hc]
          _ = d⁻¹ * (d * x * d⁻¹) * d := by rw [hd]
          _ = x := by group
      · exact mem_of_conj_conj hCv hcN hdN hc hd

theorem isStronglyEmbeddedOrder_NW_of_weakConfig
    (hZD : CFSG.GH74.Uniqueness.S_ZD)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {n : ℕ} (hn : n = 5 ∨ n = 7) {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW n x K T Q S a) (hS : S = T ⊔ zpowers a)
    (hz : a * x * a⁻¹ ∈ T ⊓ K) (haN : a ∈ NW x)
    (hW : pPrimeCore 2 ↥(centralizer ({x} : Set G)) ≠ ⊥)
    {H : Subgroup (NWbar x)} {e : ↥H ≃* alternatingGroup (Fin (n + 4))}
    (hHsub : H.IsSubnormal) (hKH : toNWbar x K ≤ H)
    (hKe : ((toNWbar x K).subgroupOf H).map e.toMonoidHom = stdAlt n)
    (hAM : AModel (n + 4)) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (NW x) := by
  obtain ⟨hCv, hfusN⟩ := centralizer_v_le_NW hZD hn hAM h hS hz haN hHsub hKH hKe
  exact strongly_embedded_of_cent (inferInstance : IsSimpleGroup G) h.x_order
    (not_isConj_x_v h hS hz) hW hfusN hCv

theorem b_L114_SE57_of_leaf
    (hZD : CFSG.GH74.Uniqueness.S_ZD) (hA : B_L114_fusion57) (hI : B_ivk_7_3_A57) :
    B_L114_SE57 := by
  intro G _ _ hG n hn x K T Q S a h hS haN hW
  have hn' : n = 5 ∨ n = 7 := by simpa using hn
  obtain ⟨hz, -, -⟩ := hA G hG n hn x K T Q S a h
  obtain ⟨H, e, hHsub, hKH, hKe⟩ := hI G hG n hn x K T Q S a h hS hz haN hW
  have hsimp : IsSimpleGroup G := (isKProperSimple_iff.1 hG.kproper).1
  have hAM : AModel (n + 4) := by
    rcases hn' with rfl | rfl
    · exact Mod9.amodel_nine
    · exact Mod11.amodel_eleven
  have : IsSimpleGroup G := hsimp
  exact isStronglyEmbeddedOrder_NW_of_weakConfig hZD hn' h hS hz haN hW hHsub hKH hKe hAM

theorem b_L114_final57_of_leaf
    (hZD : CFSG.GH74.Uniqueness.S_ZD) (hA : B_L114_fusion57)
    (hI : B_ivk_7_3_A57) : B_L114_final57 :=
  b_L114_final57_of_SE (b_L114_SE57_of_leaf hZD hA hI)

end CFSG.GH74.GLS.C3.Layer1.Bk
