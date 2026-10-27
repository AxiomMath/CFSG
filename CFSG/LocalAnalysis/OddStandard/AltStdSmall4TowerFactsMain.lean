module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerFactsIso
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerMainSteps
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerEmbedCard

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G}

theorem false_of_towerFacts {X : Type} [Group X] {n : ℕ} (hX : Nat.card X = 2 ^ n) {t' : X}
    (hF : TowerFacts X t') [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (ht : CentHyp t)
    (ht2 : t ^ 2 = 1) (ι : X →* G) (hι : Function.Injective ι) (hιt : ι t' = t) : False := by
  obtain ⟨⟨hC1, Q, hQ, htQ, hin, hout⟩, hF2⟩ := hF
  have hK := isPGroup_range hι hX
  have htK : t ∈ ι.range := ⟨t', hιt⟩
  obtain ⟨c, hcN, hcK, hc2, hct⟩ := level1_step ht hnab hK htK ht2 (map_le_range ι Q)
    (by rw [relIndex_map_range hι]; exact hQ) (by rw [← hιt, mem_map_iff_mem hι]; exact htQ)
    (by
      rintro _ ⟨q, hq, rfl⟩ h2 h1
      rw [← map_pow, map_eq_one_iff ι hι] at h2
      rw [Ne, map_eq_one_iff ι hι] at h1
      rw [card_cent_map hι, pinv_map_iff hι]
      exact hin q hq h2 h1)
    (by
      rintro _ ⟨q, rfl⟩ h2 - hq
      rw [← map_pow, map_eq_one_iff ι hι] at h2
      rw [mem_map_iff_mem hι] at hq
      rw [← hιt]
      exact conj_map hι (hout q hq h2))
  set D := ExtData.ofConj hι hcN hc2
  set Φ := cycHom hι hcN hc2
  have hΦ : Function.Injective Φ := cycHom_injective hι hcN hc2 hcK
  have hK₂ : IsPGroup 2 Φ.range :=
    isPGroup_range hΦ (n := n + 1) (by rw [CycExt.card, hX, pow_succ])
  have hΦt : Φ (CycExt.incl D t') = t := by rw [cycHom_incl, hιt]
  have htK₂ : t ∈ Φ.range := ⟨_, hΦt⟩
  have hC2 : Nat.card (Φ.range ⊓ centralizer {t} : Subgroup G) = 2 ^ 8 := by
    have h2 : 2 * Nat.card (ι.range ⊓ centralizer {t} : Subgroup G) ≤
        Nat.card (Φ.range ⊓ centralizer {t} : Subgroup G) :=
      two_mul_card_le (inf_le_inf_right (centralizer {t}) (range_le_cycHom hι hcN hc2))
      (mem_inf.2 ⟨mem_range_cycHom hι hcN hc2, mem_centralizer_singleton_iff.2 hct⟩)
      (fun h => hcK (mem_inf.1 h).1)
    have h1 : Nat.card (ι.range ⊓ centralizer {t} : Subgroup G) = 2 ^ 7 := by
      rw [← hιt, card_cent_map hι]
      exact hC1
    have h3 : Nat.card (Φ.range ⊓ centralizer {t} : Subgroup G) ≤ 2 ^ 8 :=
      ht.card_le _ inf_le_right (hK₂.to_le inf_le_left)
    omega
  have hα : D.α t' = t' := hι (by rw [map_ofConj_α, hιt, hct, mul_inv_cancel_right])
  have hg : D.g * t' = t' * D.g := hι (by
    rw [map_mul, map_mul, map_ofConj_g, hιt]
    exact ((show Commute c t from hct).pow_left 2).eq)
  have hP2 : PInv (centralizer {CycExt.incl D t'} : Subgroup (CycExt D)) := by
    rw [← pinv_map_iff hΦ, hΦt]
    exact pinv_of_conj ht hK₂ (g := 1) (by group) hC2.ge
  obtain ⟨Q₂, hQ₂, htQ₂, hQP₂, x₀, hcls₂, hor⟩ := hF2 D hα hg hP2
  obtain ⟨hnot, c', hc'N, hc'K, hc'2, hc'x⟩ := level2_step ht hnab hK₂ htK₂ ht2 hC2
    (map_le_range Φ Q₂) (by rw [relIndex_map_range hΦ]; exact hQ₂)
    (by rw [← hΦt, mem_map_iff_mem hΦ]; exact htQ₂)
    (by
      rintro _ ⟨q, hq, rfl⟩ h
      exact hQP₂ q hq ((isPInv_map_iff hΦ q).1 h))
    (x₀ := Φ x₀) (by
      intro x hx
      obtain ⟨q, rfl⟩ := MonoidHom.mem_range.1 hx.1
      rw [← hΦt]
      exact (hcls₂ q ((isPInv_map_iff hΦ q).1 hx)).imp (conj_map hΦ) (conj_map hΦ))
  rcases hor with hx₀ | hL3
  · obtain ⟨k, hk, hx⟩ := conj_map hΦ hx₀
    rw [hΦt] at hx
    exact hnot k hk hx
  set Φ' := cycHom hΦ hc'N hc'2
  have hΦ' : Function.Injective Φ' := cycHom_injective hΦ hc'N hc'2 hc'K
  have hK₃ : IsPGroup 2 Φ'.range :=
    isPGroup_range hΦ' (n := n + 2) (by rw [CycExt.card, CycExt.card, hX, pow_succ, pow_succ])
  have hΦ't : Φ' (CycExt.incl _ (CycExt.incl D t')) = t := by rw [cycHom_incl, hΦt]
  have hC3 : Nat.card (Φ'.range ⊓ centralizer {t} : Subgroup G) = 2 ^ 8 := by
    have h1 : Nat.card (Φ.range ⊓ centralizer {t} : Subgroup G) ≤
        Nat.card (Φ'.range ⊓ centralizer {t} : Subgroup G) :=
      card_le_of_le (inf_le_inf_right (centralizer {t}) (range_le_cycHom hΦ hc'N hc'2))
    have h3 : Nat.card (Φ'.range ⊓ centralizer {t} : Subgroup G) ≤ 2 ^ 8 :=
      ht.card_le _ inf_le_right (hK₃.to_le inf_le_left)
    omega
  obtain ⟨Q₃, hQ₃, htQ₃, hcls₃⟩ := hL3 (ExtData.ofConj hΦ hc'N hc'2)
    (hΦ (by rw [map_ofConj_α, hc'x, hΦt]))
    (by rw [← card_cent_map hΦ', hΦ't]; exact hC3)
  exact level3_false ht hnab hK₃ ⟨_, hΦ't⟩ ht2 hC3 (map_le_range Φ' Q₃)
    (by rw [relIndex_map_range hΦ']; exact hQ₃) (by rw [← hΦ't, mem_map_iff_mem hΦ']; exact htQ₃)
    (by
      intro x hx
      obtain ⟨q, rfl⟩ := MonoidHom.mem_range.1 hx.1
      rw [← hΦ't]
      exact conj_map hΦ' (hcls₃ q ((isPInv_map_iff hΦ' q).1 hx)))

theorem t₀_sq (S : Subgroup (GL (Fin 6) (ZMod 2))) (h : GL62.z₀ ∈ S) : t₀ S h ^ 2 = 1 := by
  rw [sq]
  refine SemidirectProduct.ext ?_ ?_
  · rw [SemidirectProduct.mul_left, t₀_left, map_one, one_mul]
    rfl
  · rw [SemidirectProduct.mul_right, t₀_right]
    exact Subtype.ext GL62.z0_mul_self

theorem card_grp {S : Subgroup (GL (Fin 6) (ZMod 2))} (hS : Nat.card S = 2 ^ 7) :
    Nat.card (Grp S) = 2 ^ 13 := by
  rw [SemidirectProduct.card, hS, Nat.card_eq_fintype_card (α := Multiplicative _),
    Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem false_of_towerFacts_model {S : Subgroup (GL (Fin 6) (ZMod 2))} (h0 : GL62.z₀ ∈ S)
    (hS : Nat.card S = 2 ^ 7) (hF : TowerFacts (Grp S) (t₀ S h0)) [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (ht : CentHyp t) (ι : Grp S →* G)
    (hι : Function.Injective ι) (hιt : ι (t₀ S h0) = t) : False :=
  false_of_towerFacts (card_grp hS) hF hnab ht (by rw [← hιt, ← map_pow, t₀_sq, map_one]) ι hι hιt

theorem wrFalse_of_towerFacts (hF : TowerFacts (Grp wrS) (t₀ wrS z0_mem_wrS)) : WrFalse := by
  intro G _ _ _ hnab t ht ι hι hιt
  exact false_of_towerFacts_model z0_mem_wrS card_wrS hF hnab ht ι hι hιt

theorem slFalse_of_towerFacts (hF : TowerFacts (Grp slS) (t₀ slS z0_mem_slS)) : SlFalse := by
  intro G _ _ _ hnab t ht ι hι hιt
  exact false_of_towerFacts_model z0_mem_slS card_slS hF hnab ht ι hι hιt

end CFSG.OddStandard.AltStdSmall4.Tower
