module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RCtx
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHD16
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHProd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHSc
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHuA

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem isPGroup_zpowers_of_sq {G : Type} [Group G] {u : G} (hu : u * u = 1) :
    IsPGroup 2 (zpowers u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : u = 1
  · rw [h1, zpowers_one_eq_bot]
    exact IsPGroup.of_card (n := 0) (by simp)
  · have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu) h1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)

namespace OuterS16Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (c : OuterS16Ctx G L z t T E Q x B β S)

include c

theorem z_conj_sigma_five (hH : Harada75E8) {σ ξ : G} (hσ2 : σ * σ = 1) (hσz : σ * z = z * σ)
    (hσL : σ ∉ L ⊔ zpowers z) {V0 : Subgroup G}
    (hV0L : V0 ≤ L ⊓ centralizer ({σ} : Set G)) (hV02 : IsPGroup 2 V0)
    (hV0max : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ L ⊓ centralizer ({σ} : Set G) → V0 ≤ R →
      R ≤ V0)
    (hV0D : Nonempty (↥V0 ≃* DihedralGroup 8))
    (hξ : ∃ g : G, g * (z * σ) * g⁻¹ = ξ)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hRξ : R ≤ centralizer ({ξ} : Set G)) (hξR : ξ ∈ R)
    (h5 : ∀ X : Finset G, (↑X : Set G) ⊆ ↑R → X.card ≤ 4 →
      Subgroup.closure (X : Set G) ⊔ Subgroup.zpowers ξ ≠ R) :
    ∃ g : G, g * z * g⁻¹ = σ := by
  by_contra hnc
  have hcfg := c.hyp.outerE.cfg
  have hz2 : z * z = 1 := hcfg.z_sq
  have hzσ : z * σ = σ * z := hσz.symm
  obtain ⟨c0, d0, hc0, hd0, hc2, hd2, hc1, hd1, hc0d0, hcd, hcentV0, hself, hcard⟩ :=
    exists_klein_selfcentralizing hV0D.some
  have hV0L' : V0 ≤ L := fun v hv => (hV0L hv).1
  have hV0σ : V0 ≤ centralizer ({σ} : Set G) := fun v hv => (hV0L hv).2
  have hV0z : V0 ≤ centralizer ({z} : Set G) := fun v hv =>
    mem_centralizer_singleton_iff.2 (hcfg.z_comm_of_mem_A (hV0L' hv))
  have hσV0 : σ ∉ V0 := fun h => hσL (mem_sup_left (hV0L' h))
  have hzV0 : z ∉ V0 ⊔ zpowers σ := by
    intro hmem
    have hzσc : zpowers σ ≤ centralizer (V0 : Set G) := by
      rw [zpowers_le]
      exact mem_centralizer_iff.2 fun v hv => mem_centralizer_singleton_iff.1 (hV0σ hv)
    obtain ⟨v, hv, w, hw, hvw⟩ := exists_mul_of_mem_sup_comm' hzσc hmem
    rcases mem_zpowers_sq_eq_one hσ2 hw with h1 | h1
    · rw [h1, mul_one] at hvw
      exact hcfg.z_not_mem_A (hvw ▸ hV0L' hv)
    · rw [h1] at hvw
      apply hσL
      have hσ' : σ = v⁻¹ * z := by rw [hvw]; group
      rw [hσ']
      exact mul_mem (mem_sup_left (inv_mem (hV0L' hv))) (mem_sup_right (mem_zpowers z))
  set A : Subgroup G := zpowers z ⊔ zpowers σ with hA
  have hzP2 : IsPGroup 2 (zpowers z) := isPGroup_zpowers_of_sq hz2
  have hσP2 : IsPGroup 2 (zpowers σ) := isPGroup_zpowers_of_sq hσ2
  have hzσn : zpowers z ≤ normalizer (zpowers σ : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun w hw => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
      exact (Commute.zpow_left (show Commute σ z from hσz) k).eq
  have hA2 : IsPGroup 2 A := hzP2.to_sup_of_normal_right' hσP2 hzσn
  have hV0A : V0 ≤ centralizer (A : Set G) := by
    intro v hv
    rw [mem_centralizer_iff]
    intro a ha
    have hA' : A ≤ centralizer ({v} : Set G) := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (hV0z hv)).symm
      · exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (hV0σ hv)).symm
    exact mem_centralizer_singleton_iff.1 (hA' ha)
  have hAn : V0 ≤ normalizer (A : Set G) := hV0A.trans (centralizer_le_normalizer _)
  set D : Subgroup G := A ⊔ V0 with hD
  have hD2 : IsPGroup 2 D := hA2.to_sup_of_normal_left' hV02 hAn
  have hAz : A ≤ centralizer ({z} : Set G) := by
    refine sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)) (zpowers_le.2 ?_)
    exact mem_centralizer_singleton_iff.2 hσz
  have hAσ : A ≤ centralizer ({σ} : Set G) := by
    refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    exact mem_centralizer_singleton_iff.2 hσz.symm
  have hDz : D ≤ centralizer ({z} : Set G) := sup_le hAz hV0z
  have hDσ : D ≤ centralizer ({σ} : Set G) := sup_le hAσ hV0σ
  have hDmax : ∀ R : Subgroup G, IsPGroup 2 R →
      R ≤ centralizer ({z} : Set G) ⊓ centralizer ({σ} : Set G) → D ≤ R → R ≤ D := by
    intro R hR hRY hDR
    have hYCA : centralizer ({z} : Set G) ⊓ centralizer ({σ} : Set G) =
        (L ⊓ centralizer ({σ} : Set G)) ⊔ A :=
      cent_sigma_eq hcfg hσz hσL hσ2
    have hAc : ∀ a ∈ A, ∀ y ∈ centralizer ({z} : Set G) ⊓ centralizer ({σ} : Set G),
        a * y = y * a := by
      intro a ha y hy
      have hA' : A ≤ centralizer ({y} : Set G) := by
        refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
        · exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hy.1).symm
        · exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hy.2).symm
      exact mem_centralizer_singleton_iff.1 (hA' ha)
    have := maximal_two_sup_central hYCA hA2 hAc hV0L hV0max R hR hRY
      (by rw [sup_comm, ← hD]; exact hDR)
    rw [hD, sup_comm]; exact this
  have hcV0z : c0 * z = z * c0 := mem_centralizer_singleton_iff.1 (hV0z hc0)
  have hdV0z : d0 * z = z * d0 := mem_centralizer_singleton_iff.1 (hV0z hd0)
  have hKV0 : Subgroup.closure ({c0, d0} : Set G) ≤ V0 := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hc0
    · exact hd0
  have hzK : z ∉ Subgroup.closure ({c0, d0} : Set G) := fun h =>
    hcfg.z_not_mem_A (hV0L' (hKV0 h))
  obtain ⟨hA₀e, hA₀8⟩ := elemAbelian8_of_card4 hz2 hc2 hd2 hcV0z.symm hdV0z.symm hcd hcard hzK
  have hA₀D : Subgroup.closure ({z, c0, d0} : Set G) ≤ D := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact mem_sup_left (mem_sup_left (mem_zpowers y))
    · exact mem_sup_right hc0
    · exact mem_sup_right hd0
  have hzA : z ∈ Subgroup.closure ({z, c0, d0} : Set G) := subset_closure (by simp)
  have huA := uA_not_mem hz2 hσ2 hV0z hc0 hd0 hσV0 hzV0
  have hcent := sc_step hz2 hσ2 hzσ hV0z hV0σ hzV0 hc0 hd0 hself
  exact harada_contradiction hH hz2 hσ2 hzσ hnc hD2 hDz hDσ hDmax hA₀D hA₀e hA₀8 hzA huA hcent hξ
    hR2 hRξ hξR h5

end OuterS16Ctx

end CFSG.EvenSporadicStandard.Fin76b
