module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoNormalizerECount

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace Janko

open JankoNormalizerE

variable {G : Type*} [Group G] {z : G} (hz : orderOf z = 2)
  (hH : IsTwoANine (centralizer ({z} : Set G)))
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))

theorem L_le_K : closure ({ℓ e, t e} : Set G) ≤ K e := by
  rw [closure_le]
  rintro _ (rfl | rfl)
  · exact ℓ_mem_K e
  · exact t_mem_K e

include hH

theorem K_le_normalizer : K e ≤ normalizer (E e : Set G) := fun x hx => by
  have h : x ∈ normalizer (E e : Set G) ⊓ centralizer ({z} : Set G) := by
    rw [normalizer_E_inf hH e]
    exact map_mono (comap_mono Kbar_le_normalizer_Ebar) hx
  exact h.1

theorem E_inf_K : E e ⊓ K e = ⊥ := by
  rw [E, K, ← map_inf_eq _ _ _ (centralizer _).subtype_injective]
  suffices h : liftOddSubgroup e Ebar ⊓ Kbar.comap (proj e) = ⊥ by rw [h, Subgroup.map_bot]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxE, hxK⟩ := mem_inf.mp hx
  rw [hH.mem_liftOddSubgroup_iff e JankoPTwoThree.odd_card_Ebar] at hxE
  have h1 : proj e x = 1 := by
    have h : proj e x ∈ Ebar ⊓ Kbar := ⟨hxE.1, hxK⟩
    rwa [Ebar_inf_Kbar, mem_bot] at h
  exact mem_bot.mpr (hH.eq_one_of_mem_center_of_odd ((proj_eq_one_iff e).mp h1) hxE.2)

theorem sup_K_le : E e ⊔ K e ≤ normalizer (E e : Set G) ⊓ centralizer ({z} : Set G) :=
  sup_le (le_inf le_normalizer (E_le e)) (le_inf (K_le_normalizer hH e) (K_le e))

theorem card_sup_K : Nat.card (E e ⊔ K e : Subgroup G) = 27 * Nat.card (K e) := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    (K_le_normalizer hH e) (disjoint_iff.mpr (E_inf_K hH e)), card_E hH e]

include hz

theorem card_K : Nat.card (K e) = 48 := by
  have hK2 : Nat.card (K e) = 2 * Nat.card Kbar := by
    rw [K, card_map_of_injective (centralizer _).subtype_injective, hH.card_comap_proj e]
  have hpos : 0 < Nat.card (K e) := by
    rw [hK2]
    exact Nat.mul_pos (by norm_num) Nat.card_pos
  have h16 : 16 ∣ Nat.card (K e) := card_L hz hH e ▸ card_dvd_of_le (L_le_K e)
  have h3 : 3 ∣ Nat.card (K e) := orderOf_ρ hH e ▸ Subgroup.orderOf_dvd_natCard _ (ρ_mem_K hH e)
  have := finite_inf_centralizer hH (normalizer (E e : Set G))
  have hle : 27 * Nat.card (K e) ≤ 1296 := by
    rw [← card_sup_K hH e]
    exact (card_le_of_le (sup_K_le hH e)).trans (card_normalizer_E_le hH e)
  omega

theorem normalizer_E : normalizer (E e : Set G) ⊓ centralizer ({z} : Set G) = E e ⊔ K e := by
  have := finite_inf_centralizer hH (normalizer (E e : Set G))
  refine (Subgroup.eq_of_le_of_card_ge (sup_K_le hH e) ?_).symm
  rw [card_sup_K hH e, card_K hz hH e]
  exact card_normalizer_E_le hH e

theorem card_ne_three :
    ∀ B : Subgroup G, B ≤ K e → K e ≤ normalizer (B : Set G) → Nat.card B ≠ 3 := by
  intro B hBK hKB hB3
  have hρ3 : Nat.card (zpowers (ρ e)) = 3 := by rw [Nat.card_zpowers, orderOf_ρ hH e]
  have : Finite (zpowers (ρ e)) := Nat.finite_of_card_ne_zero (by rw [hρ3]; norm_num)
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hB3]; norm_num)
  have hρK : zpowers (ρ e) ≤ K e := zpowers_le.mpr (ρ_mem_K hH e)
  by_cases hdisj : Disjoint B (zpowers (ρ e))
  · have h9 := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B
      (zpowers (ρ e)) (hρK.trans hKB) hdisj
    have hdvd := card_dvd_of_le (sup_le hBK hρK)
    rw [h9, hB3, hρ3, card_K hz hH e] at hdvd
    exact absurd hdvd (by norm_num)
  · have hdvd : Nat.card (B ⊓ zpowers (ρ e) : Subgroup G) ∣ 3 :=
      hB3 ▸ card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact hdisj (disjoint_iff.mpr (Subgroup.card_eq_one.mp h))
    · have h1 : B ⊓ zpowers (ρ e) = B :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hB3])
      have h2 : B ⊓ zpowers (ρ e) = zpowers (ρ e) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hρ3])
      have ht := hKB (t_mem_K e)
      rw [← h1, h2] at ht
      exact t_notMem_normalizer_zpowers_ρ hH e ht

theorem K_inf_normalizer_P₁ :
    K e ⊓ normalizer (zpowers (s₁ e) : Set G) = closure ({ℓ e, t e} : Set G) := by
  have hK := card_K hz hH e
  have hL := card_L hz hH e
  have : Finite (K e) := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Finite (K e ⊓ normalizer (zpowers (s₁ e) : Set G) : Subgroup G) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : K e ⊓
      normalizer (zpowers (s₁ e) : Set G) ≤ _))
  have hle : closure ({ℓ e, t e} : Set G) ≤ K e ⊓ normalizer (zpowers (s₁ e) : Set G) :=
    le_inf (L_le_K e) (L_le_normalizer_P₁ hH e)
  have hd1 := card_dvd_of_le hle
  have hd2 := card_dvd_of_le (inf_le_left : K e ⊓ normalizer (zpowers (s₁ e) : Set G) ≤ _)
  rw [hL] at hd1
  rw [hK] at hd2
  have hne : Nat.card (K e ⊓ normalizer (zpowers (s₁ e) : Set G) : Subgroup G) ≠ 48 := by
    intro h48
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : K e ⊓
      normalizer (zpowers (s₁ e) : Set G) ≤ _) (by rw [h48, hK])
    exact ρ_notMem_normalizer_P₁ hH e ((inf_eq_left.mp heq) (ρ_mem_K hH e))
  have hne32 : Nat.card (K e ⊓ normalizer (zpowers (s₁ e) : Set G) : Subgroup G) ≠ 32 := by
    intro h32
    rw [h32] at hd2
    exact absurd hd2 (by norm_num)
  have hpos := Nat.pos_of_dvd_of_pos hd2 (by norm_num)
  have hle48 := Nat.le_of_dvd (by norm_num) hd2
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem normalizer_E_inf_P₁ : normalizer (E e : Set G) ⊓ normalizer (zpowers (s₁ e) : Set G) ⊓
    centralizer ({z} : Set G) = E e ⊔ closure ({ℓ e, t e} : Set G) := by
  apply le_antisymm
  · rintro x ⟨⟨hxE, hxP⟩, hxz⟩
    have hx : x ∈ E e ⊔ K e := by
      rw [← normalizer_E hz hH e]
      exact ⟨hxE, hxz⟩
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ (K_le_normalizer hH e)] at hx
    obtain ⟨a, ha, k, hk, rfl⟩ := hx
    have hkP : k ∈ normalizer (zpowers (s₁ e) : Set G) := by
      have h := mul_mem (inv_mem (E_le_normalizer_P₁ hH e ha)) hxP
      rwa [inv_mul_cancel_left] at h
    have hkL : k ∈ closure ({ℓ e, t e} : Set G) := by
      rw [← K_inf_normalizer_P₁ hz hH e]
      exact ⟨hk, hkP⟩
    exact mul_mem_sup ha hkL
  · exact sup_le (le_inf (le_inf le_normalizer (E_le_normalizer_P₁ hH e)) (E_le e))
      (le_inf (le_inf ((L_le_K e).trans (K_le_normalizer hH e)) (L_le_normalizer_P₁ hH e))
        ((L_le_K e).trans (K_le e)))

omit hz in
theorem le_normalizer_E : ∀ X : Subgroup G, X ≤ centralizer ({z} : Set G) → Odd (Nat.card X) →
    E e ≤ X → K e ≤ normalizer (X : Set G) → X ≤ normalizer (E e : Set G) := by
  intro X hXH hodd hEX _
  have hXH' : Odd (Nat.card (X.subgroupOf (centralizer ({z} : Set G)))) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hXH).toEquiv]
  have hEbar : Ebar ≤ (X.subgroupOf (centralizer ({z} : Set G))).map (proj e) := by
    rw [← hH.map_liftOddSubgroup e JankoPTwoThree.odd_card_Ebar]
    exact map_mono fun y hy => mem_subgroupOf.mpr (hEX ⟨y, hy, rfl⟩)
  have hY := JankoPerm.le_normalizer_Ebar_of_odd (hH.odd_card_map_proj e hXH') hEbar
  intro x hx
  have hmem : x ∈ normalizer (E e : Set G) ⊓ centralizer ({z} : Set G) := by
    rw [normalizer_E_inf hH e]
    exact ⟨⟨x, hXH hx⟩, hY ⟨⟨x, hXH hx⟩, mem_subgroupOf.mpr hx, rfl⟩, rfl⟩
  exact hmem.1

end Janko

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
