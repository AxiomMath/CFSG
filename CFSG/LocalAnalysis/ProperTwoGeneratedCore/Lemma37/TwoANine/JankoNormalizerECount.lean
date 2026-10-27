module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoNormalizerEL
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoRegular

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace JankoNormalizerE

theorem card_le_card_mul_card_inf_centralizer {G : Type*} [Group G] (X : Subgroup G) (s : G)
    (T : Set G) [Finite T] (hT : ∀ x ∈ X, x * s * x⁻¹ ∈ T) :
    Nat.card X ≤ Nat.card T * Nat.card (X ⊓ centralizer ({s} : Set G) : Subgroup G) := by
  set S := (centralizer ({s} : Set G)).subgroupOf X
  have h1 : Nat.card S * S.index = Nat.card X := S.card_mul_index
  have h2 : Nat.card S = Nat.card (X ⊓ centralizer ({s} : Set G) : Subgroup G) := by
    rw [show S = (centralizer ({s} : Set G) ⊓ X).subgroupOf X from
      (inf_subgroupOf_right _ _).symm, inf_comm]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  let f : X ⧸ S → T := fun q => Quotient.liftOn' q
    (fun x => (⟨(x : G) * s * (x : G)⁻¹, hT x x.2⟩ : T)) (by
      intro a b hab
      have hc := mem_centralizer_singleton_iff.mp
        (mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab))
      apply Subtype.ext
      simp only [coe_mul, coe_inv] at hc ⊢
      calc (a : G) * s * (a : G)⁻¹ = (a : G) * ((a : G)⁻¹ * b * s) * (b : G)⁻¹ := by
            rw [hc]; group
        _ = (b : G) * s * (b : G)⁻¹ := by group)
  have hf : Function.Injective f := by
    intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with | H a => ?_
    induction q₂ using QuotientGroup.induction_on with | H b => ?_
    have h' : (a : G) * s * (a : G)⁻¹ = (b : G) * s * (b : G)⁻¹ := congrArg Subtype.val h
    refine QuotientGroup.eq.mpr (mem_subgroupOf.mpr (mem_centralizer_singleton_iff.mpr ?_))
    simp only [coe_mul, coe_inv]
    calc (a : G)⁻¹ * b * s = (a : G)⁻¹ * ((b : G) * s * (b : G)⁻¹) * b := by group
      _ = (a : G)⁻¹ * ((a : G) * s * (a : G)⁻¹) * b := by rw [h']
      _ = s * ((a : G)⁻¹ * b) := by group
  have h3 : S.index ≤ Nat.card T := Nat.card_le_card_of_injective f hf
  calc Nat.card X = Nat.card S * S.index := h1.symm
    _ ≤ Nat.card S * Nat.card T := Nat.mul_le_mul_left _ h3
    _ = Nat.card T * Nat.card (X ⊓ centralizer ({s} : Set G) : Subgroup G) := by
      rw [h2, mul_comm]

theorem card_centralizer_conj_inf {G : Type*} [Group G] (k a b : G) (hb : k * b * k⁻¹ = b) :
    Nat.card (centralizer ({k * a * k⁻¹} : Set G) ⊓ centralizer ({b} : Set G) : Subgroup G) =
      Nat.card (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) : Subgroup G) := by
  conv_lhs => rw [← hb]
  rw [JankoInvolution.centralizer_conj_eq, JankoInvolution.centralizer_conj_eq,
    ← map_inf_eq _ _ _ (MulAut.conj k).injective, card_map_of_injective (MulAut.conj k).injective]

open Janko

variable {G : Type*} [Group G] {z : G} (hz : orderOf z = 2)
  (hH : IsTwoANine (centralizer ({z} : Set G)))
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))

@[expose] noncomputable def ρ : G :=
  (liftOdd e ρbar : centralizer ({z} : Set G))

theorem odd_orderOf_ρbar : Odd (orderOf ρbar) := by
  rw [orderOf_ρbar]
  exact ⟨1, rfl⟩

theorem odd_orderOf_sbar₁ : Odd (orderOf sbar₁) := by
  rw [orderOf_sbar₁]
  exact ⟨1, rfl⟩

theorem proj_eq_of_coe_eq {u v : centralizer ({z} : Set G)} (h : (u : G) = v) :
    proj e u = proj e v := by
  rw [Subtype.ext h]

theorem t_mem_K : t e ∈ K e :=
  (JankoF.coe_mem_map_comap_iff e _).mpr (by rw [proj_someLift]; exact tbar_mem_Kbar)

theorem ℓ_mem_K : ℓ e ∈ K e :=
  (JankoF.coe_mem_map_comap_iff e _).mpr (by rw [proj_someLift]; exact ℓbar_mem_Kbar)

include hH

theorem ρ_mem_K : ρ e ∈ K e :=
  (JankoF.coe_mem_map_comap_iff e _).mpr (by
    rw [hH.proj_liftOdd e odd_orderOf_ρbar]
    exact ρbar_mem_Kbar)

theorem orderOf_ρ : orderOf (ρ e) = 3 := by
  rw [ρ, Subgroup.orderOf_coe, hH.orderOf_liftOdd e odd_orderOf_ρbar, orderOf_ρbar]

theorem ρ_ne_one : ρ e ≠ 1 := fun h => by
  have h3 := orderOf_ρ hH e
  rw [h, orderOf_one] at h3
  exact absurd h3 (by norm_num)

theorem ρ_notMem_normalizer_P₁ : ρ e ∉ normalizer (zpowers (s₁ e) : Set G) := by
  intro hN
  have hmem : ρ e * s₁ e * (ρ e)⁻¹ ∈ zpowers (s₁ e) :=
    (mem_normalizer_iff.mp hN _).mp (mem_zpowers _)
  have hρ := hH.proj_liftOdd e odd_orderOf_ρbar
  have hs := hH.proj_liftOdd e odd_orderOf_sbar₁
  rcases JankoPTwoThree.eq_or_eq_inv_of_mem_zpowers (orderOf_s₁ hH e) hmem
    (JankoPTwoThree.conj_ne_one (s₁_ne_one hH e)) with h | h
  · have h' := proj_eq_of_coe_eq e (u := liftOdd e ρbar * liftOdd e sbar₁ * (liftOdd e ρbar)⁻¹)
      (v := liftOdd e sbar₁) h
    rw [map_mul, map_mul, map_inv, hρ, hs] at h'
    exact ρbar_conj_sbar₁_ne.1 h'
  · have h' := proj_eq_of_coe_eq e (u := liftOdd e ρbar * liftOdd e sbar₁ * (liftOdd e ρbar)⁻¹)
      (v := (liftOdd e sbar₁)⁻¹) h
    rw [map_mul, map_mul, map_inv, map_inv, hρ, hs] at h'
    exact ρbar_conj_sbar₁_ne.2 h'

theorem t_notMem_normalizer_zpowers_ρ : t e ∉ normalizer (zpowers (ρ e) : Set G) := by
  intro hN
  have hmem : t e * ρ e * (t e)⁻¹ ∈ zpowers (ρ e) :=
    (mem_normalizer_iff.mp hN _).mp (mem_zpowers _)
  have hρ := hH.proj_liftOdd e odd_orderOf_ρbar
  rcases JankoPTwoThree.eq_or_eq_inv_of_mem_zpowers (orderOf_ρ hH e) hmem
    (JankoPTwoThree.conj_ne_one (ρ_ne_one hH e)) with h | h
  · have h' := proj_eq_of_coe_eq e (u := someLift e tbar * liftOdd e ρbar * (someLift e tbar)⁻¹)
      (v := liftOdd e ρbar) h
    rw [map_mul, map_mul, map_inv, hρ, proj_someLift] at h'
    exact tbar_conj_ρbar_ne.1 h'
  · have h' := proj_eq_of_coe_eq e (u := someLift e tbar * liftOdd e ρbar * (someLift e tbar)⁻¹)
      (v := (liftOdd e ρbar)⁻¹) h
    rw [map_mul, map_mul, map_inv, map_inv, hρ, proj_someLift] at h'
    exact tbar_conj_ρbar_ne.2 h'

theorem normalizer_E_inf : normalizer (E e : Set G) ⊓ centralizer ({z} : Set G) =
    ((normalizer (Ebar : Set (alternatingGroup (Fin 9)))).comap (proj e)).map
      (centralizer ({z} : Set G)).subtype := by
  rw [E, normalizer_map_inf_eq_map_subtype,
    hH.normalizer_liftOddSubgroup e JankoPTwoThree.odd_card_Ebar]

theorem s₁_mem_E : s₁ e ∈ E e := by
  rw [E_eq_closure hH e]
  exact subset_closure (by simp)

theorem E_le_normalizer_P₁ : E e ≤ normalizer (zpowers (s₁ e) : Set G) := fun a ha =>
  centralizer_le_normalizer _ (by
    rw [centralizer_zpowers_s₁, mem_centralizer_singleton_iff]
    exact E_comm hH e a ha _ (s₁_mem_E hH e))

theorem finite_inf_centralizer (X : Subgroup G) : Finite (X ⊓ centralizer ({z} : Set G) :
    Subgroup G) := by
  have := hH.finite
  exact Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right : X ⊓
    centralizer ({z} : Set G) ≤ _))

theorem card_normalizer_E_le :
    Nat.card (normalizer (E e : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) ≤ 1296 := by
  set T : Set G := {x | x ∈ E e ∧
    Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162}
  have hT8 : Nat.card T = 8 := card_type_s₃_E hH e
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT8]; norm_num)
  have hT : ∀ x ∈ normalizer (E e : Set G) ⊓ centralizer ({z} : Set G), x * s₃ e * x⁻¹ ∈ T := by
    rintro x ⟨hxE, hxz⟩
    refine ⟨(mem_normalizer_iff.mp hxE _).mp (s₃_mem_E hH e), ?_⟩
    have hz' : x * z * x⁻¹ = z := by
      rw [mem_centralizer_singleton_iff.mp hxz, mul_inv_cancel_right]
    rw [card_centralizer_conj_inf x (s₃ e) z hz', card_centralizer_s₃ hH e]
  have h162 := card_centralizer_s₃ hH e
  have : Finite (centralizer ({s₃ e} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) :=
    Nat.finite_of_card_ne_zero (by rw [h162]; norm_num)
  have hle : Nat.card (normalizer (E e : Set G) ⊓ centralizer ({z} : Set G) ⊓
      centralizer ({s₃ e} : Set G) : Subgroup G) ≤ 162 := by
    rw [← h162]
    exact card_le_of_le (le_inf inf_le_right (inf_le_left.trans inf_le_right))
  calc Nat.card (normalizer (E e : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G)
      ≤ Nat.card T * Nat.card (normalizer (E e : Set G) ⊓ centralizer ({z} : Set G) ⊓
        centralizer ({s₃ e} : Set G) : Subgroup G) :=
        card_le_card_mul_card_inf_centralizer _ _ T hT
    _ ≤ 8 * 162 := by rw [hT8]; exact Nat.mul_le_mul_left _ hle
    _ = 1296 := by norm_num

end JankoNormalizerE

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
