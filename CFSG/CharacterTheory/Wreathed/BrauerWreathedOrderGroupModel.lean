module

public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderGroupSupport
public import CFSG.CharacterTheory.Wreathed.SplitCyclicActorSupport
public import CFSG.CharacterTheory.Wreathed.InvertedLocalSylowSupport
public import CFSG.Walter.ReeOrder.JT.Basic

public section

namespace CFSG.Wreathed.BrauerWreathedOrder

open scoped Pointwise
open CFSG.Wreathed.BrauerWong

universe u

variable {G : Type u} [Group G]

theorem modelHom_z_not_mem_modelBase {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.z (2 ^ n)) ∉ modelBase S e := by
  rw [mem_modelBase_iff S e, Original.z, element_mem_base]
  decide

theorem modelHom_x2_mem_modelBase {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.x2 (2 ^ n)) ∈ modelBase S e := by
  rw [mem_modelBase_iff S e, Original.x2_eq, element_mem_base]

theorem modelHom_t_half_mul_x2 {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) *
        wreathModelHom S e (Original.x2 (2 ^ n)) =
      wreathModelHom S e (Original.x (2 ^ n)) := by
  rw [← map_mul, x_eq_element, x2_eq_element, t_half_eq_element, element_base_mul, zero_add,
    add_zero]

theorem card_sylow_model {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (S : Subgroup G) = 2 * (2 ^ n) ^ 2 := by
  rw [Nat.card_congr e.toEquiv, card_wreath]

variable [Finite G]

theorem base_relIndex_cases (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (Subgroup.centralizer (modelBase S e : Set G)).relIndex
        (Subgroup.normalizer (modelBase S e : Set G)) = 2 ∨
      ((Subgroup.centralizer (modelBase S e : Set G)).relIndex
          (Subgroup.normalizer (modelBase S e : Set G)) = 6 ∧
        Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
          (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
            (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3))) := by
  rw [relIndex_eq_card_quotient]
  rcases modelBaseNormalizerQuotient_alternatives n (by omega) S e with h | h
  · exact Or.inl h
  · right
    refine ⟨?_, h⟩
    obtain ⟨esix⟩ := h
    rw [Nat.card_congr esix.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl

theorem vSym3_of_swap_conj (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (h : ∃ g ∈ Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G),
      g⁻¹ * wreathModelHom S e (Original.z (2 ^ n)) * g =
        wreathModelHom S e (Original.x2 (2 ^ n))) :
    Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3)) := by
  rcases modelVNormalizerQuotient_alternatives n hn S e with hv2 | hv6
  · exfalso
    obtain ⟨g, -, hg⟩ := h
    have hconj : IsConj (wreathModelHom S e (Original.z (2 ^ n)))
        (wreathModelHom S e (Original.x2 (2 ^ n))) :=
      isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]; exact hg⟩
    have hsw := modelSwapValue_conjugate_eq_of_v_order_two n hn S e hv2 _ _
      (wreathModelHom_mem S e _) (wreathModelHom_mem S e _) hconj
    rw [(modelSwapValue_eq_one_iff S e _ (wreathModelHom_mem S e _)).mpr
      (modelHom_x2_mem_modelBase S e)] at hsw
    exact modelHom_z_not_mem_modelBase S e
      ((modelSwapValue_eq_one_iff S e _ (wreathModelHom_mem S e _)).mp hsw)
  · exact hv6

theorem swap_conj_of_vSym3 (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    ∃ g ∈ Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G),
      g⁻¹ * wreathModelHom S e (Original.z (2 ^ n)) * g =
        wreathModelHom S e (Original.x2 (2 ^ n)) := by
  obtain ⟨h, hhN, hh⟩ := exists_vNormalizer_swap_eq_x2 n hn S e hsix
  refine ⟨h, ?_, hh⟩
  have hC := modelVNormalizer_le_center_centralizer n hn S e hhN
  have hxZ : wreathModelHom S e (Original.x (2 ^ n)) ∈
      (Original.Z (2 ^ n)).map (wreathModelHom S e) :=
    Subgroup.mem_map_of_mem _ ((Original.Z (2 ^ n)).pow_mem (Subgroup.mem_zpowers _) _)
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact (Subgroup.mem_centralizer_iff.mp hC _ hxZ).symm

theorem normal_two_complement_of_order_two (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hb2 : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    (hv2 : Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) = 2) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧ ∃ k : ℕ, N.index = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFB := model_base_contains_focal_of_v_order_two n hn S e hv2
  have hFY := modelY_contains_focal_of_base_order_two n hn S e hb2
  have hBY : modelBase S e ⊓ modelY S e =
      Subgroup.zpowers (wreathModelHom S e (Original.r (2 ^ n))) := by
    rw [modelBase, modelY, ← Subgroup.map_inf_eq _ _ _ (wreathModelHom_injective S e),
      SplitCyclicActor.base_inf_quaternion_eq_zpowers n hn, MonoidHom.map_zpowers]
  have hFcyc : IsCyclic (S : Subgroup G).focalSubgroup := by
    have hle : (S : Subgroup G).focalSubgroup ≤
        Subgroup.zpowers (wreathModelHom S e (Original.r (2 ^ n))) :=
      hBY ▸ le_inf hFB hFY
    exact Subgroup.isCyclic_of_le hle
  obtain ⟨hDn, hDidx, hDinf, -⟩ := transferFocal_ker_spec S
  have := hDn
  obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal S (N := (S : Subgroup G).transferFocal.ker)
  have hQcyc : IsCyclic Q := by
    have e1 : (Q : Subgroup (S : Subgroup G).transferFocal.ker) ≃*
        (S : Subgroup G).focalSubgroup :=
      ((MulEquiv.subgroupCongr hQ).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)).trans
        (MulEquiv.subgroupCongr hDinf)
    exact e1.isCyclic.mpr hFcyc
  exact SplitCyclicActor.normal_two_complement_of_normal_cyclic_sylow _ hDidx Q hQcyc

theorem index_two_of_focal_le (S : Sylow 2 G) (X : Subgroup G)
    (hFX : (S : Subgroup G).focalSubgroup ≤ X) (hX : Nat.card X < Nat.card (S : Subgroup G)) :
    ∃ H : Subgroup G, H.Normal ∧ H.index = 2 := by
  apply CFSG.Semidihedral.FocalTransfer.exists_index_two_of_focal_ne S
  intro hF
  rw [hF] at hFX
  exact absurd (Subgroup.card_le_of_le hFX) (not_le.mpr hX)

theorem index_two_of_base_order_two (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hb2 : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2) :
    ∃ H : Subgroup G, H.Normal ∧ H.index = 2 := by
  refine index_two_of_focal_le S (modelY S e)
    (modelY_contains_focal_of_base_order_two n hn S e hb2) ?_
  rw [modelY_card n hn S e, card_sylow_model S e, ← pow_mul, ← pow_succ']
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem index_two_of_v_order_two (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hv2 : Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) = 2) :
    ∃ H : Subgroup G, H.Normal ∧ H.index = 2 := by
  refine index_two_of_focal_le S (modelBase S e)
    (model_base_contains_focal_of_v_order_two n hn S e hv2) ?_
  rw [modelBase, Subgroup.card_map_of_injective (wreathModelHom_injective S e), card_base,
    card_sylow_model S e]
  have : 0 < (2 ^ n) ^ 2 := by positivity
  omega

theorem three_power_cycle_of_base_sym3 (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hbase : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3))) :
    ∃ Y : G, (∃ k : ℕ, orderOf Y = 3 ^ k) ∧
      Y⁻¹ * wreathModelHom S e (Original.x (2 ^ n)) * Y =
          wreathModelHom S e (Original.x2 (2 ^ n)) ∧
      Y⁻¹ * wreathModelHom S e (Original.x2 (2 ^ n)) * Y =
          wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) ∧
      Y⁻¹ * wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) * Y =
          wreathModelHom S e (Original.x (2 ^ n)) := by
  obtain ⟨Y, -, h1, h2, h3⟩ := exists_base_three_cycle hn S e hbase
  exact exists_three_power_cycle _ _ _ Y h1 h2 h3

theorem all_involutions_conjugate_of_conj (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hx : IsConj (wreathModelHom S e (Original.x (2 ^ n)))
      (wreathModelHom S e (Original.x2 (2 ^ n))))
    (hz : IsConj (wreathModelHom S e (Original.z (2 ^ n)))
      (wreathModelHom S e (Original.x2 (2 ^ n)))) :
    ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  have hall : ∀ u : G, orderOf u = 2 → IsConj u (wreathModelHom S e (Original.x2 (2 ^ n))) := by
    intro u hu
    have hp : IsPGroup 2 (Subgroup.zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
    obtain ⟨k, hk⟩ := exists_conj_mem_sylow S hp
    have hwS := hk u (Subgroup.mem_zpowers u)
    have huw : IsConj u (k⁻¹ * u * k) := isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]⟩
    obtain ⟨w, hw⟩ := exists_wreathModelHom_eq S e hwS
    have hworder : orderOf w = 2 := by
      rw [← orderOf_injective _ (wreathModelHom_injective S e), hw,
        show k⁻¹ * u * k = MulAut.conj k⁻¹ u by simp, MulEquiv.orderOf_eq]
      exact hu
    have hwy : IsConj (wreathModelHom S e w) (wreathModelHom S e (Original.x2 (2 ^ n))) := by
      rcases hstr.involution_classes w hworder with h | h | h
      · exact ((wreathModelHom S e).map_isConj h).symm.trans hx
      · exact ((wreathModelHom S e).map_isConj h).symm
      · exact ((wreathModelHom S e).map_isConj h).symm.trans hz
    rw [hw] at hwy
    exact huw.trans hwy
  intro u v hu hv
  exact (hall u hu).trans (hall v hv).symm

theorem order_formula_of_base_order_two (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hb2 : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2) :
    Nat.card G * Nat.card (Subgroup.centralizer
        ((Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
          wreathModelHom S e (Original.x2 (2 ^ n))} : Subgroup G) : Set G)) ^ 2 =
      Nat.card (Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G)) *
        Nat.card (Subgroup.centralizer
          ({wreathModelHom S e (Original.x2 (2 ^ n))} : Set G)) ^ 2 := by
  set J := wreathModelHom S e (Original.x (2 ^ n)) with hJdef
  set J₁ := wreathModelHom S e (Original.x2 (2 ^ n)) with hJ₁def
  set J₂ := wreathModelHom S e (Original.t (2 ^ n) ^ (2 ^ n / 2)) with hJ₂def
  set z := wreathModelHom S e (Original.z (2 ^ n)) with hzdef
  set O := CFSG.pPrimeCore 2 G with hOdef
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hON : ∀ g : G, g ∈ Subgroup.normalizer (O : Set G) := by
    intro g
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  have hsq : ∀ u : G, orderOf u = 2 → u * u = 1 := by
    intro u hu
    rw [← pow_two, ← hu]
    exact pow_orderOf_eq_one u
  have hne : ∀ u : G, orderOf u = 2 → u ≠ 1 := by
    rintro u hu rfl
    rw [orderOf_one] at hu
    omega
  have hJ2 : orderOf J = 2 := by
    rw [orderOf_injective _ (wreathModelHom_injective S e)]
    exact hstr.involution_orders.1
  have hJ₁2 : orderOf J₁ = 2 := by
    rw [orderOf_injective _ (wreathModelHom_injective S e)]
    exact hstr.involution_orders.2.1
  have hJJ : J * J = 1 := hsq J hJ2
  have hJ₁J₁ : J₁ * J₁ = 1 := hsq J₁ hJ₁2
  have hconjz : z⁻¹ * J₁ * z = J₂ := modelHom_swap_conj_x2 S e
  have hJ₂2 : orderOf J₂ = 2 := by
    rw [← hconjz, show z⁻¹ * J₁ * z = MulAut.conj z⁻¹ J₁ by simp, MulEquiv.orderOf_eq]
    exact hJ₁2
  have hJ₂J₂ : J₂ * J₂ = 1 := hsq J₂ hJ₂2
  have h12 : J₁ * J₂ = J := modelHom_x2_mul_t_half S e
  have h21 : J₂ * J₁ = J := modelHom_t_half_mul_x2 S e
  have hJ₁1 : J₁ ≠ 1 := hne J₁ hJ₁2
  have hJ₂1 : J₂ ≠ 1 := hne J₂ hJ₂2
  have hJ₁J₂ : J₁ ≠ J₂ := modelHom_x2_ne_t_half S e (by omega)
  have hJJ₁ : J * J₁ = J₁ * J := by
    calc J * J₁ = J₂ * J₁ * J₁ := by rw [h21]
      _ = J₂ * (J₁ * J₁) := by group
      _ = J₂ := by rw [hJ₁J₁, mul_one]
      _ = J₁ * J₁ * J₂ := by rw [hJ₁J₁, one_mul]
      _ = J₁ * (J₁ * J₂) := by group
      _ = J₁ * J := by rw [h12]
  have hJZ : J ∈ modelCenter S e :=
    ⟨_, (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _, rfl⟩
  have hfac := eq_centralizer_mul_pPrimeCore_of_base_order_two S e hn hb2 hJZ
  have hcen : ∀ g : G, g * J * g⁻¹ * J⁻¹ ∈ O := by
    intro g
    obtain ⟨c, hc, o, ho, rfl⟩ := hfac g
    have hcJ : c * J = J * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have h1 : J * o⁻¹ * J⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hON J) o⁻¹).mp (O.inv_mem ho)
    have h2 : o * (J * o⁻¹ * J⁻¹) ∈ O := O.mul_mem ho h1
    have h3 := (Subgroup.mem_normalizer_iff.mp (hON c) _).mp h2
    have heq : c * o * J * (c * o)⁻¹ * J⁻¹ = c * (o * (J * o⁻¹ * J⁻¹)) * c⁻¹ := by
      have hJc : J⁻¹ = c * J⁻¹ * c⁻¹ := by
        calc J⁻¹ = c * (c⁻¹ * J⁻¹ * c) * c⁻¹ := by group
          _ = c * J⁻¹ * c⁻¹ := by
            rw [show c⁻¹ * J⁻¹ * c = J⁻¹ by
              calc c⁻¹ * J⁻¹ * c = (c⁻¹ * J * c)⁻¹ := by group
                _ = J⁻¹ := by
                  rw [show c⁻¹ * J * c = J by
                    calc c⁻¹ * J * c = c⁻¹ * (J * c) := by group
                      _ = c⁻¹ * (c * J) := by rw [hcJ]
                      _ = J := by group]]
      calc c * o * J * (c * o)⁻¹ * J⁻¹ = c * o * J * o⁻¹ * c⁻¹ * J⁻¹ := by group
        _ = c * o * J * o⁻¹ * c⁻¹ * (c * J⁻¹ * c⁻¹) := by rw [← hJc]
        _ = c * (o * (J * o⁻¹ * J⁻¹)) * c⁻¹ := by group
    rw [heq]
    exact h3
  have hJO : Subgroup.centralizer ({J} : Set G) ⊔ O = ⊤ := by
    apply eq_top_iff.mpr
    intro g _
    obtain ⟨c, hc, o, ho, rfl⟩ := hfac g
    exact Subgroup.mul_mem_sup hc ho
  have hrelJ : O.relIndex (Subgroup.centralizer ({J} : Set G)) = O.index := by
    rw [← Subgroup.relIndex_sup_right, hJO, Subgroup.relIndex_top_right]
  have hcount1 : Nat.card G * Nat.card (O ⊓ Subgroup.centralizer ({J} : Set G) : Subgroup G) =
      Nat.card (Subgroup.centralizer ({J} : Set G)) * Nat.card O := by
    rw [← O.card_mul_index, ← Subgroup.relIndex_mul_card O
      (Subgroup.centralizer ({J} : Set G)), hrelJ]
    ring
  set CD := Subgroup.centralizer ({J} : Set G) ⊓ Subgroup.centralizer ({J₁} : Set G) with hCD
  have hJ₁O : Subgroup.centralizer ({J₁} : Set G) ⊔ O = CD ⊔ O := by
    apply le_antisymm
    · apply sup_le _ le_sup_right
      intro g hg
      obtain ⟨o, ho, c, hc, rfl⟩ :=
        centralizer_mem_mul_of_central_mod O hOodd hJJ hcen hJJ₁ hg
      exact (sup_comm CD O) ▸ Subgroup.mul_mem_sup ho.1 hc
    · exact sup_le_sup_right inf_le_right O
  have hrelJ₁ : O.relIndex (Subgroup.centralizer ({J₁} : Set G)) = O.relIndex CD := by
    rw [← Subgroup.relIndex_sup_right, hJ₁O, Subgroup.relIndex_sup_right]
  have hcount2 : Nat.card (Subgroup.centralizer ({J₁} : Set G)) *
      Nat.card (O ⊓ CD : Subgroup G) =
      Nat.card (O ⊓ Subgroup.centralizer ({J₁} : Set G) : Subgroup G) * Nat.card CD := by
    rw [← Subgroup.relIndex_mul_card O (Subgroup.centralizer ({J₁} : Set G)),
      ← Subgroup.relIndex_mul_card O CD, hrelJ₁]
    ring
  have hcount3 : Nat.card (O ⊓ Subgroup.centralizer ({J₂} : Set G) : Subgroup G) =
      Nat.card (O ⊓ Subgroup.centralizer ({J₁} : Set G) : Subgroup G) := by
    have h := InvertedLocalSylow.map_conj_inf_centralizer O z⁻¹ J₁ (hON z⁻¹)
    rw [inv_inv, hconjz] at h
    rw [← h, Subgroup.card_map_of_injective (MulAut.conj z⁻¹).injective]
  have hBW := CFSG.Walter.JT.card_mul_card_sq_eq_mul hJ₁J₁ hJ₂J₂ hJ₁1 hJ₂1 hJ₁J₂
    (show Commute J₁ J₂ from (h12.trans h21.symm)) O (hON J₁) (hON J₂) hOodd
  rw [h12] at hBW
  have hOD : O ⊓ Subgroup.centralizer ({J₁} : Set G) ⊓ Subgroup.centralizer ({J₂} : Set G) =
      O ⊓ CD := by
    ext g
    simp only [Subgroup.mem_inf, hCD, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨hgO, hg1⟩, hg2⟩
      refine ⟨hgO, ?_, hg1⟩
      rw [← h12]
      calc g * (J₁ * J₂) = (g * J₁) * J₂ := by group
        _ = (J₁ * g) * J₂ := by rw [hg1]
        _ = J₁ * (g * J₂) := by group
        _ = J₁ * (J₂ * g) := by rw [hg2]
        _ = J₁ * J₂ * g := by group
    · rintro ⟨hgO, hgJ, hg1⟩
      refine ⟨⟨hgO, hg1⟩, ?_⟩
      have hJ₂eq : J₂ = J₁ * J := by
        rw [← h12]
        calc J₂ = J₁ * J₁ * J₂ := by rw [hJ₁J₁, one_mul]
          _ = J₁ * (J₁ * J₂) := by group
      rw [hJ₂eq]
      calc g * (J₁ * J) = (g * J₁) * J := by group
        _ = (J₁ * g) * J := by rw [hg1]
        _ = J₁ * (g * J) := by group
        _ = J₁ * (J * g) := by rw [hgJ]
        _ = J₁ * J * g := by group
  rw [hOD] at hBW
  have hcD : Subgroup.centralizer ((Subgroup.closure {J, J₁} : Subgroup G) : Set G) = CD := by
    rw [Subgroup.centralizer_closure, centralizer_pair_eq]
  rw [hcD]
  exact order_formula_arith _ _ _ _ _ _ _ _ _ Nat.card_pos Nat.card_pos hcount1 hcount2
    hcount3 hBW

end CFSG.Wreathed.BrauerWreathedOrder
