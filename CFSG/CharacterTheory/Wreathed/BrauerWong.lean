module

public import CFSG.CharacterTheory.Wreathed.BrauerWongCentralizers
public import CFSG.CharacterTheory.Wreathed.BrauerWongBaseFusion
public import CFSG.CharacterTheory.Wreathed.BrauerWongBaseNormalizer
public import CFSG.CharacterTheory.Wreathed.BrauerWongMaximalOrder
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem brauer_wong_wreathed_two_element_classes [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (S₁ S₂ T : G)
    (hgen : Subgroup.closure {S₁, S₂, T} = (S : Subgroup G))
    (hcard : Nat.card (S : Subgroup G) = 2 ^ (2 * n + 1))
    (hS₁ : S₁ ^ 2 ^ n = 1) (hS₂ : S₂ ^ 2 ^ n = 1) (hT : T ^ 2 = 1)
    (hcomm : S₁ * S₂ = S₂ * S₁) (hconj : T⁻¹ * S₁ * T = S₂)
    (hH : NoAbelianTwoPowerIndexIntersection G (S : Subgroup G)) :
    let S₀ := Subgroup.closure {S₁, S₂}
    let A := S₁⁻¹ * S₂⁻¹
    let J := A ^ 2 ^ (n - 1)
    let J₁ := S₁ ^ 2 ^ (n - 1)
    let J₂ := S₂ ^ 2 ^ (n - 1)
    let D := Subgroup.closure {J, J₁}
    let R := S₁ * T
    let Q₀ := Subgroup.closure {S₁ * S₂⁻¹, T * J₁}
    let C := Subgroup.centralizer ((S : Subgroup G) : Set G)
    let E := (CFSG.pPrimeCore 2 C).map C.subtype
    (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype = Subgroup.zpowers A ∧
    (∃ φ : ↥(Subgroup.zpowers A) × ↥E ≃* ↥C, ∀ x y, (φ (x, y) : G) = x * y) ∧
    (∃ ψ : ↥(S : Subgroup G) × ↥E ≃* ↥(Subgroup.normalizer ((S : Subgroup G) : Set G)),
      ∀ x y, (ψ (x, y) : G) = x * y) ∧
    ((IsTypeI G ∧ ¬ IsTypeII G (S : Subgroup G) n) ∨
      (¬ IsTypeI G ∧ IsTypeII G (S : Subgroup G) n)) ∧
    (∀ (G₀ : Subgroup G) [G₀.Normal], G₀.index = 2 ^ n →
      Nonempty (↥((S : Subgroup G) ⊓ G₀) ≃* QuaternionGroup (2 ^ (n - 1))) →
        (S : Subgroup G) ⊓ G₀ = Q₀ ∧ IsCyclic (G ⧸ G₀)) ∧
    (∃ g ∈ Subgroup.centralizer {J}, g⁻¹ * T * g = J₁) ∧
    S₀ ≤ Subgroup.centralizer (D : Set G) ∧
    (∃ P : Sylow 2 ↥(Subgroup.centralizer (D : Set G)),
      (P : Subgroup ↥(Subgroup.centralizer (D : Set G))).map
        (Subgroup.centralizer (D : Set G)).subtype = S₀) ∧
    ((Subgroup.normalizer (D : Set G) : Set G) =
      (Subgroup.centralizer (D : Set G) : Set G) * (Subgroup.normalizer (S₀ : Set G) : Set G)) ∧
    (IsTypeI G →
      (∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) ∧
      (Subgroup.centralizer (S₀ : Set G)).relIndex (Subgroup.normalizer (S₀ : Set G)) = 6 ∧
      ∃ Y ∈ Subgroup.normalizer (S₀ : Set G),
        Y⁻¹ * J * Y = J₁ ∧ Y⁻¹ * J₁ * Y = J₂ ∧ Y⁻¹ * J₂ * Y = J ∧
        (Subgroup.normalizer (S₀ : Set G) : Set G) =
          (Subgroup.centralizer (S₀ : Set G) : Set G) * (Subgroup.closure {T, Y} : Set G)) ∧
    (IsTypeII G (S : Subgroup G) n →
      Set.ncard {c : ConjClasses G | ∃ g : G, orderOf g = 2 ∧ ConjClasses.mk g = c} = 2 ∧
      {g : G | IsConj J g} ∩ ((S : Subgroup G) : Set G) = {J} ∧
      (Subgroup.centralizer (S₀ : Set G)).relIndex (Subgroup.normalizer (S₀ : Set G)) = 2 ∧
      (Subgroup.normalizer (S₀ : Set G) : Set G) =
        (Subgroup.centralizer (S₀ : Set G) : Set G) * (Subgroup.closure {T} : Set G)) ∧
    (∀ g ∈ (S : Subgroup G), orderOf g = 2 ^ (n + 1) ↔
      ∃ a b : ℕ, Odd (a + b) ∧ g = T * S₁ ^ a * S₂ ^ b) ∧
    (∀ g ∈ (S : Subgroup G), orderOf g = 2 ^ (n + 1) →
      ∃ h : ℕ, Odd h ∧ 1 ≤ h ∧ h < 2 ^ n ∧ IsConj g (R ^ h)) ∧
    Set.ncard {g : G | ∃ h : ℕ, Odd h ∧ h < 2 ^ n ∧ g = R ^ h} = 2 ^ (n - 1) ∧
    (∀ h h' : ℕ, Odd h → h < 2 ^ n → Odd h' → h' < 2 ^ n →
      IsConj (R ^ h) (R ^ h') → h = h') ∧
    (∀ g : G, g ≠ 1 → (∃ k : ℕ, orderOf g = 2 ^ k) → orderOf g ≠ 2 ^ (n + 1) →
      ∃ x ∈ S₀, IsConj g x) ∧
    (∀ x ∈ S₀, ∀ y ∈ S₀,
      IsConj x y ↔ ∃ g ∈ Subgroup.normalizer (S₀ : Set G), g⁻¹ * x * g = y) ∧
    (∀ h : ℤ, Odd h → ∃ P : Sylow 2 ↥(Subgroup.centralizer {R ^ h}),
      (P : Subgroup ↥(Subgroup.centralizer {R ^ h})).map
        (Subgroup.centralizer {R ^ h}).subtype = Subgroup.zpowers R) ∧
    (∀ μ ∈ S₀, (¬ ∃ z ∈ Subgroup.zpowers A, IsConj μ z) →
      ∃ P : Sylow 2 ↥(Subgroup.centralizer {μ}),
        (P : Subgroup ↥(Subgroup.centralizer {μ})).map (Subgroup.centralizer {μ}).subtype = S₀) ∧
    (∀ z ∈ Subgroup.zpowers A, z ≠ 1 →
      (S : Subgroup G) ≤ Subgroup.centralizer {z} ∧
      NoAbelianTwoPowerIndexIntersection ↥(Subgroup.centralizer {z})
        ((S : Subgroup G).subgroupOf (Subgroup.centralizer {z})) ∧
      IsTypeII ↥(Subgroup.centralizer {z})
        ((S : Subgroup G).subgroupOf (Subgroup.centralizer {z})) n) ∧
    (IsTypeII G (S : Subgroup G) n → ∀ z ∈ Subgroup.zpowers A, z ≠ 1 →
      ∀ g : G, ∃ c ∈ Subgroup.centralizer {z}, ∃ o ∈ CFSG.pPrimeCore 2 G, g = c * o) ∧
    (IsTypeII G (S : Subgroup G) n →
      ∀ g : G, ∃ c ∈ Subgroup.centralizer {J}, ∃ o ∈ CFSG.pPrimeCore 2 G, g = c * o) := by
  intro S₀ A J J₁ J₂ D R Q₀ C E
  have hW : WreathGenerators n (S : Subgroup G) S₁ S₂ T :=
    ⟨hgen, hcard, hS₁, hS₂, hT, hcomm, hconj⟩
  have hn1 : 1 ≤ n := by omega
  set e := hW.equiv hn1 with he
  set φ := wreathModelHom S e with hφ
  have hs : φ (Original.s (2 ^ n)) = S₁ := hW.modelHom_s hn1
  have ht : φ (Original.t (2 ^ n)) = S₂ := hW.modelHom_t hn1
  have hz : φ (Original.z (2 ^ n)) = T := hW.modelHom_z hn1
  have hJ : φ (Original.x (2 ^ n)) = J := hW.modelHom_x hn
  have hJ₁ : φ (Original.x2 (2 ^ n)) = J₁ := hW.modelHom_x2 hn1
  have hJ₂ : φ (Original.t (2 ^ n) ^ (2 ^ n / 2)) = J₂ := hW.modelHom_t_half hn1
  have hR : φ (originalRoot (2 ^ n)) = R := by
    rw [originalRoot]
    exact hW.modelHom_root hn1
  have hB : modelBase S e = S₀ := hW.modelBase_eq hn1
  have hZ : modelCenter S e = Subgroup.zpowers A := hW.modelCenter_eq hn1
  have hY : modelY S e = Q₀ := hW.modelY_eq hn
  have hD : modelOmega S e = D := by
    rw [modelOmega, MonoidHom.map_closure, Set.image_pair]
    change Subgroup.closure {φ (Original.x (2 ^ n)), φ (Original.x2 (2 ^ n))} = _
    rw [hJ, hJ₁]
  have h2n : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  have hsix := vSym3_of_noAbelian n hn S e hH
  have hJZ : φ (Original.x (2 ^ n)) ∈ modelCenter S e :=
    ⟨_, (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _, rfl⟩
  have hJ1 : J ≠ 1 := by
    rw [← hJ, ← map_one φ]
    intro h
    have h' := wreathModelHom_injective S e h
    rw [x_eq_element, ← element_zero, element_eq_iff] at h'
    exact half_ne_zero n hn1 h'.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  ·
    rw [center_map_eq_modelCenter n hn S e, hZ]
  ·
    have h := centralizer_eq_center_prod_core n hn S e
    rw [hZ] at h
    exact h
  ·
    exact normalizer_eq_sylow_prod_core n hn S e
  ·
    exact exactly_one_type n hn S e hsix
  ·
    intro G₀ _ hidx hQ
    have h := typeII_subgroup_spec n hn S e G₀ hidx hQ
    rw [hY] at h
    exact h
  ·
    have h := exists_centralizer_singleton_conj_swap_eq_x2 hn S e hsix _ hJZ
    rw [hJ, hz, hJ₁] at h
    exact h
  ·
    have h := modelBase_le_centralizer_modelOmega S e hn1
    rw [hB, hD] at h
    exact h
  ·
    have h := modelBase_sylow_centralizer_modelOmega hn S e
    rw [hD, hB] at h
    exact h
  ·
    have h := normalizer_modelOmega_eq hn S e
    rw [hD, hB] at h
    exact h
  ·
    intro hI
    have hbase := base_sym3_of_typeI n hn S e hsix hI
    obtain ⟨Y, hYN, hY1, hY2, hY3⟩ := exists_base_three_cycle hn S e hbase
    have hNY := normalizer_base_eq_of_three_cycle hn S e hbase Y hYN hY1 hY2 hY3
    have hidx : (Subgroup.centralizer (modelBase S e : Set G)).relIndex
        (Subgroup.normalizer (modelBase S e : Set G)) = 6 := by
      obtain ⟨esix⟩ := hbase
      rw [relIndex_eq_card_quotient, Nat.card_congr esix.toEquiv, Nat.card_eq_fintype_card,
        Fintype.card_perm]
      decide
    rw [hB] at hYN hidx hNY
    rw [hJ, hJ₁] at hY1
    rw [hJ₁, hJ₂] at hY2
    rw [hJ₂, hJ] at hY3
    rw [hz] at hNY
    exact ⟨all_involutions_conjugate_of_base_sym3 hn S e hbase hsix, hidx, Y, hYN, hY1, hY2, hY3,
      hNY⟩
  ·
    intro hII
    have hcard := base_order_two_of_typeII n hn S e hsix hII
    have hclasses := involution_classes_ncard_of_base_order_two hn S e hcard hsix
    have hJS := conj_class_x_inter_sylow_of_base_order_two hn S e hcard
    have hN := normalizer_base_eq_of_order_two hn S e hcard
    have hidx : (Subgroup.centralizer (modelBase S e : Set G)).relIndex
        (Subgroup.normalizer (modelBase S e : Set G)) = 2 := by
      rw [relIndex_eq_card_quotient, hcard]
    rw [hJ] at hJS
    rw [hB, hz] at hN
    rw [hB] at hidx
    exact ⟨hclasses, hJS, hidx, hN⟩
  ·
    intro g hg
    have h := maximal_order_iff S e hn g hg
    rw [hz, hs, ht, ← h2n] at h
    exact h
  ·
    intro g hg hord
    rw [h2n] at hord
    obtain ⟨h, hodd, h1, hlt, s, -, hsg⟩ := exists_isConj_root_pow S e hn g hg hord
    rw [hR] at hsg
    exact ⟨h, hodd, h1, hlt, isConj_iff.mpr ⟨s⁻¹, by rw [inv_inv]; exact hsg⟩⟩
  ·
    have h := root_pow_odd_ncard S e hn
    rw [hR] at h
    exact h
  ·
    intro h h' hh hlt hh' hlt' hc
    rw [← hR] at hc
    exact root_pow_isConj_iff S e hn h h' hh hh' hlt hlt' hc
  ·
    intro g _ hg hord
    rw [h2n] at hord
    have h := exists_isConj_mem_modelBase S e hn hsix g hg hord
    rw [hB] at h
    exact h
  ·
    intro x hx y hy
    rw [← hB] at hx hy
    have h := base_isConj_iff S e hn hx hy
    rw [hB] at h
    exact h
  ·
    intro h hh
    have hS := exists_sylow_centralizer_root_zpow S e hn h hh
    rw [hR] at hS
    exact hS
  ·
    intro μ hμ hμZ
    rw [← hB] at hμ
    rw [← hZ] at hμZ
    have h := modelBase_sylow_centralizer_of_not_isConj S e hn hμ hμZ
    rw [hB] at h
    exact h
  ·
    intro z hzA hz1
    rw [← hZ] at hzA
    exact centralizer_noAbelian_and_typeII S e hn hsix hzA hz1
  ·
    intro hII z hzA _ g
    rw [← hZ] at hzA
    exact eq_centralizer_mul_pPrimeCore_of_base_order_two S e hn
      (base_order_two_of_typeII n hn S e hsix hII) hzA g
  ·
    intro hII g
    have h := eq_centralizer_mul_pPrimeCore_of_base_order_two S e hn
      (base_order_two_of_typeII n hn S e hsix hII) hJZ g
    rw [hJ] at h
    exact h

end CFSG.Wreathed.BrauerWong
