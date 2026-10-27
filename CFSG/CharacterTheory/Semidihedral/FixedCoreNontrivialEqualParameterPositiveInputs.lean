module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterData
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ABGLocalTools (IsSylowOf)

structure PositiveInputs (G : Type) [Group G] [Finite G] (t s₀ d : G) (J : Subgroup G)
    (p f : ℕ) : Prop where
  card_W_B :
    (p ^ f % 4 = 1 → 2 * Nat.card (torusW G t s₀) = p ^ f + 1 ∧
      4 * Nat.card ((N t).map (C t).subtype) = p ^ f - 1) ∧
    (p ^ f % 4 = 3 → 2 * Nat.card (torusW G t s₀) = p ^ f - 1 ∧
      4 * Nat.card ((N t).map (C t).subtype) = p ^ f + 1) ∧
    (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
  card_sylow_two : ∀ T : Sylow 2 G, Nat.card T = 16
  le_C_of_isPGroup : ∀ {ℓ : ℕ}, ℓ.Prime → ℓ ∣ Nat.card ((N t).map (C t).subtype) →
    ∀ (P : Sylow ℓ ((N t).map (C t).subtype)) {Q : Subgroup G}, IsPGroup ℓ Q →
    (P : Subgroup ((N t).map (C t).subtype)).map ((N t).map (C t).subtype).subtype ≤ Q →
    Q ≤ C t ∧ Subgroup.normalizer (Q : Set G) ≤ C t
  exists_normal_complement_torus_core : ∀ (R : Subgroup G), Odd (Nat.card R) →
    torusW G t s₀ ≤ R → (N t).map (C t).subtype ≤ R →
    Nat.Coprime (Nat.card (torusW G t s₀))
      ((torusW G t s₀).relIndex (R ⊓ torusH G t s₀)) →
    Nat.card (torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) =
        Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype) ∧
      ∃ U : Subgroup G, U ≤ R ∧ R ≤ Subgroup.normalizer (U : Set G) ∧
        Disjoint U (torusW G t s₀ ⊔ (N t).map (C t).subtype) ∧
        U ⊔ (torusW G t s₀ ⊔ (N t).map (C t).subtype) = R ∧
        Nat.card U * Nat.card (torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) =
          Nat.card R ∧
        Nat.Coprime (Nat.card U) (Nat.card (torusW G t s₀))
  sylow_C_facts : ∀ {Q₁ : Subgroup G}, IsSylowOf p Q₁ (C t) →
    Nat.card Q₁ = p ^ f ∧ Q₁ ≤ J ∧ (∀ x ∈ Q₁, ∀ y ∈ Q₁, x * y = y * x) ∧
      C t ⊓ Subgroup.centralizer (Q₁ : Set G) =
        Q₁ ⊔ (N t).map (C t).subtype ⊔ Subgroup.zpowers t ∧
      Nat.card (C t ⊓ Subgroup.normalizer (Q₁ : Set G) : Subgroup G) =
        2 * Nat.card ((N t).map (C t).subtype) * p ^ f * (p ^ f - 1)
  eq_bot_of_mod_four_eq_one : p ^ f % 4 = 1 →
    (∀ X : Subgroup G, X ≤ C t → IsPGroup p X →
      torusW G t s₀ ≤ Subgroup.normalizer (X : Set G) → X = ⊥) ∧
    (∀ X : Subgroup G, X ≤ C t → IsPGroup p X → s₀ ∈ Subgroup.normalizer (X : Set G) →
      X = ⊥) ∧
    ∀ X : Subgroup G, X ≤ C t → Odd (Nat.card X) →
      Nat.Coprime (Nat.card X) (Nat.card (torusW G t s₀)) →
      torusW G t s₀ ≤ Subgroup.normalizer (X : Set G) → X ≤ (N t).map (C t).subtype
  layer_le_of_not_le_normalizer : p ^ f % 4 = 1 → ∀ {X : Subgroup G}, X ≤ C t →
    torusW G t s₀ ≤ X → (N t).map (C t).subtype ≤ X → t ∈ X →
    ¬ X ≤ Subgroup.normalizer ((torusW G t s₀ : Subgroup G) : Set G) → J ≤ X
  exists_layer_torus : p ^ f % 4 = 1 → ∀ {Q₁ : Subgroup G}, IsSylowOf p Q₁ (C t) →
    ∃ Y O : Subgroup G, Y ≤ C t ⊓ Subgroup.normalizer (Q₁ : Set G) ∧ IsCyclic Y ∧
      Nat.card Y = 2 * (p ^ f - 1) ∧ t ∈ Y ∧ Disjoint Y ((N t).map (C t).subtype) ∧
      C t ⊓ Subgroup.normalizer (Q₁ : Set G) = Q₁ ⊔ Y ⊔ (N t).map (C t).subtype ∧
      O ≤ Y ∧ O ≤ J ∧ Nat.card O = Nat.card ((N t).map (C t).subtype) ∧
      (∀ y ∈ O, ∀ x ∈ (N t).map (C t).subtype, y * x = x * y) ∧
      Nat.card (O ⊔ (N t).map (C t).subtype : Subgroup G) =
        Nat.card ((N t).map (C t).subtype) ^ 2 ∧
      ∀ E : Subgroup G, E ≤ O ⊔ (N t).map (C t).subtype → ¬ E ≤ (N t).map (C t).subtype →
        ∀ c ∈ C t ⊓ Subgroup.normalizer (E : Set G), Odd (orderOf c) →
          c ∈ O ⊔ (N t).map (C t).subtype
  sylow_H_facts : ∀ {P : Subgroup G}, IsSylowOf p P (torusH G t s₀) →
    Nat.card P = p ^ f ∧ P ≤ torusK G t s₀ ∧
      torusH G t s₀ ⊓ Subgroup.centralizer (P : Set G) = P ⊔ torusW G t s₀
  exists_split_torus_sylow : p ^ f % 4 = 1 →
    ∃ P : Subgroup G, IsSylowOf p P (torusH G t s₀) ∧
      (N t).map (C t).subtype ⊔ Subgroup.zpowers d ≤ Subgroup.normalizer (P : Set G) ∧
      IsCyclic ((N t).map (C t).subtype ⊔ Subgroup.zpowers d : Subgroup G) ∧
      Nat.card ((N t).map (C t).subtype ⊔ Subgroup.zpowers d : Subgroup G) = p ^ f - 1 ∧
      (∀ x ∈ (N t).map (C t).subtype ⊔ Subgroup.zpowers d, x ≠ 1 →
        P ⊓ Subgroup.centralizer {x} = ⊥) ∧
      Nat.card (P ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype : Subgroup G) =
        p ^ f * Nat.card (torusW G t s₀) * Nat.card ((N t).map (C t).subtype) ∧
      ∀ X : Subgroup G, X ≤ torusH G t s₀ → Odd (Nat.card X) →
        P ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype ≤ X →
        X = P ⊔ torusW G t s₀ ⊔ (N t).map (C t).subtype
  le_centralizer_of_isPGroup_two_of_no_kleinFour : ∀ {S : Subgroup G}, IsPGroup 2 S →
    (∀ T : Subgroup G, T ≤ S → ¬ IsKleinFour T) → ∀ {u : G}, u ∈ S → orderOf u = 2 →
    S ≤ Subgroup.centralizer {u}
  conj_eq_inv_of_inf_centralizer_eq_bot : ∀ {Q : Subgroup G}, Odd (Nat.card Q) → ∀ {u : G},
    u * u = 1 → u ∈ Subgroup.normalizer (Q : Set G) → Q ⊓ Subgroup.centralizer {u} = ⊥ →
    (∀ x ∈ Q, u * x * u⁻¹ = x⁻¹) ∧ ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x
  odd_mem_pPrimeCore_of_isCyclic_sylow : ∀ {F₁ : Subgroup G} (S : Sylow 2 F₁),
    IsCyclic (S : Subgroup F₁) →
    IsPGroup 2 (F₁ ⧸ CFSG.pPrimeCore 2 F₁) ∧
      ∀ x ∈ F₁, Odd (orderOf x) → x ∈ (CFSG.pPrimeCore 2 F₁).map F₁.subtype
  sq_dvd_card_of_sl2_inverting : ∀ {F₀ : Type} [Field F₀] [Finite F₀] {p₀ f₀ : ℕ},
    p₀.Prime → Odd p₀ → 1 ≤ f₀ → Nat.card F₀ = p₀ ^ f₀ → 5 ≤ p₀ ^ f₀ →
    ∀ (J₀ Q : Subgroup G) (e : J₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F₀),
    IsPGroup p₀ Q → (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) →
    J₀ ≤ Subgroup.normalizer (Q : Set G) →
    (∀ x ∈ Q, (e.symm (-1) : G) * x * (e.symm (-1) : G)⁻¹ = x⁻¹) → Q ≠ ⊥ →
    (p₀ ^ f₀) ^ 2 ∣ Nat.card Q


namespace PositiveInputs

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem numerics (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1) :
    p ^ f = 4 * Nat.card ((N t).map (C t).subtype) + 1 ∧
      Nat.card (torusW G t s₀) = 2 * Nat.card ((N t).map (C t).subtype) + 1 ∧
      Odd (Nat.card ((N t).map (C t).subtype)) ∧ 1 < Nat.card ((N t).map (C t).subtype) ∧
      p ^ f % 8 = 5 ∧
      Nat.card (C t) = 16 * Nat.card ((N t).map (C t).subtype) ^ 2 * p ^ f *
        Nat.card (torusW G t s₀) := by
  obtain ⟨hWB, -, h8⟩ := hI.card_W_B
  obtain ⟨hw, hb⟩ := hWB he
  set b := Nat.card ((N t).map (C t).subtype) with hbdef
  set w := Nat.card (torusW G t s₀) with hwdef
  have hq : p ^ f = 4 * b + 1 := by omega
  have hwb : w = 2 * b + 1 := by omega
  have hq8 : p ^ f % 8 = 5 := by omega
  have hbodd : Odd b := by
    rw [Nat.odd_iff]
    omega
  have hb1 : 1 < b := (Subgroup.one_lt_card_iff_ne_bot _).mpr h.B_ne_bot
  refine ⟨hq, hwb, hbodd, hb1, hq8, ?_⟩
  have hsq : (4 * b + 1) ^ 2 - 1 = 8 * b * (2 * b + 1) := by
    have : (4 * b + 1) ^ 2 = 8 * b * (2 * b + 1) + 1 := by ring
    omega
  rw [h.card_C, ← hbdef, hq, hsq, hwb]
  ring

theorem coprimes (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1) :
    Nat.Coprime (Nat.card ((N t).map (C t).subtype)) (Nat.card (torusW G t s₀)) ∧
      Nat.Coprime (p ^ f) (Nat.card (torusW G t s₀)) ∧
      Nat.Coprime (p ^ f) (Nat.card ((N t).map (C t).subtype)) ∧
      Nat.Coprime p (Nat.card (torusW G t s₀)) ∧
      Nat.Coprime p (Nat.card ((N t).map (C t).subtype)) := by
  obtain ⟨hq, hwb, -⟩ := hI.numerics h he
  set b := Nat.card ((N t).map (C t).subtype)
  set w := Nat.card (torusW G t s₀)
  have hbw : Nat.Coprime b w := by
    rw [← Nat.isCoprime_iff_coprime]
    exact ⟨-2, 1, by rw [hwb]; push_cast; ring⟩
  have hqw : Nat.Coprime (p ^ f) w := by
    rw [← Nat.isCoprime_iff_coprime]
    exact ⟨-1, 2, by rw [hwb, hq]; push_cast; ring⟩
  have hqb : Nat.Coprime (p ^ f) b := by
    rw [← Nat.isCoprime_iff_coprime]
    exact ⟨1, -4, by rw [hq]; push_cast; ring⟩
  have hpq : p ∣ p ^ f := dvd_pow_self p (Nat.one_le_iff_ne_zero.mp h.one_le)
  exact ⟨hbw, hqw, hqb, Nat.Coprime.coprime_dvd_left hpq hqw,
    Nat.Coprime.coprime_dvd_left hpq hqb⟩

end PositiveInputs

end CFSG.Semidihedral.FixedCoreNontrivial
