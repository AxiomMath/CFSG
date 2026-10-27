module

public import CFSG.CharacterTheory.Wreathed.ConfinedOddCoreStructure
public import CFSG.CharacterTheory.Wreathed.NormalComponentLift

public section

open scoped Classical Pointwise commutatorElement

namespace CFSG.Wreathed.ConfinedOddCore


open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.TorusSplitting

theorem confined_original_odd_core_has_cyclic_fixed_factor_and_abelian_inverted_kernel
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    (hconf : ∀ r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, r ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers r : Set G) ≤ involutionCentralizer n S e) :
    let m := 2 ^ n
    let q := p ^ f
    let ε : ℤ := if q % 4 = 1 then 1 else -1
    let N := involutionCentralizer n S e
    let x : G := wreathModelHom S e (Original.x m)
    let y : G := wreathModelHom S e (Original.x2 m)
    let RG : Subgroup G := (centralizerOddCore n S e).map N.subtype
    let JG : Subgroup G := J.map N.subtype
    let C₀ := torusCore n S e
    let A₀ := torusFixedCore n S e
    (∀ g, g ∈ A₀ ↔ g ∈ RG ∧ g * y = y * g) ∧
    ∃ W₀ : Subgroup G, (∀ g, g ∈ W₀ ↔ g ∈ JG ∧ g * y = y * g ∧ Odd (orderOf g)) ∧
      W₀ ⊔ A₀ = C₀ ∧ W₀ ⊓ A₀ = ⊥ ∧ (∀ g ∈ W₀, ∀ z ∈ A₀, g * z = z * g) ∧
      (∃ μ : W₀ × A₀ ≃* C₀, ∀ z : W₀ × A₀, (μ z : G) = z.1 * z.2) ∧
      IsCyclic W₀ ∧ (m : ℤ) * Nat.card W₀ = q - ε ∧
      IsCyclic A₀ ∧ (Nat.card A₀ : ℤ) ∣ (q - ε) / m ∧
      ∃ B : Subgroup G, (∀ g, g ∈ B ↔ g ∈ RG ∧ y * g * y⁻¹ = g⁻¹) ∧ B ≤ RG ∧
        IsMulCommutative B ∧ (B.subgroupOf RG).Characteristic ∧ (B.subgroupOf RG).Normal ∧
        B ⊓ A₀ = ⊥ ∧ B ⊔ A₀ = RG ∧ (RG : Set G) = (B : Set G) * (A₀ : Set G) ∧
        B = ⁅RG, Subgroup.zpowers y⁆ ∧
        (∀ g ∈ N, orderOf g = 2 → g ≠ x →
          (∃ k ∈ N, k * y * k⁻¹ = g) ∧ ∀ v ∈ B, g * v * g⁻¹ = v⁻¹) ∧
        (A₀ ≠ ⊥ → (∀ a ∈ A₀, a ≠ 1 → RG ⊓ Subgroup.centralizer {a} = A₀) ∧
          (B ≠ ⊥ → ∀ a ∈ A₀, a ≠ 1 → ∀ v ∈ B, a * v * a⁻¹ = v → v = 1)) := by
  intro m q ε N x y RG JG C₀ A₀
  obtain ⟨F, hF, hFfin, Sigma, b, hSigma, ρ, Ψ, hdata⟩ :=
    exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hF
  let : Finite F := hFfin
  obtain ⟨hd1, W₀, hW₀mem, hW₀C, -, hW₀c, hW₀A, hW₀Ac, -, hwA, hcard, ⟨WF, hWF⟩, hζ⟩ :=
    NormalComponentLift.actual_normal_component_lift_eliminates_odd_field_factor hnonab n hn S e
      hfour p f hp hpodd hf hmodel J hJM hJR F Sigma b hSigma ρ Ψ hdata
  obtain ⟨ζ, -, hζW⟩ := hζ WF hWF
  have hsub : Subsingleton Sigma := (Nat.card_eq_one_iff_unique.mp hd1).1
  have hC₀ : torusCore n S e ≤ W₀ ⊔ torusFixedCore n S e := by
    intro k hk
    refine (hζW ⟨k, hk⟩).mpr ⟨(ζ (QuotientGroup.mk ⟨k, hk⟩)).left, ?_⟩
    have hr : (ζ (QuotientGroup.mk ⟨k, hk⟩)).right = 1 := Subsingleton.elim _ _
    conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right (ζ (QuotientGroup.mk ⟨k, hk⟩))]
    rw [hr, map_one, mul_one]
  have h := confined_core_structure hnonab n hn S e p f hp hpodd hf J hJR hconf F Sigma b hSigma
    ρ Ψ hdata W₀ hW₀mem hW₀C hW₀c hW₀A hW₀Ac hwA hcard hC₀
  exact ⟨h.1, W₀, hW₀mem, h.2⟩

end CFSG.Wreathed.ConfinedOddCore
