module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderLargeRee

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag

theorem entrywise_baseChangeGL_fixSubfield
    {τ' : Tag} {K : Type} [Field K]
    [Finite K] (τ σ : K ≃+* K) (j : ModGL τ' (fixSubfield σ)) :
    Units.map (entrywiseHom τ.toRingHom) (baseChangeGL (fixSubfield σ).subtype j) =
      baseChangeGL (fixSubfield σ).subtype
        (Units.map (entrywiseHom (fixSubfieldRestrict τ σ).toRingHom) j) := by
  rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
    baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL]
  congr 1

theorem exists_reeGamma_fixSubfield_hom
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (σ : K ≃+* K)
    (hσ : orderOf σ = p) :
    ∃ (b : ℕ) (_ : Nat.card (fixSubfield σ) = 2 ^ (2 * b + 1))
      (ψ : F4.reeGamma (fixSubfield σ) b →* F4.reeGamma K a),
      (2 * b + 1) * p = 2 * a + 1 ∧ Function.Injective ψ ∧
      (∀ g : F4.reeGamma K a, F4.reeGammaFieldAut K a σ g = g ↔ g ∈ ψ.range) ∧
      ∀ (τ : K ≃+* K) (g₀ : F4.reeGamma (fixSubfield σ) b),
        F4.reeGammaFieldAut K a τ (ψ g₀) =
          ψ (F4.reeGammaFieldAut (fixSubfield σ) b (fixSubfieldRestrict τ σ) g₀) := by
  obtain ⟨b, hbp, hk, hfix⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.largeRee_fixed_data_of_odd hK hp hp2 σ hσ
  set ι := (fixSubfield σ).subtype with hι
  have hmem : ∀ g₀ : F4.reeGamma (fixSubfield σ) b,
      baseChangeGL ι (g₀ : ModGL F4.tag (fixSubfield σ)) ∈ F4.reeGamma K a := by
    intro g₀
    have h : baseChangeGL ι (g₀ : ModGL F4.tag (fixSubfield σ)) ∈
        (F4.reeGamma (fixSubfield σ) b).map (baseChangeGL ι) := ⟨g₀, g₀.2, rfl⟩
    rw [← hfix] at h
    obtain ⟨g, -, hg⟩ := h
    rw [← hg]
    exact g.2
  let ψ : F4.reeGamma (fixSubfield σ) b →* F4.reeGamma K a :=
    ((baseChangeGL ι).comp (F4.reeGamma (fixSubfield σ) b).subtype).codRestrict _ hmem
  have hψ : ∀ g₀, ((ψ g₀ : F4.reeGamma K a) : ModGL F4.tag K) =
      baseChangeGL ι (g₀ : ModGL F4.tag (fixSubfield σ)) := fun _ => rfl
  refine ⟨b, hk, ψ, hbp, fun g₀ g₀' h => ?_, fun g => ?_, fun τ g₀ => ?_⟩
  · have h' := congrArg (fun z : F4.reeGamma K a => (z : ModGL F4.tag K)) h
    simp only [hψ] at h'
    exact Subtype.ext (baseChangeGL_injective ι h')
  · constructor
    · intro hg
      have h : (g : ModGL F4.tag K) ∈
          ((F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
            (F4.reeGamma K a).subtype := ⟨g, hg, rfl⟩
      rw [hfix] at h
      obtain ⟨g₀, hg₀, hgg⟩ := h
      exact ⟨⟨g₀, hg₀⟩, Subtype.ext hgg⟩
    · rintro ⟨g₀, rfl⟩
      have h : baseChangeGL ι (g₀ : ModGL F4.tag (fixSubfield σ)) ∈
          (F4.reeGamma (fixSubfield σ) b).map (baseChangeGL ι) := ⟨g₀, g₀.2, rfl⟩
      rw [← hfix] at h
      obtain ⟨g, hg, hgg⟩ := h
      have : g = ψ g₀ := Subtype.ext hgg
      rw [← this]
      exact hg
  · apply Subtype.ext
    rw [coe_reeGammaFieldAut, hψ, hψ, coe_reeGammaFieldAut]
    exact entrywise_baseChangeGL_fixSubfield τ σ _

end CFSG.HardMathSupport.Timmesfeld.CrossChar
