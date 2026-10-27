module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

section Conj

variable {W : Type*} [AddCommMonoid W] [Module (ZMod 2) W] {U : Type*} [AddCommMonoid U]
  [Module (ZMod 2) U]

@[expose] noncomputable def conjU (β : W ≃ₗ[ZMod 2] U) :
    (Module.End (ZMod 2) W)ˣ →* (Module.End (ZMod 2) U)ˣ :=
  Units.map (β.conjRingEquiv.toRingHom : Module.End (ZMod 2) W →+* Module.End (ZMod 2) U)

theorem conjU_val_apply (β : W ≃ₗ[ZMod 2] U) (y : (Module.End (ZMod 2) W)ˣ) (w : W) :
    (conjU β y).val (β w) = β (y.val w) := by
  simp [conjU]

theorem conjU_injective (β : W ≃ₗ[ZMod 2] U) : Function.Injective (conjU β) :=
  Units.map_injective β.conjRingEquiv.injective

end Conj

section Extension

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {F : Type*} [Field F] {W : Type*}
  [AddCommGroup W] [Module (ZMod 2) W]

omit [DecidableEq Ω] in
theorem permU_one : permU (1 : Equiv.Perm Ω) = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem exists_sym_extension (h5 : Fintype.card Ω = 5) (β : W ≃ₗ[ZMod 2] ↥(evenWeight Ω))
    (π : SL(2, F) →* Equiv.Perm Ω) (hπ : π.range = alternatingGroup Ω)
    (ρU : SL(2, F) →* (Module.End (ZMod 2) W)ˣ)
    (hβ : ∀ g w, ((β ((ρU g).val w) : ↥(evenWeight Ω)) : Ω → ZMod 2) =
      permAct (π g) (β w : Ω → ZMod 2))
    (G : Subgroup (Module.End (ZMod 2) W)ˣ) (hLG : ρU.range ≤ G)
    (hGN : ∀ y ∈ G, y ∈ Subgroup.normalizer (ρU.range : Set (Module.End (ZMod 2) W)ˣ)) :
    ∃ ψ : ↥G →* Equiv.Perm Ω, Function.Injective ψ ∧
      (∀ (y : ↥G) (w : W), ((β (y.1.val w) : ↥(evenWeight Ω)) : Ω → ZMod 2) =
          permAct (ψ y) (β w : Ω → ZMod 2)) ∧
      (∀ (g : SL(2, F)) (h : ρU g ∈ G), ψ ⟨ρU g, h⟩ = π g) ∧
      ((∃ y ∈ G, y ∉ ρU.range) → Function.Surjective ψ) := by
  classical
  have hconjπ : ∀ g, conjU β (ρU g) = permU (π g) := by
    intro g
    apply Units.ext
    apply LinearMap.ext
    intro u
    obtain ⟨w, rfl⟩ := β.surjective u
    apply Subtype.ext
    rw [conjU_val_apply]
    exact hβ g w
  have hnorm : ∀ y ∈ G, ∀ σ ∈ alternatingGroup Ω, ∃ σ' ∈ alternatingGroup Ω,
      conjU β y * permU σ * (conjU β y)⁻¹ = permU σ' := by
    intro y hy σ hσ
    rw [← hπ] at hσ
    obtain ⟨g, rfl⟩ := hσ
    have hyN := Subgroup.mem_normalizer_iff.mp (hGN y hy) (ρU g)
    obtain ⟨g', hg'⟩ := hyN.mp ⟨g, rfl⟩
    refine ⟨π g', ?_, ?_⟩
    · rw [← hπ]
      exact ⟨g', rfl⟩
    · rw [← hconjπ g, ← hconjπ g', hg', ← map_inv, ← map_mul, ← map_mul]
  have hex : ∀ y : ↥G, ∃! τ : Equiv.Perm Ω, conjU β y.1 = permU τ := fun y =>
    deleted_five_normalizer h5 (conjU β y.1) (hnorm y.1 y.2)
  choose ψf hψf hψu using hex
  have hψ_unique : ∀ (y : ↥G) (τ : Equiv.Perm Ω), conjU β y.1 = permU τ → τ = ψf y :=
    fun y τ h => hψu y τ h
  let ψ : ↥G →* Equiv.Perm Ω :=
    { toFun := ψf
      map_one' := by
        apply permU_injective h5
        rw [← hψf 1, permU_one]
        exact map_one _
      map_mul' := fun y y' => by
        apply permU_injective h5
        rw [permU_mul, ← hψf y, ← hψf y', ← hψf (y * y')]
        exact map_mul _ _ _ }
  have hψ_apply : ∀ y : ↥G, ψ y = ψf y := fun y => rfl
  have hinj : Function.Injective ψ := by
    intro y y' h
    apply Subtype.ext
    apply conjU_injective β
    rw [hψf y, hψf y']
    exact congrArg permU h
  have hequiv : ∀ (y : ↥G) (w : W), ((β (y.1.val w) : ↥(evenWeight Ω)) : Ω → ZMod 2) =
      permAct (ψ y) (β w : Ω → ZMod 2) := by
    intro y w
    have h1 := conjU_val_apply β y.1 w
    rw [hψf y] at h1
    rw [← h1]
    rfl
  have hL : ∀ (g : SL(2, F)) (h : ρU g ∈ G), ψ ⟨ρU g, h⟩ = π g := by
    intro g h
    exact (hψ_unique ⟨ρU g, h⟩ (π g) (hconjπ g)).symm
  refine ⟨ψ, hinj, hequiv, hL, ?_⟩
  rintro ⟨y₀, hy₀G, hy₀L⟩
  have hτ₀ : ψ ⟨y₀, hy₀G⟩ ∉ alternatingGroup Ω := by
    intro hmem
    rw [← hπ] at hmem
    obtain ⟨g, hg⟩ := hmem
    apply hy₀L
    have h1 : ψ ⟨ρU g, hLG ⟨g, rfl⟩⟩ = ψ ⟨y₀, hy₀G⟩ := by rw [hL, hg]
    have h2 := hinj h1
    have h3 : ρU g = y₀ := congrArg Subtype.val h2
    exact ⟨g, h3⟩
  intro σ
  by_cases hσ : σ ∈ alternatingGroup Ω
  · rw [← hπ] at hσ
    obtain ⟨g, rfl⟩ := hσ
    exact ⟨⟨ρU g, hLG ⟨g, rfl⟩⟩, hL g _⟩
  · have hs1 : Equiv.Perm.sign σ = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) hσ
      · exact h
    have hs2 : Equiv.Perm.sign (ψ ⟨y₀, hy₀G⟩) = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (ψ ⟨y₀, hy₀G⟩)) with h | h
      · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) hτ₀
      · exact h
    have hmem : σ * (ψ ⟨y₀, hy₀G⟩)⁻¹ ∈ alternatingGroup Ω := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs1, hs2]
      decide
    rw [← hπ] at hmem
    obtain ⟨g, hg⟩ := hmem
    refine ⟨⟨ρU g, hLG ⟨g, rfl⟩⟩ * ⟨y₀, hy₀G⟩, ?_⟩
    rw [map_mul, hL, hg]
    group

end Extension

end CFSG.QuasithinUnique.Setup.SL2Modules
