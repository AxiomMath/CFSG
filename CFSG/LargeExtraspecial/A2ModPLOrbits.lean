module

public import CFSG.LargeExtraspecial.A2ModPLPairing
public import CFSG.LargeExtraspecial.A2ModPointMapsNorm

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Module Matrix CFSG.RankThree.OrthogonalInvolutions

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {ρ' : SpecialLinearGroup (Fin n) (ZMod 2) →* (V ≃ₗ[ZMod 2] V)}
  {P Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V}

theorem IsPointMaps.four_le_natCard_commSpace [Finite V] (hP : IsPointMaps ρ' Q P Pd)
    {g : SpecialLinearGroup (Fin n) (ZMod 2)} (hg : g ≠ 1) :
    4 ≤ Nat.card ↥(commSpace (ρ' g)) := by
  obtain ⟨v, hv⟩ : ∃ v, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v ≠ v := by
    by_contra hcon
    push Not at hcon
    have hmat : (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 :=
      Matrix.ext_iff_mulVec.mpr fun v => by rw [hcon v, one_mulVec]
    exact hg (Subtype.ext (hmat.trans Matrix.SpecialLinearGroup.coe_one.symm))
  obtain ⟨φ, hφ⟩ : ∃ φ, contra g φ ≠ φ := by
    by_contra hcon
    push Not at hcon
    have h1 : ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        1 := Matrix.ext_iff_vecMul.mpr fun φ => by rw [vecMul_one]; exact hcon φ
    exact hg (inv_eq_one.mp (Subtype.ext (h1.trans Matrix.SpecialLinearGroup.coe_one.symm)))
  have hp₁c : P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v - v) ∈ commSpace (ρ' g) :=
    mem_commSpace.mpr ⟨P v, by rw [map_sub, hP.map_mulVec]⟩
  have hp₂c : Pd (contra g φ - φ) ∈ commSpace (ρ' g) :=
    mem_commSpace.mpr ⟨Pd φ, by rw [map_sub, hP.map_contra]⟩
  have hp₁0 : P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v - v) ≠ 0 := fun h0 =>
    hv (sub_eq_zero.mp (hP.injective (h0.trans (map_zero P).symm)))
  have hp₂0 : Pd (contra g φ - φ) ≠ 0 := fun h0 =>
    hφ (sub_eq_zero.mp (hP.injective_dual (h0.trans (map_zero Pd).symm)))
  have key : ∀ p₁ p₂ : V, p₁ ∈ commSpace (ρ' g) → p₂ ∈ commSpace (ρ' g) →
      p₁ ∈ LinearMap.range P → p₂ ∈ LinearMap.range Pd → p₁ ≠ 0 → p₂ ≠ 0 →
      4 ≤ Nat.card ↥(commSpace (ρ' g)) := by
    intro p₁ p₂ hc₁ hc₂ hr₁ hr₂ h₁0 h₂0
    have hind : ∀ s t : ZMod 2, s • p₁ + t • p₂ = 0 → s = 0 ∧ t = 0 := by
      intro s t hst
      have hmem₁ : s • p₁ ∈ LinearMap.range P := Submodule.smul_mem _ s hr₁
      have hmem₂ : s • p₁ ∈ LinearMap.range Pd := by
        have : s • p₁ = -(t • p₂) := eq_neg_of_add_eq_zero_left hst
        rw [this]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ t hr₂)
      have h0 : s • p₁ ∈ LinearMap.range P ⊓ LinearMap.range Pd := ⟨hmem₁, hmem₂⟩
      rw [hP.range_inf_range, Submodule.mem_bot] at h0
      have hs : s = 0 := (smul_eq_zero.mp h0).resolve_right h₁0
      rw [hs, zero_smul, zero_add] at hst
      exact ⟨hs, (smul_eq_zero.mp hst).resolve_right h₂0⟩
    let f : ZMod 2 × ZMod 2 → ↥(commSpace (ρ' g)) := fun st =>
      ⟨st.1 • p₁ + st.2 • p₂,
        Submodule.add_mem _ (Submodule.smul_mem _ _ hc₁) (Submodule.smul_mem _ _ hc₂)⟩
    have hf : Function.Injective f := by
      rintro ⟨s, t⟩ ⟨s', t'⟩ hst
      have h1 : s • p₁ + t • p₂ = s' • p₁ + t' • p₂ := congrArg Subtype.val hst
      have h2 : (s - s') • p₁ + (t - t') • p₂ = 0 := by
        rw [sub_smul, sub_smul]
        linear_combination (norm := module) h1
      obtain ⟨hs, ht⟩ := hind _ _ h2
      exact Prod.ext (sub_eq_zero.mp hs) (sub_eq_zero.mp ht)
    have h4 := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_zmod] at h4
  exact key _ _ hp₁c hp₂c ⟨_, rfl⟩ ⟨_, rfl⟩ hp₁0 hp₂0

theorem IsPointMaps.mem_range_of_apply_eq {H : Type*} [Group H] {ρ : H →* (V ≃ₗ[ZMod 2] V)}
    {Ψ : SpecialLinearGroup (Fin n) (ZMod 2) →* H} (hP : IsPointMaps (ρ.comp Ψ) Q P Pd)
    (hC : Subgroup.centralizer (Ψ.range : Set H) = ⊥) {ℓ : H}
    (hℓ : ∀ g, ∃ g', ℓ * Ψ g * ℓ⁻¹ = Ψ g') {u : V} (hu : u ≠ 0)
    (hu' : u ∈ LinearMap.range P ∨ u ∈ LinearMap.range Pd) (hfix : ρ ℓ u = u) :
    ℓ ∈ Ψ.range := by
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : SpecialLinearGroup (Fin n) (ZMod 2),
      ∀ g, Commute ((Ψ g₁)⁻¹ * ℓ) (Ψ g) := by
    rcases hu' with ⟨v₀, rfl⟩ | ⟨φ₀, rfl⟩
    · have hv₀ : v₀ ≠ 0 := fun h0 => hu (by rw [h0, map_zero])
      exact hP.exists_mul_commute_of_apply_eq hℓ hv₀ hfix
    · have hφ₀ : φ₀ ≠ 0 := fun h0 => hu (by rw [h0, map_zero])
      exact hP.exists_mul_commute_of_apply_dual_eq hℓ hφ₀ hfix
  have hc : (Ψ g₁)⁻¹ * ℓ ∈ Subgroup.centralizer (Ψ.range : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hh
    exact (hg₁ g).eq.symm
  rw [hC, Subgroup.mem_bot] at hc
  exact ⟨g₁, inv_mul_eq_one.mp hc⟩

theorem IsPointMaps.exists_apply_eq_of_singular_of_not_mem_range [FiniteDimensional (ZMod 2) V]
    {ρ' : SpecialLinearGroup (Fin 4) (ZMod 2) →* (V ≃ₗ[ZMod 2] V)}
    {P Pd : (Fin 4 → ZMod 2) →ₗ[ZMod 2] V}
    (hA : A2Action (transvectionSet 4 (ZMod 2)) Q ρ') (hP : IsPointMaps ρ' Q P Pd)
    (hdim : finrank (ZMod 2) V < 16) {u u' : V}
    (hu : u ∈ LinearMap.range P ⊔ LinearMap.range Pd)
    (hu' : u' ∈ LinearMap.range P ⊔ LinearMap.range Pd) (hu0 : Q u = 0) (hu0' : Q u' = 0)
    (huP : u ∉ LinearMap.range P) (huPd : u ∉ LinearMap.range Pd)
    (hu'P : u' ∉ LinearMap.range P) (hu'Pd : u' ∉ LinearMap.range Pd) :
    ∃ g : SpecialLinearGroup (Fin 4) (ZMod 2), ρ' g u' = u := by
  have dec : ∀ w : V, w ∈ LinearMap.range P ⊔ LinearMap.range Pd → w ∉ LinearMap.range P →
      w ∉ LinearMap.range Pd → Q w = 0 →
      ∃ v φ : Fin 4 → ZMod 2, v ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ v = 0 ∧ w = P v + Pd φ := by
    intro w hw hwP hwPd hw0
    obtain ⟨p, ⟨v, rfl⟩, d, ⟨φ, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hw
    have hv : v ≠ 0 := by
      rintro rfl
      exact hwPd ⟨φ, by simp⟩
    have hφ : φ ≠ 0 := by
      rintro rfl
      exact hwP ⟨v, by simp⟩
    refine ⟨v, φ, hv, hφ, ?_, rfl⟩
    have h1 := QuadraticMap.map_add Q (P v) (Pd φ)
    rw [hP.map_eq_zero, hP.map_eq_zero_dual, hP.polar_eq_dotProduct hA hdim, zero_add,
      zero_add] at h1
    rw [← h1]
    exact hw0
  obtain ⟨v, φ, hv, hφ, hvφ, rfl⟩ := dec u hu huP huPd hu0
  obtain ⟨v', φ', hv', hφ', hvφ', rfl⟩ := dec u' hu' hu'P hu'Pd hu0'
  obtain ⟨g, hg1, hg2⟩ := exists_mulVec_eq_contra_eq hv' hφ' hvφ' hv hφ hvφ
  refine ⟨g, ?_⟩
  rw [map_add, ← hP.map_mulVec, ← hP.map_contra, hg1, hg2]

end CFSG.LargeExtraspecial.A2Mod
