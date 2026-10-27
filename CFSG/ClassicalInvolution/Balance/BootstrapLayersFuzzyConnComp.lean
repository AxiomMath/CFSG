module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyLink

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

section Components

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}
  (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)

include hs in
theorem SecData.exists_comp {K : Subgroup G} (hK : K ∈ Φ) :
    ∃ j : Fin D.card, modOdd a K ≤ (secComponentHom hs.normalizes D j).range := by
  obtain ⟨j, R, -, hR⟩ := hs.exists_fundamental D hK
  exact ⟨j, hR ▸ Subgroup.map_le_range _ _⟩

include hs in
theorem SecData.comp_unique {K : Subgroup G} (hK : K ∈ Φ) {i j : Fin D.card}
    (hi : modOdd a K ≤ (secComponentHom hs.normalizes D i).range)
    (hj : modOdd a K ≤ (secComponentHom hs.normalizes D j).range) : i = j := by
  have hM : K ∈ centMembers Φ a := ⟨hK, hs.le K hK⟩
  obtain ⟨R, -, hR⟩ := exists_fundamental_of_modOdd_le_sec hs D i hM hi
  obtain ⟨R', -, hR'⟩ := exists_fundamental_of_modOdd_le_sec hs D j hM hj
  exact hs.eq_of_map_eq D hK hR hR'

include hs in
theorem SecData.comm_of_ne {i j : Fin D.card} (hij : i ≠ j) {x y : OddQuot a}
    (hx : x ∈ (secComponentHom hs.normalizes D i).range)
    (hy : y ∈ (secComponentHom hs.normalizes D j).range) : x * y = y * x := by
  obtain ⟨r, rfl⟩ := hx
  obtain ⟨r', rfl⟩ := hy
  have key := D.commute i j hij r r'
  exact (map_mul (sectionQuotientHom hs.normalizes) (D.hom i r) (D.hom j r')).symm.trans
    ((congrArg (sectionQuotientHom hs.normalizes) key).trans
      (map_mul (sectionQuotientHom hs.normalizes) (D.hom j r') (D.hom i r)))

include hs in
theorem SecData.exists_decomp_indices
    (D' : LieDecomposition (memberImages Φ a) (memberJoin Φ a))
    (hD'Q : ∀ i, D'.Q i ∈ Set.range fun j : Fin D.card =>
      ((sectionQuotientHom hs.normalizes).comp (D.hom j)).range)
    {K K' : Subgroup G} (hK : K ∈ Φ) (hK' : K' ∈ Φ) {j₁ j₂ : Fin D.card} (hj : j₁ ≠ j₂)
    (h₁ : modOdd a K ≤ (secComponentHom hs.normalizes D j₁).range)
    (h₂ : modOdd a K' ≤ (secComponentHom hs.normalizes D j₂).range) :
    ∃ i₁ i₂ : D'.ι, i₁ ≠ i₂ ∧ modOdd a K ≤ D'.Q i₁ ∧ modOdd a K' ≤ D'.Q i₂ := by
  obtain ⟨i₁, hi₁⟩ := D'.exists_le (modOdd a K) ⟨K, ⟨hK, hs.le K hK⟩, rfl⟩
  obtain ⟨i₂, hi₂⟩ := D'.exists_le (modOdd a K') ⟨K', ⟨hK', hs.le K' hK'⟩, rfl⟩
  obtain ⟨k₁, hk₁⟩ := hD'Q i₁
  obtain ⟨k₂, hk₂⟩ := hD'Q i₂
  have hk₁' : (secComponentHom hs.normalizes D k₁).range = D'.Q i₁ := hk₁
  have hk₂' : (secComponentHom hs.normalizes D k₂).range = D'.Q i₂ := hk₂
  have e₁ : modOdd a K ≤ (secComponentHom hs.normalizes D k₁).range := by
    rw [hk₁']
    exact hi₁
  have e₂ : modOdd a K' ≤ (secComponentHom hs.normalizes D k₂).range := by
    rw [hk₂']
    exact hi₂
  have hk₁j : k₁ = j₁ := hs.comp_unique D hK e₁ h₁
  have hk₂j : k₂ = j₂ := hs.comp_unique D hK' e₂ h₂
  refine ⟨i₁, i₂, fun h => hj ?_, hi₁, hi₂⟩
  subst h
  have e₃ : modOdd a K ≤ (secComponentHom hs.normalizes D k₂).range := by
    rw [hk₂']
    exact hi₁
  rw [← hk₁j, ← hk₂j]
  exact hs.comp_unique D hK e₁ e₃

end Components

section Conjugation

variable {G : Type} [Group G] {a : G}

theorem modOdd_conjSub_of_mem_oddCoreIn {K : Subgroup G} {x : G}
    (hx : x ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G))) :
    modOdd a (conjSub x K) = modOdd a K := by
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := oddCoreIn_le _ hx
  have hx1 : oddQuotMk a ⟨x, hxC⟩ = 1 := oddQuotMk_eq_one_of_mem_oddCoreIn hx hxC
  ext y
  rw [mem_modOdd_iff, mem_modOdd_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : x⁻¹ * (k : G) * x ∈ K := mem_conjSub_iff.mp hk
    have hkC : x⁻¹ * (k : G) * x ∈ Subgroup.centralizer ({a} : Set G) :=
      mul_mem (mul_mem (inv_mem hxC) k.2) hxC
    refine ⟨⟨x⁻¹ * (k : G) * x, hkC⟩, hk', ?_⟩
    have e : (⟨x⁻¹ * (k : G) * x, hkC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) =
        ⟨x, hxC⟩⁻¹ * k * ⟨x, hxC⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, hx1]
    simp
  · rintro ⟨k, hk, rfl⟩
    have hk' : x * (k : G) * x⁻¹ ∈ conjSub x K := conj_mem_conjSub hk
    have hkC : x * (k : G) * x⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
      mul_mem (mul_mem hxC k.2) (inv_mem hxC)
    refine ⟨⟨x * (k : G) * x⁻¹, hkC⟩, hk', ?_⟩
    have e : (⟨x * (k : G) * x⁻¹, hkC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) =
        ⟨x, hxC⟩ * k * ⟨x, hxC⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hx1]
    simp

end Conjugation

section Residual

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem oddQuotMk_centralizes_triangleResidual {J : Subgroup G} {t a s : G}
    (hJ : IsClassicalMember p f J t) (ha2 : a * a = 1) (haJ : a ∈ trivialOnQuot J)
    (hqs : CFSG.Open.IsQuasisimple ↥(modOdd a (triangleResidual J a)))
    (hsJ : s ∈ trivialOnQuot J) (hsC : s ∈ Subgroup.centralizer ({a} : Set G)) :
    ∀ y ∈ modOdd a (triangleResidual J a),
      oddQuotMk a ⟨s, hsC⟩ * y = y * oddQuotMk a ⟨s, hsC⟩ :=
  oddQuotMk_centralizes_of_commutator_mem (isSectionMember_triangleResidual hJ ha2 haJ).le hsC hqs
    fun _ hl => commutator_mem_oddCoreIn_triangleResidual hsJ hsC (axisResidual_single hJ ha2 haJ)
      hl

end Residual

end CFSG.ClassicalInvolution.Balance.Bootstrap
