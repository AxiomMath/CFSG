module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace SpChain

section ConjRep

variable {X P : Type*} [Group X] [Group P]

theorem exists_conjRep {F : Subgroup X} [F.Normal] (θ : F ≃* P) :
    ∃ ρ : X →* MulAut P, ∀ (x : X) (y z : F), (z : X) = x * y * x⁻¹ → ρ x (θ y) = θ z := by
  refine ⟨(MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal, fun x y z hz => ?_⟩
  change θ (MulAut.conjNormal x (θ.symm (θ y))) = θ z
  rw [MulEquiv.symm_apply_apply]
  congr 1
  exact Subtype.ext (by rw [MulAut.conjNormal_apply, hz])

theorem conjRep_facts {F : Subgroup X} [F.Normal]
    (hC : Subgroup.centralizer (F : Set X) ≤ F) (hZ : Subgroup.center F = ⊥) (θ : F ≃* P)
    {ρ : X →* MulAut P} (hρ : ∀ (x : X) (y z : F), (z : X) = x * y * x⁻¹ → ρ x (θ y) = θ z) :
    Function.Injective ρ ∧ (∀ y : F, ρ y = MulAut.conj (θ y)) ∧ F.map ρ = inner P ∧
      ∀ z : X, z ∈ F ↔ ρ z ∈ inner P := by
  have hρF : ∀ y : F, ρ y = MulAut.conj (θ y) := by
    intro y
    refine MulEquiv.ext fun p => ?_
    obtain ⟨y', rfl⟩ := θ.surjective p
    rw [hρ y y' (y * y' * y⁻¹) (by simp), MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxC : x ∈ Subgroup.centralizer (F : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hρ x ⟨y, hy⟩ ⟨x * y * x⁻¹, (inferInstance : F.Normal).conj_mem y hy x⟩ rfl
      rw [hx, MulAut.one_apply] at h1
      have h2 := congrArg Subtype.val (θ.injective h1)
      change y = x * y * x⁻¹ at h2
      calc y * x = x * y * x⁻¹ * x := by rw [← h2]
        _ = x * y := by group
    have hxF : x ∈ F := hC hxC
    have hxZ : (⟨x, hxF⟩ : F) ∈ Subgroup.center F :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hxZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxZ
  have hmap : F.map ρ = inner P := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨θ ⟨y, hy⟩, (hρF ⟨y, hy⟩).symm⟩
    · rintro _ ⟨p, rfl⟩
      obtain ⟨y, rfl⟩ := θ.surjective p
      exact ⟨y, y.2, hρF y⟩
  refine ⟨hinj, hρF, hmap, fun z => ⟨fun hz => hmap ▸ ⟨z, hz, rfl⟩, fun hz => ?_⟩⟩
  rw [← hmap] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  rwa [← hinj hyz]

end ConjRep

theorem generalizedFitting_facts {X : Type} [Group X] [Finite X]
    [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) :
    Subgroup.centralizer (CFSG.generalizedFitting X : Set X) ≤ CFSG.generalizedFitting X ∧
      Subgroup.center (CFSG.generalizedFitting X) = ⊥ := by
  refine ⟨CFSG.centralizer_generalizedFitting_le X, ?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (CFSG.generalizedFitting X))
    with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have hb : b ∈ Subgroup.center (CFSG.generalizedFitting X) := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

end SpChain

open SpChain

theorem even_symplectic_almost_simple_field_involution_exclusion {X : Type} [Group X]
    [Finite X] [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) {r f : ℕ}
    (hmodel : StatedClassicalModel (CFSG.generalizedFitting X) .PSp r 2 f) :
    2 ≤ r ∧ 1 ≤ f ∧
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      Nonempty (CFSG.generalizedFitting X ≃* StatedProj (StatedSp r K))) ∧
    ∀ (K : Type) [Field K], Nat.card K = 2 ^ f →
      ∀ θ : CFSG.generalizedFitting X ≃* StatedProj (StatedSp r K),
        (∃ ρ : X →* MulAut (StatedProj (StatedSp r K)), ∀ (x : X)
          (y z : CFSG.generalizedFitting X), (z : X) = x * y * x⁻¹ → ρ x (θ y) = θ z) ∧
        ∀ ρ : X →* MulAut (StatedProj (StatedSp r K)),
          (∀ (x : X) (y z : CFSG.generalizedFitting X), (z : X) = x * y * x⁻¹ →
            ρ x (θ y) = θ z) →
          Function.Injective ρ ∧
          (CFSG.generalizedFitting X).map ρ = inner (StatedProj (StatedSp r K)) ∧
          (∀ z : X, orderOf z = 2 → z ∉ CFSG.generalizedFitting X →
            ρ z ∈ spSemilinearAutGroup r K →
            CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥) ∧
          (3 ≤ r → ∀ z : X, ρ z ∈ spSemilinearAutGroup r K) ∧
          ∀ z : X, orderOf z = 2 → CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) ≠ ⊥ →
            z ∈ CFSG.generalizedFitting X ∨ (r = 2 ∧ ρ z ∉ spSemilinearAutGroup r K) := by
  set F := CFSG.generalizedFitting X with hFdef
  have hFn : F.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  obtain ⟨hC, hZ⟩ := generalizedFitting_facts hnonab
  obtain ⟨⟨-, hf1, hr2, -⟩, hK⟩ := hmodel
  refine ⟨hr2, hf1, hK, fun K _ hcard θ => ⟨exists_conjRep θ, fun ρ hρ => ?_⟩⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf1 hcard
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hρinj, -, hmap, hmemF⟩ := conjRep_facts hC hZ θ hρ
  set E := spSemilinearAutGroup r K with hEdef
  have hIH : inner (StatedProj (StatedSp r K)) ≤ ρ.range := by
    rw [← hmap]
    exact Subgroup.map_le_range ρ F
  have hvan : ∀ z : X, orderOf z = 2 → z ∉ F → ρ z ∈ E →
      CFSG.oddCore ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ := by
    intro z hz hzF hzE
    rw [oddCore_centralizer_eq_bot_iff hρinj z]
    have haI : ρ z ∉ inner (StatedProj (StatedSp r K)) := fun h => hzF ((hmemF z).mpr h)
    have hao : orderOf (ρ z) = 2 := by rw [orderOf_injective ρ hρinj z, hz]
    obtain ⟨g, φ, hgφ⟩ := exists_eq_spInner_mul_fieldAut hzE
    have hφ1 : φ ≠ 1 := (spInner_mul_fieldAut_not_mem_inner_iff g φ).mp (hgφ ▸ haI)
    have haa : ρ z * ρ z = 1 := by rw [← sq, ← hao, pow_orderOf_eq_one]
    obtain ⟨hfe, hφform, -⟩ :=
      even_symplectic_quadratic_involution_descent (by omega) hf1 hcard haa g φ hgφ hφ1
    have hf2 : 2 ≤ f := by obtain ⟨m, hm⟩ := hfe; omega
    obtain ⟨-, -, -, -, -, hcore⟩ :=
      even_symplectic_field_centralizers_and_intermediate_odd_cores hr2 hf2 hfe hcard φ hφform
    have h₀ := hcore (ρ.range ⊓ E) (le_inf hIH inner_le_spSemilinearAutGroup) inf_le_right
      (ρ z) (Subgroup.mem_inf.mpr ⟨⟨z, rfl⟩, hzE⟩) hao haI
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    · obtain rfl : r = 2 := by omega
      obtain ⟨-, -, hEn, hEi⟩ :=
        CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := K)
      exact oddCore_eq_bot_of_index_le_two hEi h₀
    · have hEtop : E = ⊤ := (automorphism_generation (K := K) hr3).1
      rw [hEtop, inf_top_eq] at h₀
      exact h₀
  have hall : 3 ≤ r → ∀ z : X, ρ z ∈ E := fun hr3 z => by
    have hEtop : E = ⊤ := (automorphism_generation (K := K) hr3).1
    rw [hEtop]
    exact Subgroup.mem_top _
  refine ⟨hρinj, hmap, hvan, hall, fun z hz hne => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hzF, hr⟩ := hcon
  by_cases hzE : ρ z ∈ E
  · exact hne (hvan z hz hzF hzE)
  · rcases Nat.lt_or_ge r 3 with hr3 | hr3
    · exact hzE (hr (by omega))
    · exact hzE (hall hr3 z)

end CFSG.ComponentClassification.UnbalancedCatalog
