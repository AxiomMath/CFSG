module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLSemilinearInvolution
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenLinearTwoOutcome
public import CFSG.GroupTheory.LocalCores.Components

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank

namespace EvenLinearSL

theorem generalizedFitting_normal' (X : Type*) [Group X] : (CFSG.generalizedFitting X).Normal :=
  CFSG.LocalCores.generalized_fitting_characteristic.2

theorem conj_mem_generalizedFitting {X : Type*} [Group X] (x : X)
    (y : CFSG.generalizedFitting X) : x * (y : X) * x⁻¹ ∈ CFSG.generalizedFitting X :=
  (generalizedFitting_normal' X).conj_mem y y.2 x

@[expose] def conjModel {X : Type*} [Group X] {P : Type*} [Group P]
    (θ : CFSG.generalizedFitting X ≃* P) : X →* MulAut P :=
  (MulAut.congr θ).toMonoidHom.comp (@MulAut.conjNormal X _ (CFSG.generalizedFitting X)
    (generalizedFitting_normal' X))

theorem conjModel_apply {X : Type*} [Group X] {P : Type*} [Group P]
    (θ : CFSG.generalizedFitting X ≃* P) (x : X) (y : CFSG.generalizedFitting X) :
    conjModel θ x (θ y) = θ ⟨x * (y : X) * x⁻¹, conj_mem_generalizedFitting x y⟩ := by
  change θ (@MulAut.conjNormal X _ (CFSG.generalizedFitting X) (generalizedFitting_normal' X) x
    (θ.symm (θ y))) = _
  rw [MulEquiv.symm_apply_apply]
  congr 1

theorem conjModel_of_mem {X : Type*} [Group X] {P : Type*} [Group P]
    (θ : CFSG.generalizedFitting X ≃* P) (y : CFSG.generalizedFitting X) :
    conjModel θ (y : X) = MulAut.conj (θ y) := by
  ext p
  obtain ⟨q, rfl⟩ := θ.surjective p
  rw [conjModel_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (mem_center_iff.mp (h ▸ mem_top b) a)

end EvenLinearSL

open EvenLinearSL

theorem even_linear_higher_almost_simple_graph_coset_reduction {X : Type} [Group X] [Finite X]
    [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) {n f : ℕ} (hn : 3 ≤ n)
    (hf : 1 ≤ f) (hmodel : StatedClassicalModel (CFSG.generalizedFitting X) .PSL n 2 f) :
    (∃ (K : Type) (_ : Field K), Nat.card K = 2 ^ f ∧
      Nonempty (CFSG.generalizedFitting X ≃* projectiveSL n K)) ∧
    ∀ (K : Type*) [Field K], Nat.card K = 2 ^ f →
      ∀ θ : CFSG.generalizedFitting X ≃* projectiveSL n K,
        (∀ (x : X) (y : CFSG.generalizedFitting X),
          conjModel θ x (θ y) = θ ⟨x * (y : X) * x⁻¹, conj_mem_generalizedFitting x y⟩) ∧
        Function.Injective (conjModel θ) ∧
        (CFSG.generalizedFitting X).map (conjModel θ) = inner (projectiveSL n K) ∧
        (∀ z : X, orderOf z = 2 → conjModel θ z ∈ semilinearAutGroup n K →
          CFSG.oddCore ↥(centralizer {z}) = ⊥) ∧
        (∀ z : X, orderOf z = 2 → CFSG.oddCore ↥(centralizer {z}) ≠ ⊥ →
          conjModel θ z ∉ semilinearAutGroup n K ∧ z ∉ CFSG.generalizedFitting X ∧
          CFSG.generalizedFitting X < ⊤) := by
  set F := CFSG.generalizedFitting X with hF
  refine ⟨?_, fun K _ hK θ => ?_⟩
  · obtain ⟨-, K, hKf, -, hcard, ⟨e⟩⟩ := hmodel
    exact ⟨K, hKf, hcard, ⟨(e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)⟩⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  set ρ := conjModel θ with hρ
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : x ∈ centralizer (F : Set X) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun φ : MulAut (projectiveSL n K) => φ (θ ⟨y, hy⟩)) hx
      simp only [MulAut.one_apply] at h1
      rw [hρ, conjModel_apply] at h1
      have h2 := congrArg Subtype.val (θ.injective h1)
      simp only at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    have hxF : x ∈ F := CFSG.centralizer_generalizedFitting_le X hxC
    have hcen : (⟨x, hxF⟩ : F) ∈ center F := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hxC y y.2)
    rw [center_eq_bot_of_simple hnonab, mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have himage : F.map ρ = inner (projectiveSL n K) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨θ ⟨y, hy⟩, (conjModel_of_mem θ ⟨y, hy⟩).symm⟩
    · rintro _ ⟨p, rfl⟩
      obtain ⟨y, rfl⟩ := θ.surjective p
      exact ⟨y, y.2, conjModel_of_mem θ y⟩
  have hinnH : inner (projectiveSL n K) ≤ ρ.range := by
    rw [← himage]
    exact map_le_range ρ F
  have hodd : ∀ z : X, orderOf z = 2 → ρ z ∈ semilinearAutGroup n K →
      CFSG.oddCore ↥(centralizer {z}) = ⊥ := by
    intro z hz hzE
    have hρz : orderOf (ρ z) = 2 := by rw [orderOf_injective ρ hinj z, hz]
    have h1 := even_linear_semilinear_involution_full_centralizer_odd_core hn hf hK hinnH hzE hρz
    exact EvenCatalog.oddCore_eq_bot_of_mulEquiv (EvenCatalog.centralizerMapEquiv hinj z).symm h1
  refine ⟨conjModel_apply θ, hinj, himage, hodd, fun z hz hne => ?_⟩
  have hzE : ρ z ∉ semilinearAutGroup n K := fun h => hne (hodd z hz h)
  have hzF : z ∉ F := by
    intro hzF
    apply hzE
    have h1 : ρ z ∈ inner (projectiveSL n K) := himage ▸ mem_map_of_mem ρ hzF
    exact linearAutGroup_le_semilinearAutGroup ((standard_outer_quotients (K := K) (n := n)).1 h1)
  exact ⟨hzE, hzF, lt_top_iff_ne_top.mpr fun htop => hzF (by rw [hF, htop]; trivial)⟩

end CFSG.ComponentClassification.UnbalancedCatalog
