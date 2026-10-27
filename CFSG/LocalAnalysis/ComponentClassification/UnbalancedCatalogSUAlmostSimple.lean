module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLGraphCoset

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank EvenLinearSL

theorem even_unitary_almost_simple_odd_core_vanishing {X : Type} [Group X] [Finite X]
    [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) {n f : ℕ}
    (hmodel : StatedClassicalModel (CFSG.generalizedFitting X) .PSU n 2 f) :
    (3 ≤ n ∧ 1 ≤ f ∧ (n, 2 ^ f) ≠ (3, 2)) ∧
    ∀ z : X, orderOf z = 2 → CFSG.oddCore ↥(centralizer {z}) = ⊥ := by
  set F := CFSG.generalizedFitting X with hF
  obtain ⟨-, hf, hn, hq⟩ := hmodel.1
  have hq' : ¬(n = 3 ∧ 2 ^ f = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  refine ⟨⟨hn, hf, hq⟩, fun z hz => ?_⟩
  obtain ⟨K, _, h, ⟨e⟩⟩ := (unitary_classical_model_outer_normalizer hmodel).1
  obtain ⟨ψ⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := n) (K := K))
  set θ : F ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := e.trans ψ.symm
  set ρ := conjModel θ with hρ
  have := EvenCatalog.finite_mulAut_primeFormP (C := (1 : GL (Fin n) K)) h
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : x ∈ centralizer (F : Set X) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun φ : MulAut (primeFormP h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) => φ (θ ⟨y, hy⟩)) hx
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
  have hinner : inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≤
      ρ.range := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨y, rfl⟩ := θ.surjective p
    exact ⟨y, conjModel_of_mem θ y⟩
  have hρz : orderOf (ρ z) = 2 := by rw [orderOf_injective ρ hinj z, hz]
  have h1 := even_unitary_all_involution_full_centralizer_odd_core h isPrimeFormGram_one hn hq'
    hinner (ρ z) ⟨z, rfl⟩ hρz
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv (EvenCatalog.centralizerMapEquiv hinj z).symm h1

end CFSG.ComponentClassification.UnbalancedCatalog
