module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLGraphCoset

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open EvenLinearSL

theorem even_G2_almost_simple_odd_core_vanishing {X : Type} [Group X] [Finite X]
    [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) {f : ℕ}
    (hmodel : CFSG.Blueprint.ChevalleyExceptionalModel (CFSG.generalizedFitting X) .G2 2 f) :
    2 ≤ f ∧ ∀ z : X, orderOf z = 2 → CFSG.oddCore ↥(centralizer {z}) = ⊥ := by
  set F := CFSG.generalizedFitting X with hF
  obtain ⟨⟨-, -, -, h3⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have hf : 2 ≤ f := by
    rcases Nat.lt_or_ge f 2 with h | h
    · interval_cases f <;> norm_num at h3
    · exact h
  refine ⟨hf, fun z hz => ?_⟩
  set θ : F ≃* adjointGroup .G2 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  set ρ := conjModel θ with hρ
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : x ∈ centralizer (F : Set X) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun φ : MulAut (adjointGroup .G2 K) => φ (θ ⟨y, hy⟩)) hx
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
  have hinner : inner (adjointGroup .G2 K) ≤ ρ.range := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨y, rfl⟩ := θ.surjective p
    exact ⟨y, conjModel_of_mem θ y⟩
  have hρz : orderOf (ρ z) = 2 := by rw [orderOf_injective ρ hinj z, hz]
  have h1 := even_G2_all_involution_full_centralizer_odd_core hf K hK ρ.range hinner hρz
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv (EvenCatalog.centralizerMapEquiv hinj z).symm h1

end CFSG.ComponentClassification.UnbalancedCatalog
