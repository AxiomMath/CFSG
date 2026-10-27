module

public import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

theorem normalizer_le_of_equivariant {p : ℕ} {Q M O D : Subgroup G}
    {θ : Subgroup G → Subgroup G} (hD : IsPPlane p D)
    (heq : ∀ D' : Subgroup G, IsPPlane p D' → ∀ g : G, θ (GLBConj g D') = GLBConj g (θ D'))
    (hO : ∀ y ∈ Subgroup.normalizer (Q : Set G), O ≤ θ (GLBConj y D))
    (hnorm : ∀ T : Subgroup G, O ≤ T → T ≤ θ D → Subgroup.normalizer (T : Set G) ≤ M) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  intro x hx
  have hOT : O ≤ ⨅ i : ℤ, θ (GLBConj (x ^ i) D) :=
    le_iInf fun i => hO (x ^ i) (Subgroup.zpow_mem _ hx i)
  have hTD : (⨅ i : ℤ, θ (GLBConj (x ^ i) D)) ≤ θ D := by
    have := iInf_le (fun i : ℤ => θ (GLBConj (x ^ i) D)) 0
    simpa [gLBConj_one] using this
  apply hnorm _ hOT hTD
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ∀ i : ℤ, x * h * x⁻¹ ∈ θ (GLBConj (x ^ i) D) ↔ h ∈ θ (GLBConj (x ^ (i + 1)) D) := by
    intro i
    have hpl : IsPPlane p (GLBConj (x ^ i) D) := isPPlane_gLBConj _ hD
    rw [← mem_gLBConj, ← heq _ hpl x, gLBConj_gLBConj, ← zpow_add_one]
  rw [Subgroup.mem_iInf, Subgroup.mem_iInf, forall_congr' key]
  refine ⟨fun hh i => hh (i + 1), fun hh i => ?_⟩
  have := hh (i - 1)
  rwa [sub_add_cancel] at this

end CFSG.LocalAnalysis.GLTheoremB
