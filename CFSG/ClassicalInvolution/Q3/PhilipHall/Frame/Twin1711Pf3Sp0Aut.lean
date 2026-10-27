module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Model

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0Aut

open CFSG CFSG.ClassicalInvolution
open CFSG.Open (componentClassificationOddCore)
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ClassicalInvolution.Q3.TL4.Vtx (ringEquiv_eq_one_of_card_two)

theorem autInner_of_lieModel_PSp {M : Type} [Group M] [Finite M]
    (h : CFSG.Blueprint.LieModel M .PSp 3 2 1) : ∀ α : MulAut M, ∃ g : M, α = MulAut.conj g := by
  rcases h with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
    have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two le_rfl hK
    have : NeZero (3 : ℕ) := ⟨by norm_num⟩
    have hFin : Finite (StatedProj (StatedSp 3 K)) := Finite.of_equiv M e.toEquiv
    have key : ∀ α : MulAut (StatedProj (StatedSp 3 K)), α ∈ inner (StatedProj (StatedSp 3 K)) := by
      intro α
      have hE := (automorphism_generation (K := K) (r := 3) le_rfl).1
      obtain ⟨g, φ, hgφ⟩ := SpChain.exists_eq_spInner_mul_fieldAut
        (show α ∈ spSemilinearAutGroup 3 K by rw [hE]; exact Subgroup.mem_top α)
      by_contra hn
      exact ((SpChain.spInner_mul_fieldAut_not_mem_inner_iff g φ).1 (hgφ ▸ hn))
        (ringEquiv_eq_one_of_card_two hK2 φ)
    intro α
    obtain ⟨g, hg⟩ := key (e.symm.trans (α.trans e))
    refine ⟨e.symm g, ?_⟩
    apply MulEquiv.ext
    intro x
    have h1 := congrArg (fun γ : MulAut (StatedProj (StatedSp 3 K)) => γ (e x)) hg
    simp only [MulEquiv.trans_apply, MulAut.conj_apply] at h1 ⊢
    apply e.injective
    simpa using h1.symm
  all_goals exact absurd h0 (by norm_num)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0Aut
