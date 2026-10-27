module

public import CFSG.HardMathSupport.Lang.AnisoE6.ThirdA2
public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2Split

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.TwE6Step3

set_option linter.unusedSectionVars false

variable {τ : Tag} (K : Type) [Field K]

section


theorem nElt_inv_conj (ω : List (Fin τ.rank)) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K,
      (nElt τ K ω)⁻¹ * pinnedX τ K α c * nElt τ K ω =
        pinnedX τ K (((coxeterSystem τ).wordProd ω)⁻¹ • α) (ε * c) := by
  induction ω generalizing α with
  | nil => exact ⟨1, one_mul 1, fun c => by simp [nElt]⟩
  | cons i ω ih =>
    have hα' : IsRoot τ (reflect τ i α) := IsRoot.reflect i hα
    obtain ⟨ε₁, hε₁, h₁⟩ := weylElt_mul_pinnedX_mul_inv K i hα'
    obtain ⟨ε₂, hε₂, h₂⟩ := ih hα'
    have hs : reflect τ i (reflect τ i α) = α := by
      rw [← simple_smul, ← simple_smul, ← mul_smul, (coxeterSystem τ).simple_mul_simple_self,
        one_smul]
    refine ⟨ε₂ * ε₁, by linear_combination (ε₂ * ε₂) * hε₁ + hε₂, fun c => ?_⟩
    have hstep : (weylElt τ K i 1)⁻¹ * pinnedX τ K α c * weylElt τ K i 1 =
        pinnedX τ K (reflect τ i α) (ε₁ * c) := by
      have h := h₁ (ε₁ * c)
      rw [hs, ← mul_assoc, hε₁, one_mul] at h
      rw [← h]
      group
    have e : (nElt τ K (i :: ω))⁻¹ * pinnedX τ K α c * nElt τ K (i :: ω) =
        (nElt τ K ω)⁻¹ * ((weylElt τ K i 1)⁻¹ * pinnedX τ K α c * weylElt τ K i 1) *
          nElt τ K ω := by
      simp only [nElt, List.map_cons, List.prod_cons, mul_inv_rev]
      group
    rw [e, hstep, h₂ (ε₁ * c), (coxeterSystem τ).wordProd_cons, mul_inv_rev, mul_smul]
    have hinv : ((coxeterSystem τ).simple i)⁻¹ = (coxeterSystem τ).simple i :=
      (coxeterSystem τ).inv_simple i
    rw [hinv, simple_smul, mul_assoc]

theorem nElt_inv_conj_mem_rootSpan (ω : List (Fin τ.rank)) {S S' : Set (Fin τ.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot τ γ ∧ ((coxeterSystem τ).wordProd ω)⁻¹ • γ ∈ S')
    {g : ModGL τ K} (hg : g ∈ rootSpan τ K S) :
    (nElt τ K ω)⁻¹ * g * nElt τ K ω ∈ rootSpan τ K S' := by
  have hF : ∀ γ ∈ S, ∀ c : K, ∃ d : K,
      (MulAut.conj (nElt τ K ω)⁻¹).toMonoidHom (pinnedX τ K γ c) =
        pinnedX τ K (((coxeterSystem τ).wordProd ω)⁻¹ • γ) d := by
    intro γ hγ c
    obtain ⟨ε, -, hε⟩ := nElt_inv_conj K ω (hS γ hγ).1
    refine ⟨ε * c, ?_⟩
    have := hε c
    simpa [MulAut.conj_apply] using this
  have := map_mem_rootSpan (MulAut.conj (nElt τ K ω)⁻¹).toMonoidHom
    (fun γ => ((coxeterSystem τ).wordProd ω)⁻¹ • γ) hF (fun γ hγ => (hS γ hγ).2) hg
  simpa [MulAut.conj_apply] using this

theorem commute_of_forall_pinnedX {S : Set (Fin τ.rank → ℤ)} {e g : ModGL τ K}
    (h : ∀ γ ∈ S, ∀ c : K, Commute e (pinnedX τ K γ c)) (hg : g ∈ rootSpan τ K S) :
    Commute e g := by
  have hle : rootSpan τ K S ≤ Subgroup.centralizer {e} := by
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (h γ hγ c).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

end

end CFSG.HardMathSupport.Lang.AnisoE6
