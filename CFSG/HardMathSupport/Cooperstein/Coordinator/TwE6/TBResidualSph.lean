module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBResidualChar
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBResidualForm27

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))


private theorem exists_sph_factor {G : Type*} [Group G] [Finite G] {B : Type*}
    {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ}
    (D : CurtisDatum G cs p) (g : G) :
    ∃ h ∈ D.H, ∃ ω : List B, ∀ (k : Type) [Field k] (χ : G → k) (μ : B → k),
      D.sph χ μ g = χ h * D.coinvScalar χ μ ω :=
  ⟨(D.cover' g).choose.2.2.1, (D.cover' g).choose_spec.2.1,
    (cs.exists_isReduced (D.cover' g).choose.2.1).choose, fun _ _ _ _ => rfl⟩

open Classical in
theorem form_eq_ite_twChi27 {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ (Finset.univ.erase twN0))
    (hχ : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (w : (orbitField TwistTag.E6 K σ a)ˣ),
      χ (hatH hf hK σ hσ a w) = 1)
    {fm : Module.Dual k (Fin m → k)}
    (hfm : ∀ z ∈ augSub ρ (twistedE6CoverData hf hK σ hσ).datum.L, fm z = 0) (hfy : fm y = 1)
    (g : ↥(TwistedE6.fixedGroup K σ)) :
    fm (ρ g y) = if twChi27 σ g = 0 then 0 else 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (twistedCover_split hf hK σ hσ k)
  have ht27 := twRep27_isCoverType hf hK σ hσ
  obtain ⟨μ27, hμ27⟩ := ht27.exists_mu (isSimpleRep_twRep27 hf hK σ hσ)
    (twistedCover_split hf hK σ hσ K)
  obtain ⟨f27, hf27, hf27y⟩ := (twistedE6CoverData hf hK σ hσ).datum.exists_form
    (isSimpleRep_twRep27 hf hK σ hσ) hμ27.1 hμ27.2.1
  obtain ⟨h, hhH, ω, hsph⟩ := exists_sph_factor (twistedE6CoverData hf hK σ hσ).datum g
  have hfa : fm (ρ g y) = (twistedE6CoverData hf hK σ hσ).datum.sph χ μ g :=
    (twistedE6CoverData hf hK σ hσ).datum.form_act ρ hfm hμ hfy g
  have hfa27 : f27 (twRep27 σ g (e6Y27 : Fin e6Data.d →₀ K)) =
      (twistedE6CoverData hf hK σ hσ).datum.sph (twChi27 σ) μ27 g :=
    (twistedE6CoverData hf hK σ hσ).datum.form_act (twRep27 σ) hf27 hμ27 hf27y g
  have hcoord : f27 (twRep27 σ g (e6Y27 : Fin e6Data.d →₀ K)) = twChi27 σ g :=
    form27_eq_coord hf hK σ hσ hf27 hf27y _
  have hχh : χ h = 1 := chi_eq_one_of_hatH hf hK σ hσ ht hχ h hhH
  have hH27 : twChi27 σ h ≠ 0 := by
    intro h0
    have e := twRep27_H hf hK σ hσ h hhH
    rw [h0, zero_smul] at e
    have h1 : twRep27 σ h⁻¹ (twRep27 σ h (e6Y27 : Fin e6Data.d →₀ K)) = e6Y27 := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [e, map_zero] at h1
    exact e6Y27_ne_zero h1.symm
  have hiff : twChi27 σ g = 0 ↔ twN0 ∈ ω := by
    have hchi27 : twChi27 σ g = twChi27 σ h *
        (twistedE6CoverData hf hK σ hσ).datum.coinvScalar (twChi27 σ) μ27 ω := by
      rw [← hcoord, hfa27, hsph K (twChi27 σ) μ27]
    rw [hchi27, mul_eq_zero, or_iff_right hH27]
    exact coinvScalar_twRep27 hf hK σ hσ hμ27 ω
  have hres := coinvScalar_residual hf hK σ hσ ht hχ hμ ω
  rw [hfa, hsph k χ μ, hχh, one_mul, hres]
  by_cases hω : twN0 ∈ ω
  · rw [if_pos hω, if_pos (hiff.2 hω)]
  · have hn : ¬ (twChi27 σ g = 0) := fun h0 => hω (hiff.1 h0)
    rw [if_neg hω, if_neg hn]

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
