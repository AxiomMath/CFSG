module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ2

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.SimplyLacedCover PairFrame

set_option linter.unusedSectionVars false

section Set

variable {τ : Tag} {L : Type} [Field L]

theorem commute_rootSpan_of_conj_gens {Ψ : Set (Fin τ.rank → ℤ)} {zu z : ModGL τ L}
    (hnorm : ∀ g : ModGL τ L, g ∈ rootSpan τ L Ψ ↔ zu * g * zu⁻¹ ∈ rootSpan τ L Ψ)
    (hgen : ∀ γ ∈ Ψ, ∀ c : L,
      z * (zu * pinnedX τ L γ c * zu⁻¹) = (zu * pinnedX τ L γ c * zu⁻¹) * z) :
    ∀ g ∈ rootSpan τ L Ψ, Commute z g := by
  have hmap : (rootSpan τ L Ψ).map (MulAut.conj zu).toMonoidHom ≤ Subgroup.centralizer {z} := by
    simp only [rootSpan, Subgroup.map_iSup]
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hgen γ hγ c).symm
  intro g hg
  have hg' : zu⁻¹ * g * zu ∈ rootSpan τ L Ψ := by
    refine (hnorm _).2 ?_
    have : zu * (zu⁻¹ * g * zu) * zu⁻¹ = g := by group
    rw [this]
    exact hg
  have hcalc : (MulAut.conj zu).toMonoidHom (zu⁻¹ * g * zu) = g := by
    show zu * (zu⁻¹ * g * zu) * zu⁻¹ = g
    group
  have hmem : g ∈ Subgroup.centralizer {z} := hmap (Subgroup.mem_map.2 ⟨_, hg', hcalc⟩)
  exact Commute.symm (Subgroup.mem_centralizer_singleton_iff.1 hmem)

end Set

section Two

variable {τ : Tag} {L : Type} [Field L]

theorem commute_rootSpan_of_conj_gens_two [CharP L 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ) (hneg : ∀ γ ∈ Ψ, -γ ∈ Ψ)
    (hadj : ∀ α ∈ Ψ, ∃ δ ∈ Ψ, iform α δ = 1) {zu z : ModGL τ L}
    (hnorm : ∀ g : ModGL τ L, g ∈ rootSpan τ L Ψ ↔ zu * g * zu⁻¹ ∈ rootSpan τ L Ψ)
    (hz : ∀ γ ∈ Ψ,
      z * (zu * pinnedX τ L γ 1 * zu⁻¹) = (zu * pinnedX τ L γ 1 * zu⁻¹) * z) :
    ∀ g ∈ rootSpan τ L Ψ, Commute z g := by
  have hz' : ∀ γ ∈ Ψ, (zu⁻¹ * z * zu) * pinnedX τ L γ 1 = pinnedX τ L γ 1 * (zu⁻¹ * z * zu) := by
    intro γ hγ
    have := commute_conj_aux zu (hz γ hγ)
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel, mul_one]
      using this
  refine commute_rootSpan_of_conj_gens hnorm fun γ hγ c => ?_
  obtain ⟨δ, hδ, hγδ⟩ := hadj γ hγ
  have hδr := hΨ δ hδ
  have hγr := hΨ γ hγ
  have hsl := symmetrizer_diag_one hτ
  have hab : iform γ (-δ) = -1 := by
    rw [SimplyLacedCover.iform_neg_right, hγδ]
  have key := core_two_tag hτ (zu⁻¹ * z * zu) hγr (IsRoot.neg hδr) hab (hz' γ hγ)
    (hz' _ (hneg γ hγ)) (hz' _ (hneg δ hδ)) (by simpa only [neg_neg] using hz' δ hδ) c
  calc z * (zu * pinnedX τ L γ c * zu⁻¹)
      = zu * ((zu⁻¹ * z * zu) * pinnedX τ L γ c) * zu⁻¹ := by group
    _ = zu * (pinnedX τ L γ c * (zu⁻¹ * z * zu)) * zu⁻¹ := by rw [key]
    _ = (zu * pinnedX τ L γ c * zu⁻¹) * z := by group

end Two

end CFSG.HardMathSupport.Timmesfeld.LangTorus
