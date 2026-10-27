module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParam
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldTwist
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

local instance e6PilotCoverFamilyA3NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section A3

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem FieldNeighbourCover.exists_section_a3 {N : E6Neighbour} (h : FieldNeighbourCover σ e N)
    (hK : 5 ≤ Nat.card K) (hN : ({0, 2, 3} : Finset (Fin (Tag.rank .E6))) ⊆ N.nodes) :
    ∃ s : (a3Levi K).subgroupOf (N.levi K) →* neighbourCore e N, ∀ x, h.p (s x) = x := by
  set H := (a3Levi K).subgroupOf (N.levi K) with hH
  have hAN : a3Levi K ≤ N.levi K := levi_le_neighbourLevi hN
  set lam : SpecialLinearGroup (Fin 4) K ≃* H :=
    ((MonoidHom.ofInjective (a3Hom_injective (K := K))).trans
      (MulEquiv.subgroupCongr range_a3Hom)).trans (subgroupOfEquivOfLe hAN).symm with hlam
  set E' := H.comap h.p with hE'
  set π : E' →* SpecialLinearGroup (Fin 4) K :=
    lam.symm.toMonoidHom.comp ((h.p.comp E'.subtype).codRestrict H fun x => x.2) with hπ
  have hπs : Function.Surjective π := by
    intro g
    obtain ⟨y, hy⟩ := h.surjective (lam g : N.levi K)
    have hyE : y ∈ E' := by
      rw [hE', mem_comap, hy]
      exact (lam g).2
    refine ⟨⟨y, hyE⟩, ?_⟩
    change lam.symm ⟨h.p y, _⟩ = g
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hy
  have hπc : π.ker ≤ center E' := by
    intro y hy
    have h1 : h.p (y : neighbourCore e N) = 1 := by
      have h2 : ((h.p.comp E'.subtype).codRestrict H fun x => x.2) y = 1 := by
        have := (MonoidHom.mem_ker).1 hy
        rw [hπ, MonoidHom.comp_apply] at this
        exact lam.symm.injective (this.trans (map_one _).symm)
      exact congrArg Subtype.val h2
    have hz : (y : neighbourCore e N) ∈ center (neighbourCore e N) := h.ker_le_center h1
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.1 hz g)
  obtain ⟨s₀, hs₀⟩ := LinearPilot.exists_section_specialLinear (by norm_num : 3 ≤ 4) hK hπs hπc
  refine ⟨E'.subtype.comp (s₀.comp lam.symm.toMonoidHom), fun x => ?_⟩
  have h1 := hs₀ (lam.symm x)
  rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, lam.symm.injective.eq_iff] at h1
  exact congrArg Subtype.val h1

end A3

section Lift

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem FieldNeighbourCover.exists_sl6Lift (h : FieldNeighbourCover σ e .high)
    (hK : 5 ≤ Nat.card K) :
    ∃ Ψ : Matrix.SpecialLinearGroup (Fin 6) K →* neighbourCore e .high, ∀ A,
      (((h.p (Ψ A) : E6Neighbour.high.levi K) : adjointGroup .E6 K)) = slToAdjointE6 K A := by
  set β : Matrix.SpecialLinearGroup (Fin 6) K →* E6Neighbour.high.levi K :=
    (MulEquiv.subgroupCongr (E6Neighbour.levi_high K).symm).toMonoidHom.comp slToA5Levi with hβ
  obtain ⟨s, hs⟩ := LinearPilot.exists_section_specialLinear (by norm_num : 3 ≤ 6) hK
    (CFSG.LieType.Steinberg.pullbackFst_surjective (β := β) h.surjective)
    (CFSG.LieType.Steinberg.ker_pullbackFst_le_center h.ker_le_center)
  refine ⟨((MonoidHom.snd _ _).comp (CFSG.LieType.Steinberg.pullback β h.p).subtype).comp s,
    fun A => ?_⟩
  have hmem := CFSG.LieType.Steinberg.mem_pullback.1 (s A).2
  have h1 : ((s A : CFSG.LieType.Steinberg.pullback β h.p) :
      Matrix.SpecialLinearGroup (Fin 6) K × neighbourCore e .high).1 = A := hs A
  change (((h.p ((s A : CFSG.LieType.Steinberg.pullback β h.p) :
    Matrix.SpecialLinearGroup (Fin 6) K × neighbourCore e .high).2 : E6Neighbour.high.levi K)) :
      adjointGroup .E6 K) = _
  rw [← hmem, h1]
  rfl

end Lift

end CFSG.SeitzReduction.E6Pilot
