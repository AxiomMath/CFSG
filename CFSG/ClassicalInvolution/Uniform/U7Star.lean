module

public import CFSG.ClassicalInvolution.Uniform.U7Inv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement


section Star

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace G2Comp

theorem aStar_subset_members (hΩ : HypOmegaModU (.sl2 3 1) Ω) (C : G2Comp Ω) {K : Subgroup G}
    (hK : K ∈ C.members) {J : Subgroup G} (hJ : J ∈ aStar Ω K) : J ∈ C.members := by
  induction hJ with
  | refl => exact hK
  | @tail B D _ hbc ih =>
    obtain ⟨hDΩ, h | h | ⟨ht, -⟩⟩ := hbc
    · obtain ⟨zB, zD, hv⟩ := h
      obtain ⟨a, hQ⟩ := quotViol_of_aViol_self_three hΩ ih.1 hv
      rcases C.cover D hDΩ with ⟨S, hS, hDS⟩ | hc
      · exact ⟨hDΩ, S, hS, hDS⟩
      · obtain ⟨-, R, -, rfl⟩ := ih
        exact (quotViol_false_of_commutes hQ fun x hx y hy =>
          hc y hy x (Subgroup.map_le_range _ _ hx) |>.symm).elim
    · obtain ⟨zD, zB, hv⟩ := h
      obtain ⟨a, hQ⟩ := quotViol_of_aViol_self_three hΩ hDΩ hv
      rcases C.cover D hDΩ with ⟨S, hS, hDS⟩ | hc
      · exact ⟨hDΩ, S, hS, hDS⟩
      · obtain ⟨-, R, -, rfl⟩ := ih
        exact (quotViol_false_of_commutes hQ fun x hx y hy =>
          hc x hx y (Subgroup.map_le_range _ _ hy)).elim
    · exact C.twin_mem_members ih ht

end G2Comp

variable {z j a : G}

theorem mem_aStar_of_g2_three (hgen : G2NonToralGenerate3) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (C : G2Comp Ω) {R S : Subgroup G2Model} (hR : R ∈ G2Fund)
    (h : QuotViol Ω (R.map C.ψ) (S.map C.ψ) z j a) (hJ : S.map C.ψ ∈ aStar Ω (R.map C.ψ))
    {R' : Subgroup G2Model} (hR' : R' ∈ G2Fund) (hR'Ω : R'.map C.ψ ∈ Ω) :
    R'.map C.ψ ∈ aStar Ω (R.map C.ψ) :=
  mem_of_invariant_g2_three hgen hΩ C hR h
    (fun _ hM _ hx => mem_conjStab_aStar hΩ.conjInvariant h.mem_left hM hx)
    (fun _ hM _ ht hne => hM.tail ⟨ht.1, Or.inr (Or.inr ⟨ht, hne⟩)⟩)
    Relation.ReflTransGen.refl hJ hR' hR'Ω

theorem aStar_eq_members (hgen : G2NonToralGenerate3) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (C : G2Comp Ω) {R S : Subgroup G2Model} (hR : R ∈ G2Fund) (hRΩ : R.map C.ψ ∈ Ω)
    (h : QuotViol Ω (R.map C.ψ) (S.map C.ψ) z j a) (hJ : S.map C.ψ ∈ aStar Ω (R.map C.ψ)) :
    aStar Ω (R.map C.ψ) = C.members := by
  ext M
  constructor
  · exact C.aStar_subset_members hΩ ⟨hRΩ, R, hR, rfl⟩
  · rintro ⟨hMΩ, R', hR', rfl⟩
    exact mem_aStar_of_g2_three hgen hΩ C hR h hJ hR' hMΩ

end Star

end CFSG.ClassicalInvolution.Uniform
