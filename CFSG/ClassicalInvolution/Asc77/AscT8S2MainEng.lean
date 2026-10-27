module

public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.WP2Thm8
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K R : Subgroup G}

theorem exists_sylow_meeting_XE (hRK : R ≤ K) (hRsyl : IsSylow2In R K)
    (hconjX : ∀ {K₀ : Subgroup G} {b : G}, conjSub b K₀ = K₀ →
      conjSub b (omegaNbrGen Ω K₀) = omegaNbrGen Ω K₀) :
    ∃ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) ∧
      IsSylow2In ((S₂ : Subgroup G) ⊓ omegaNbrGen Ω K) (omegaNbrGen Ω K) := by
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hRN : ∀ r ∈ R, conjSub r X = X := fun r hr =>
    hconjX (conjSub_eq_self_of_mem (hRK hr))
  have hYN : X ⊔ R ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer
      (fun r hr => mem_normalizer_iff_conjSub_eq.mpr (hRN r hr))
  obtain ⟨V, hV, hRV⟩ := IsSylow2In.exists_ge hRsyl.2.1 (le_sup_right : R ≤ X ⊔ R)
  have hVX : IsSylow2In (V ⊓ X) X :=
    AscP1Nine3.isSylow2In_inf_of_le_normalizer' hV le_sup_left hYN
  obtain ⟨S₂, hS₂⟩ := hV.2.1.exists_le_sylow
  have heq : (S₂ : Subgroup G) ⊓ X = V ⊓ X :=
    hVX.2.2 _ inf_le_right S₂.isPGroup'.to_inf_left (inf_le_inf_right X hS₂)
  exact ⟨S₂, hRV.trans hS₂, heq ▸ hVX⟩

end CFSG.ClassicalInvolution.Asc77
