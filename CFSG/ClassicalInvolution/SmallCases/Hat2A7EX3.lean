module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Induction

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open
open CFSG.ClassicalInvolution.Balance (oddCoreIn oddCoreIn_le_of_isSubnormal)
open scoped commutatorElement

section System

theorem map_mem_oddCore_of_system {Z : Type} [Group Z] [Finite Z]
    {Φ : Set (Subgroup (Z ⧸ classicalInvolutionOddCore Z))}
    (D : A7SystemData (Z ⧸ classicalInvolutionOddCore Z) Φ) (i : Fin D.card)
    {A : Type*} [Group A] [Finite A] (ψ : A →* Z)
    (hi : D.comp i = ((QuotientGroup.mk' (classicalInvolutionOddCore Z)).comp ψ).range)
    {x : A} (hx : x ∈ classicalInvolutionOddCore A) : ψ x ∈ classicalInvolutionOddCore Z := by
  have : (D.comp i).Normal := D.comp_normal i
  have hcf : classicalInvolutionOddCore (Z ⧸ classicalInvolutionOddCore Z) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Z
  have hO : ∀ y ∈ classicalInvolutionOddCore ↥(D.comp i), y = 1 := by
    intro y hy
    have h1 : (classicalInvolutionOddCore ↥(D.comp i)).map (D.comp i).subtype =
        D.comp i ⊓ classicalInvolutionOddCore (Z ⧸ classicalInvolutionOddCore Z) :=
      CFSG.ComponentClassification.OddCore.normal_intersection _ (D.comp i)
    have h2 : ((y : Z ⧸ classicalInvolutionOddCore Z)) ∈
        (classicalInvolutionOddCore ↥(D.comp i)).map (D.comp i).subtype := ⟨y, hy, rfl⟩
    rw [h1, hcf, inf_bot_eq, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hmem : ∀ a : A,
      ((QuotientGroup.mk' (classicalInvolutionOddCore Z)).comp ψ) a ∈ D.comp i := fun a => by
    rw [hi]
    exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
  let φ : A →* ↥(D.comp i) :=
    ((QuotientGroup.mk' (classicalInvolutionOddCore Z)).comp ψ).codRestrict (D.comp i) hmem
  have hφ : Function.Surjective φ := by
    intro q
    have hq : (q : Z ⧸ classicalInvolutionOddCore Z) ∈
        ((QuotientGroup.mk' (classicalInvolutionOddCore Z)).comp ψ).range := by
      rw [← hi]
      exact q.2
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hq
    exact ⟨a, Subtype.ext ha⟩
  have hmap : (classicalInvolutionOddCore A).map φ ≤ classicalInvolutionOddCore ↥(D.comp i) :=
    CFSG.ComponentClassification.OddCore.maximal ↥(D.comp i) _
      (Subgroup.Normal.map (classicalInvolutionOddCore_normal A) φ hφ)
      (Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card A)
        (Subgroup.card_map_dvd (classicalInvolutionOddCore A) φ))
  have h3 : φ x = 1 := hO _ (hmap (Subgroup.mem_map_of_mem φ hx))
  have h4 : ((ψ x : Z) : Z ⧸ classicalInvolutionOddCore Z) = 1 := congrArg Subtype.val h3
  exact (QuotientGroup.eq_one_iff _).mp h4

end System

end CFSG.ClassicalInvolution.Hat2A7
