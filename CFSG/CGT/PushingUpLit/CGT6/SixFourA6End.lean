module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourPrinted
public import CFSG.CGT.PushingUpLit.CGT6.SixFourA6Core

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open scoped commutatorElement

section End

variable {Q V : Type} [Group Q] [Finite Q] [Group V] [Finite V] {θ : Q →* MulAut V}
  {J Y₀ : Subgroup Q}

theorem A6Setting.not_le_center (S : A6Setting θ J Y₀) : ¬ Y₀ ≤ Subgroup.center Q := by
  intro hle
  obtain ⟨a, haJ, ha1⟩ := S.exists_ne_one
  have hex : ∃ g ∈ Y₀, g ∉ J := by
    by_contra hcon
    push Not at hcon
    have hle' : Y₀ ≤ J := hcon
    have := Subgroup.card_le_of_le hle'
    rw [S.Y60, S.Jcard] at this
    omega
  obtain ⟨g, hgY, hgJ⟩ := hex
  have hgc : g * a = a * g := (Subgroup.mem_center_iff.mp (hle hgY) a).symm
  exact hgJ (S.Ycent a haJ ha1 g hgY hgc)

theorem A6Setting.isQuasisimple (S : A6Setting θ J Y₀) : CFSG.IsQuasisimple Q := by
  obtain ⟨e⟩ := S.alt6
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 6))
  refine ⟨⟨S.perfect⟩, e.isSimpleGroup, ?_⟩
  by_contra hcon
  push Not at hcon
  apply S.not_le_center
  have hcomm : commutator Q ≤ Subgroup.center Q := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have h1 : (QuotientGroup.mk' (Subgroup.center Q)) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcon _ _)
    exact (QuotientGroup.eq_one_iff ⁅x, y⁆).mp h1
  intro g _
  have hg : g ∈ commutator Q := by
    rw [S.perfect]
    exact Subgroup.mem_top g
  exact hcomm hg

theorem A6Setting.false_of_isSubnormal (S : A6Setting θ J Y₀) (hsub : Y₀.IsSubnormal) : False := by
  rcases isSubnormal_le_center_or_eq_top_of_quasisimple S.isQuasisimple hsub with hle | htop
  · exact S.not_le_center hle
  · obtain ⟨e⟩ := S.alt6
    have hcard : Nat.card Q = 60 := by
      rw [← S.Y60, htop]
      exact Subgroup.card_top.symm
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q)
    have h2 : Nat.card (Q ⧸ Subgroup.center Q) = 360 := by
      rw [Nat.card_congr e.toEquiv, card_alt6]
    rw [hcard, h2] at h1
    have : 0 < Nat.card (Subgroup.center Q) := Nat.card_pos
    omega

end End

end CFSG.CGT.PushingUpLit.CGT6
