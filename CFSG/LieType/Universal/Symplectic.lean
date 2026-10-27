module

public import CFSG.Foundations.Basic
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.ClassicalGroups.Symplectic.Model
import CFSG.ClassicalGroups.Symplectic.Perfect
import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.LieType.Universal.Symplectic

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic

variable (n : ℕ) (F : Type) [Field F]

theorem center_eq :
    Subgroup.center (StatedSp n F) =
      (StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F) := by
  rw [statedScalars_subgroupOf_statedSp]
  have h := statedSp_eq_GLSymplectic (n := n) (K := F)
  ext g
  simp only [Subgroup.mem_comap, Subgroup.mem_center_iff]
  constructor
  · rintro hg ⟨y, hy⟩
    have := congrArg Subtype.val (hg ⟨y, h.ge hy⟩)
    exact Subtype.ext this
  · intro hg y
    have := congrArg Subtype.val (hg (Subgroup.inclusion h.le y))
    exact Subtype.ext this

noncomputable def centerQuotientEquiv :
    StatedSp n F ⧸ Subgroup.center (StatedSp n F) ≃* StatedProj (StatedSp n F) :=
  QuotientGroup.quotientMulEquivOfEq (center_eq n F)

theorem isQuasisimple (hn : 1 ≤ n)
    (hF : (Infinite F ∨ 4 ≤ Nat.card F) ∨ (Nat.card F = 3 ∧ 2 ≤ n) ∨
      (Nat.card F = 2 ∧ 3 ≤ n)) :
    IsQuasisimple (StatedSp n F) := by
  have hperf : Group.IsPerfect (StatedSp n F) := by
    have : Group.IsPerfect (TauCeti.GLSymplecticFin n F) := isPerfect_GLSymplecticFin F n hF
    let e : TauCeti.GLSymplecticFin n F ≃* StatedSp n F :=
      (TauCeti.GLSymplecticFin.mulEquivGLSymplectic n F).trans
        (MulEquiv.subgroupCongr (statedSp_eq_GLSymplectic (n := n) (K := F)).symm)
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have : IsSimpleGroup (StatedProj (StatedSp n F)) := isSimpleGroup_statedProj_statedSp F n hn hF
  have hsimple : IsSimpleGroup (StatedSp n F ⧸ Subgroup.center (StatedSp n F)) :=
    (centerQuotientEquiv n F).isSimpleGroup
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hcomm
  simp only [not_exists, not_not] at hcomm
  have : IsMulCommutative (StatedSp n F ⧸ Subgroup.center (StatedSp n F)) := ⟨⟨hcomm⟩⟩
  exact Group.IsPerfect.not_isMulCommutative _ this

theorem isQuasisimple_of_admissible {p f : ℕ} (hadm : StatedLieAdmissible .PSp n p f)
    (hF : Nat.card F = p ^ f) : IsQuasisimple (StatedSp n F) := by
  obtain ⟨hp, hf, hn, hne⟩ := hadm
  have hq : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  refine isQuasisimple n F (by omega) ?_
  rw [hF]
  rcases Nat.lt_or_ge (p ^ f) 4 with h4 | h4
  · rcases (show p ^ f = 2 ∨ p ^ f = 3 by omega) with h2 | h3
    · have hn2 : n ≠ 2 := by
        rintro rfl
        exact hne (by rw [h2])
      exact Or.inr (Or.inr ⟨h2, by omega⟩)
    · exact Or.inr (Or.inl ⟨h3, hn⟩)
  · exact Or.inl (Or.inr h4)

theorem statedClassicalModel_center_quotient [Finite F] {p f : ℕ}
    (hadm : StatedLieAdmissible .PSp n p f) (hF : Nat.card F = p ^ f) :
    StatedClassicalModel (StatedSp n F ⧸ Subgroup.center (StatedSp n F)) .PSp n p f :=
  ⟨hadm, F, inferInstance, inferInstance, hF, ⟨centerQuotientEquiv n F⟩⟩

end CFSG.LieType.Universal.Symplectic
