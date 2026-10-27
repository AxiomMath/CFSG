module

public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.LieType.Universal.Unitary

open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.LieType.CurtisTits

variable {F : Type} [Field F] (n q : ℕ)

theorem statedScalars_subgroupOf_le_center :
    (StatedScalars (Fin n) F).subgroupOf (StatedSU n q F) ≤ Subgroup.center (StatedSU n q F) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hx' : (x : GL (Fin n) F) ∈ Subgroup.center (GL (Fin n) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx
  exact Subtype.ext (Subgroup.mem_center_iff.mp hx' (y : GL (Fin n) F))

variable {n q}

theorem isQuasisimple_statedSU (hperf : Group.IsPerfect (StatedSU n q F))
    (hsimple : IsSimpleGroup (StatedProj (StatedSU n q F))) :
    IsQuasisimple (StatedSU n q F) ∧
      Subgroup.center (StatedSU n q F) = (StatedScalars (Fin n) F).subgroupOf (StatedSU n q F) := by
  have hnc : ∃ a b : StatedProj (StatedSU n q F), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have : IsMulCommutative (StatedProj (StatedSU n q F)) := ⟨⟨h⟩⟩
    have : Group.IsPerfect (StatedProj (StatedSU n q F)) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact Group.IsPerfect.not_isMulCommutative _ ‹_›
  exact ⟨isQuasisimple_of_isSimpleGroup_quotient _ (statedScalars_subgroupOf_le_center n q) hperf
      hsimple hnc,
    center_eq_of_isSimpleGroup_quotient _ (statedScalars_subgroupOf_le_center n q) hsimple hnc⟩

theorem isQuasisimple_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : IsQuasisimple G) : IsQuasisimple H :=
  hG.of_mulEquiv e.symm

theorem map_center_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hy w]
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro z
    apply e.injective
    simp [map_mul, hx (e z)]

section Finite

variable [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

noncomputable def centerQuotientEquivStatedProj (hF : Nat.card F = (p ^ f) ^ 2)
    (hZ : Subgroup.center (StatedSU n (p ^ f) F) =
      (StatedScalars (Fin n) F).subgroupOf (StatedSU n (p ^ f) F)) :
    SU (unitaryInvolution F p f) n ⧸ Subgroup.center (SU (unitaryInvolution F p f) n) ≃*
      StatedProj (StatedSU n (p ^ f) F) :=
  (QuotientGroup.congr _ _ (equivStatedSU hF n) (map_center_mulEquiv _)).trans
    (QuotientGroup.quotientMulEquivOfEq hZ)

end Finite

end CFSG.LieType.Universal.Unitary
