module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviSL2

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise commutatorElement

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A} {a₀ : A}

private theorem isSolvable_sl2_card_two_H11 [Finite K] (hK : Nat.card K = 2) :
    Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := by
  haveI : Group.IsSolvable (GL (Fin 2) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
      (Or.inl hK)
  exact Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective

private theorem isSolvable_sl2Embed_range_H11 [Finite K] (hK : Nat.card K = 2) {i : Fin r} :
    Group.IsSolvable ↥(tailLeviSL2Embed K A r i).range := by
  let e : SpecialLinearGroup (Fin 2) K ≃* ↥(tailLeviSL2Embed K A r i).range :=
    MonoidHom.ofInjective (tailLeviSL2Embed_injective i)
  haveI : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := isSolvable_sl2_card_two_H11 hK
  exact Group.isSolvable_of_isSolvable_injective
    (f := e.symm.toMonoidHom) e.symm.injective

private theorem isSolvable_range_tailRankOneLeviHom_H11 [Finite K] [FiniteDimensional K A]
    {i : Fin r} (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0)
    (hcomm : ∀ b₁ ∈ tailBorel r qA, ∀ b₂ ∈ tailBorel r qA, ⁅b₁, b₂⁆ ∈ tailUnipotent r qA)
    (hK : Nat.card K = 2) :
    Group.IsSolvable ↥(tailRankOneLeviHom hi hani ha₀).range := by
  set R : Subgroup (TailLeviTarget K A r i) := (tailRankOneLeviHom hi hani ha₀).range
  set S : Subgroup (TailLeviTarget K A r i) := (tailLeviSL2Embed K A r i).range
  haveI : Group.IsSolvable ↥S :=
    isSolvable_sl2Embed_range_H11 (A := A) (r := r) (i := i) hK
  have hle : ⁅R, R⁆ ≤ S := commutator_range_tailRankOneLeviHom_le hi hani ha₀ hcomm
  have hmap : (commutator ↥R).map R.subtype = ⁅R, R⁆ := Subgroup.map_subtype_commutator R
  have hcomp : (R.subtype.comp (commutator ↥R).subtype).range ≤ S := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
    exact hle
  have hinj : Function.Injective (R.subtype.comp (commutator ↥R).subtype) :=
    R.subtype_injective.comp (commutator ↥R).subtype_injective
  have hcommSolv : Group.IsSolvable ↥(commutator ↥R) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (R.subtype.comp (commutator ↥R).subtype).codRestrict S fun x => hcomp ⟨x, rfl⟩)
      (fun a b hab =>
        hinj (congrArg (fun x : ↥S => (x : TailLeviTarget K A r i)) hab))
  exact (Group.isSolvable_commutator_iff (G := ↥R)).mp hcommSolv

private theorem isSolvable_ker_tailRankOneLeviHom_H11 [Finite K] [FiniteDimensional K A]
    [CharP K 2] {i : Fin r} (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0) :
    Group.IsSolvable ↥(tailRankOneLeviHom hi hani ha₀).ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥(tailRankOneLeviHom hi hani ha₀).ker :=
    IsPGroup.isNilpotent (isPGroup_ker_tailRankOneLeviHom hi hani ha₀)
  exact inferInstance

theorem isSolvable_tailRankOneParabolic [Finite K] [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0)
    (hcomm : ∀ b₁ ∈ tailBorel r qA, ∀ b₂ ∈ tailBorel r qA, ⁅b₁, b₂⁆ ∈ tailUnipotent r qA)
    (hK : Nat.card K = 2) : Group.IsSolvable ↥(tailRankOneParabolic qA a₀ i) := by
  have hchar : ringChar K = 2 :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq (p := 2) (f := 1) Nat.prime_two
      (by norm_num) (by rw [hK]; norm_num)
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  haveI hker : Group.IsSolvable ↥(tailRankOneLeviHom hi hani ha₀).ker :=
    isSolvable_ker_tailRankOneLeviHom_H11 hi hani ha₀
  haveI hrange : Group.IsSolvable ↥(tailRankOneLeviHom hi hani ha₀).range :=
    isSolvable_range_tailRankOneLeviHom_H11 hi hani ha₀ hcomm hK
  exact Group.isSolvable_of_ker_le_range
    (f := (tailRankOneLeviHom hi hani ha₀).ker.subtype)
    (g := (tailRankOneLeviHom hi hani ha₀).rangeRestrict)
    (by simp [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

theorem hinf_tailRankOneParabolic_eq_bot [Finite K] [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0)
    (hcomm : ∀ b₁ ∈ tailBorel r qA, ∀ b₂ ∈ tailBorel r qA, ⁅b₁, b₂⁆ ∈ tailUnipotent r qA)
    (hK : Nat.card K = 2) : Hinf (tailRankOneParabolic qA a₀ i) = ⊥ := by
  haveI : Finite A := Module.finite_of_finite K
  exact hinf_rankOneParabolic_tail_eq_bot_of_solvable i
    (isSolvable_tailRankOneParabolic hi hani ha₀ hcomm hK)

theorem isL2_or_hinf_eq_bot_tailRankOneParabolic [Finite K] [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0)
    (hcomm : ∀ b₁ ∈ tailBorel r qA, ∀ b₂ ∈ tailBorel r qA, ⁅b₁, b₂⁆ ∈ tailUnipotent r qA)
    {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    IsL2 (Bar2 (Hinf (tailRankOneParabolic qA a₀ i))) n ∨
      (n = 1 ∧ Hinf (tailRankOneParabolic qA a₀ i) = ⊥) := by
  have hn0 : n ≠ 0 := by
    intro hn
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, hn, pow_zero] at h1
    exact lt_irrefl 1 h1
  rcases lt_or_eq_of_le (Nat.one_le_iff_ne_zero.mpr hn0) with hn2 | hn1
  · left
    exact isL2_tailRankOneParabolic hi hani ha₀ hcomm (by omega) hK
  · right
    refine ⟨hn1.symm, ?_⟩
    exact hinf_tailRankOneParabolic_eq_bot hi hani ha₀ hcomm (by rw [hK, ← hn1]; norm_num)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
