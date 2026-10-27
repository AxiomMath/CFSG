module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.CoverLift
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section
namespace CFSG.GroupTheory
open Subgroup

theorem hom_eq_one_of_perfect_simple_solvable_kernel
    {L S H : Type} [Group L] [Finite L] [Group S] [Finite S] [IsSimpleGroup S]
    [Group H] [Finite H] (hL : Group.IsPerfect L) (π : L →* S)
    (hπ : Function.Surjective π) (hsol : Group.IsSolvable π.ker)
    {n : ℕ} (hn : n ∣ Nat.card S) (φ : L →* H)
    (hnot : ¬ n ∣ Nat.card φ.range) : φ = 1 := by
  rcases CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.ker_le_or_eq_one
    hL π hπ hsol φ with hk | ht
  · let ψ : (L ⧸ φ.ker) →* S := QuotientGroup.lift φ.ker π hk
    have hψ : Function.Surjective ψ := by
      intro s
      obtain ⟨l, rfl⟩ := hπ s
      exact ⟨QuotientGroup.mk' φ.ker l, rfl⟩
    have hcard : n ∣ Nat.card φ.range := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
      exact hn.trans (Subgroup.card_dvd_of_surjective hψ)
    exact False.elim (hnot hcard)
  · exact ht

theorem isSolvable_ker_center_quotient_comp
    {L S : Type} [Group L] [Group S] (π : L →* S)
    (hsol : Group.IsSolvable π.ker) :
    Group.IsSolvable ((QuotientGroup.mk' (center S)).comp π).ker := by
  let τ := (QuotientGroup.mk' (center S)).comp π
  have hker : π.ker ≤ τ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    change QuotientGroup.mk' (center S) (π x) = 1
    rw [hx, map_one]
  let f : π.ker →* τ.ker := Subgroup.inclusion hker
  let g : τ.ker →* center S :=
    { toFun := fun x => ⟨π x, (QuotientGroup.eq_one_iff (π x)).mp x.2⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun x y => Subtype.ext (map_mul π (x : L) (y : L)) }
  have hfg : g.ker ≤ f.range := by
    intro x hx
    have hxπ : π x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact ⟨⟨x, hxπ⟩, rfl⟩
  have : Group.IsSolvable π.ker := hsol
  exact Group.isSolvable_of_ker_le_range f g hfg

theorem perm_eq_one_of_perfect_simple_solvable_kernel
    {L S Ω : Type} [Group L] [Finite L] [Group S] [Finite S] [IsSimpleGroup S] [Finite Ω]
    (hL : Group.IsPerfect L) (π : L →* S) (hπ : Function.Surjective π)
    (hsol : Group.IsSolvable π.ker) {p : ℕ} (hp : p.Prime)
    (hpS : p ∣ Nat.card S) (hΩ : Nat.card Ω < p) (φ : L →* Equiv.Perm Ω) : φ = 1 := by
  apply hom_eq_one_of_perfect_simple_solvable_kernel hL π hπ hsol hpS φ
  intro hpφ
  have hpd : p ∣ (Nat.card Ω).factorial := by
    rw [← Nat.card_perm]
    exact hpφ.trans (Subgroup.card_subgroup_dvd_card φ.range)
  exact (not_le.mpr hΩ) ((hp.dvd_factorial).mp hpd)

theorem mulAut_eq_one_of_perfect_simple_solvable_kernel
    {L S H : Type} [Group L] [Finite L] [Group S] [Finite S] [IsSimpleGroup S]
    [Group H] [Finite H] (hL : Group.IsPerfect L) (π : L →* S)
    (hπ : Function.Surjective π) (hsol : Group.IsSolvable π.ker)
    (hS3 : 3 ∣ Nat.card S) (hH3 : ¬ 3 ∣ Nat.card H)
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer H))
    (φ : L →* MulAut H) : φ = 1 := by
  have : Group.IsPerfect L := hL
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer H) := hOut
  have hinner : φ.range ≤ (MulAut.conj : H →* MulAut H).range := by
    rintro α ⟨l, rfl⟩
    obtain ⟨h, he⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner φ l
    exact ⟨h, he.symm⟩
  have hnot : ¬ 3 ∣ Nat.card φ.range := by
    intro h
    have hd := h.trans (Subgroup.card_dvd_of_le hinner)
    exact hH3 (hd.trans (Subgroup.card_range_dvd (MulAut.conj : H →* MulAut H)))
  exact hom_eq_one_of_perfect_simple_solvable_kernel hL π hπ hsol hS3 φ hnot

theorem mulAut_eq_one_of_perfect_quasisimple_solvable_kernel
    {L S H : Type} [Group L] [Finite L] [Group S] [Finite S] [Group H] [Finite H]
    (hL : Group.IsPerfect L) (hS : CFSG.IsQuasisimple S)
    (π : L →* S) (hπ : Function.Surjective π) (hsol : Group.IsSolvable π.ker)
    (hS3 : 3 ∣ Nat.card (S ⧸ center S)) (hH3 : ¬ 3 ∣ Nat.card H)
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer H))
    (φ : L →* MulAut H) : φ = 1 := by
  have : IsSimpleGroup (S ⧸ center S) := hS.2.1
  exact mulAut_eq_one_of_perfect_simple_solvable_kernel hL
    ((QuotientGroup.mk' (center S)).comp π)
    ((QuotientGroup.mk'_surjective (center S)).comp hπ)
    (isSolvable_ker_center_quotient_comp π hsol) hS3 hH3 hOut φ

end CFSG.GroupTheory
