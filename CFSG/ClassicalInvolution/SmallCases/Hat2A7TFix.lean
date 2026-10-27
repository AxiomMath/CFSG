module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TStab

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section Fix

variable {F : Type} [Group F] [Finite F]

variable (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F)

include hZ IH in
theorem exists_member_normalized {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hodd : Odd (Nat.card (cliqueSet K))) {P : Subgroup F}
    (hPH : P ≤ Subgroup.normalizer (cliqueGrp K : Set F)) (hP2 : IsPGroup 2 P) :
    ∃ N ∈ cliqueSet K, P ≤ Subgroup.normalizer (N : Set F) := by
  set H : Subgroup F := Subgroup.normalizer (cliqueGrp K : Set F) with hH
  let _inst : MulAction ↥H ↥(cliqueSet K) :=
    { smul := fun g N => ⟨N.1.map (MulAut.conj (g : F)).toMonoidHom,
        conj_mem_cliqueSet hZ IH hK g.2 N.2⟩
      one_smul := fun N => Subtype.ext (by
        show N.1.map (MulAut.conj ((1 : ↥H) : F)).toMonoidHom = N.1
        exact map_conj_one' N.1)
      mul_smul := fun g h N => Subtype.ext (by
        show N.1.map (MulAut.conj (((g * h : ↥H)) : F)).toMonoidHom =
          (N.1.map (MulAut.conj (h : F)).toMonoidHom).map (MulAut.conj (g : F)).toMonoidHom
        rw [map_map_conj]
        rfl) }
  let P' : Subgroup ↥H := P.subgroupOf H
  have hP'2 : IsPGroup 2 ↥P' := hP2.comap_subtype
  have hmod := hP'2.card_modEq_card_fixedPoints ↥(cliqueSet K)
  have hne : Nat.card (MulAction.fixedPoints ↥P' ↥(cliqueSet K)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    have h2 : 2 ∣ Nat.card (cliqueSet K) := Nat.modEq_zero_iff_dvd.mp hmod
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  obtain ⟨⟨N, hN⟩⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne)).1
  refine ⟨N.1, N.2, fun p hp => ?_⟩
  have h1 := MulAction.mem_fixedPoints.mp hN ⟨⟨p, hPH hp⟩, hp⟩
  have h2 : N.1.map (MulAut.conj p).toMonoidHom = N.1 := congrArg Subtype.val h1
  exact map_conj_eq_iff_mem_normalizer.mp h2

end Fix

end CFSG.ClassicalInvolution.Hat2A7T
