module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.YComponentsB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.Data

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.Open CFSG.ComponentClassification

private theorem map_conj_mul {Y : Type*} [Group Y] (g h : Y) (K : Subgroup Y) :
    (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem map_conj_one {Y : Type*} [Group Y] (K : Subgroup Y) :
    K.map (MulAut.conj (1 : Y)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map]

private noncomputable def compPerm {Y : Type*} [Group Y] :
    Y →* Equiv.Perm {K : Subgroup Y // IsComponentOf K ⊤} where
  toFun g :=
    { toFun := fun K => ⟨K.1.map (MulAut.conj g).toMonoidHom, isComponentOf_map_conj K.2 g⟩
      invFun := fun K => ⟨K.1.map (MulAut.conj g⁻¹).toMonoidHom,
        isComponentOf_map_conj K.2 g⁻¹⟩
      left_inv := fun K => Subtype.ext (by
        change (K.1.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = K.1
        rw [map_conj_mul, inv_mul_cancel, map_conj_one])
      right_inv := fun K => Subtype.ext (by
        change (K.1.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K.1
        rw [map_conj_mul, mul_inv_cancel, map_conj_one]) }
  map_one' := Equiv.ext fun K => Subtype.ext (map_conj_one K.1)
  map_mul' := fun g h => Equiv.ext fun K => Subtype.ext (map_conj_mul g h K.1).symm

theorem perfect_normalizes_component {Y : Type*} [Group Y] [Finite Y]
    (hle : ∀ A B C : Subgroup Y, IsComponentOf A ⊤ → IsComponentOf B ⊤ → IsComponentOf C ⊤ →
      A = B ∨ A = C ∨ B = C)
    {F : Subgroup Y} (hF : ⁅F, F⁆ = F) {C : Subgroup Y} (hC : IsComponentOf C ⊤) :
    F ≤ Subgroup.normalizer (C : Set Y) := by
  classical
  let S := {K : Subgroup Y // IsComponentOf K ⊤}
  have hcard : Nat.card S ≤ 2 := by
    rw [← not_lt, ← Set.ncard_univ, Set.two_lt_ncard_iff]
    rintro ⟨a, b, c, _, _, _, hab, hac, hbc⟩
    rcases hle a.1 b.1 c.1 a.2 b.2 c.2 with h | h | h
    · exact hab (Subtype.ext h)
    · exact hac (Subtype.ext h)
    · exact hbc (Subtype.ext h)
  haveI : IsMulCommutative (Equiv.Perm S) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr hcard
  haveI : Group.IsPerfect F := Subgroup.isPerfect_iff.mpr hF
  have h1 : (compPerm (Y := Y)).comp F.subtype = 1 := by
    apply MonoidHom.ext
    intro x
    have hx : x ∈ ((compPerm (Y := Y)).comp F.subtype).ker := by
      have htop : (⊤ : Subgroup F) ≤ ((compPerm (Y := Y)).comp F.subtype).ker := by
        rw [← Group.IsPerfect.commutator_eq_top (G := F)]
        exact Abelianization.commutator_subset_ker _
      exact htop (Subgroup.mem_top x)
    simpa using hx
  intro f hf
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h2 : (compPerm (Y := Y)) f = 1 := by
    have := congrArg (fun g : F →* Equiv.Perm S => g ⟨f, hf⟩) h1
    simpa using this
  have h3 : ((compPerm (Y := Y)) f ⟨C, hC⟩) = ⟨C, hC⟩ := by
    rw [h2]
    rfl
  have h4 : ((compPerm (Y := Y)) f ⟨C, hC⟩).1 = C := congrArg Subtype.val h3
  exact h4

theorem perfect_le_layer {Y : Type} [Group Y] [Finite Y] (hfree : SolvableRadical.Free Y)
    (hsec : SmallSections Y)
    (hle : ∀ A B C : Subgroup Y, IsComponentOf A ⊤ → IsComponentOf B ⊤ → IsComponentOf C ⊤ →
      A = B ∨ A = C ∨ B = C)
    {F : Subgroup Y} (hF : ⁅F, F⁆ = F) : F ≤ Layer.subgroup Y := by
  haveI : Group.IsPerfect F := Subgroup.isPerfect_iff.mpr hF
  refine RadicalFreeLayer.perfect_normalizer_enters_layer hfree F ?_ ?_
  · intro component hcomponent
    exact perfect_normalizes_component hle hF hcomponent
  · intro component hcomponent
    exact (hsec component (Subgroup.center component) hcomponent.2.2.2
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian component
        hcomponent.2.2)).2

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
