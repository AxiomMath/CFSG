module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBDefs
public import CFSG.LieType.Multipliers.U43

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U43

private theorem zetaBPres_bijective {X : Type*} [Group X] {g : Fin 2 → X}
    (hP : IsPresentation g (wordSet rels)) :
    Function.Bijective (PresentedGroup.toGroup fun r hr => hP.lift_eq_one hr) := by
  set φ : PresentedGroup (wordSet rels) →* X :=
    PresentedGroup.toGroup fun r hr => hP.lift_eq_one hr with hφ
  have hφmk : ∀ f : FreeGroup (Fin 2), φ (PresentedGroup.mk _ f) = FreeGroup.lift g f := by
    intro f
    have hc : φ.comp (PresentedGroup.mk (wordSet rels)) = FreeGroup.lift g := by
      refine FreeGroup.ext_hom _ _ fun i => ?_
      rw [MonoidHom.comp_apply]
      change φ (PresentedGroup.of i) = FreeGroup.lift g (FreeGroup.of i)
      rw [hφ, PresentedGroup.toGroup.of, FreeGroup.lift_apply_of]
    rw [← MonoidHom.comp_apply, hc]
  constructor
  · intro x y hxy
    obtain ⟨f, rfl⟩ := PresentedGroup.mk_surjective (wordSet rels) x
    obtain ⟨f', rfl⟩ := PresentedGroup.mk_surjective (wordSet rels) y
    rw [hφmk, hφmk] at hxy
    have hker : f * f'⁻¹ ∈ (FreeGroup.lift g).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    rw [hP.ker_lift] at hker
    have h1 : PresentedGroup.mk (wordSet rels) (f * f'⁻¹) = 1 :=
      PresentedGroup.mk_eq_one_iff.mpr hker
    rwa [map_mul, map_inv, mul_inv_eq_one] at h1
  · intro x
    obtain ⟨f, rfl⟩ := hP.lift_surjective x
    exact ⟨PresentedGroup.mk _ f, hφmk f⟩

private theorem zetaBPres_mulEquiv :
    Nonempty (PresentedGroup (wordSet rels) ≃* X₀) :=
  ⟨MulEquiv.ofBijective
    (PresentedGroup.toGroup fun r hr => isPresentation_X₀.lift_eq_one hr)
    (zetaBPres_bijective isPresentation_X₀)⟩

private theorem zetaBPres_isSimpleGroup :
    IsSimpleGroup (PresentedGroup (wordSet rels)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup X₀ := by
    have h := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F9 3 1
      (by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num) 4 (by norm_num) (by norm_num)
    simpa using h
  obtain ⟨e⟩ := zetaBPres_mulEquiv
  exact e.isSimpleGroup

theorem zetaPresentation_holds : ZetaPresentation := by
  intro S _grp s hLie hrel hs0
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eS⟩ := nonempty_mulEquiv_X₀ hLie
  haveI : Finite S := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_congr eS.toEquiv, card_X₀]; norm_num)
  haveI : IsSimpleGroup (PresentedGroup (wordSet rels)) := zetaBPres_isSimpleGroup
  set φ : PresentedGroup (wordSet rels) →* S :=
    PresentedGroup.toGroup fun r hr => hrel r hr with hφ
  have hφ0 : φ (PresentedGroup.of (0 : Fin 2)) = s 0 := by
    rw [hφ]
    exact PresentedGroup.toGroup.of hrel
  have hker_ne_top : φ.ker ≠ ⊤ := by
    intro htop
    have hmem : PresentedGroup.of (0 : Fin 2) ∈ φ.ker := by
      rw [htop]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hφ0] at hmem
    exact hs0 hmem
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exact absurd h hker_ne_top
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  obtain ⟨eP⟩ := zetaBPres_mulEquiv
  have hcardS : Nat.card S = 3265920 := by
    rw [Nat.card_congr eS.toEquiv, card_X₀]
  have hcardP : Nat.card (PresentedGroup (wordSet rels)) = 3265920 := by
    rw [Nat.card_congr eP.toEquiv, card_X₀]
  have hcard : Nat.card S ≤ Nat.card (PresentedGroup (wordSet rels)) := by
    rw [hcardS, hcardP]
  have hb : Function.Bijective φ := hinj.bijective_of_nat_card_le hcard
  rw [hφ] at hb
  exact IsPresentation.of_bijective hrel hb

end CFSG.OddStandard.SmallF3.Omega
