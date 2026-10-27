module

public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddLinearTwo
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBase
public import CFSG.CGT.PushingUpLit.K1R.Defs
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddLinear

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open OddClassicalRankOne

namespace OddLinearInner

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.SymplecticFourStandard
open CFSG.LocalAnalysis.SymplecticFourStandard.OddLinearRoot

variable {F : Type} [Field F] [Finite F] {d : ℕ}

theorem projective_inner_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 3 ≤ d) {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {β : MulAut (projectiveSL d F)} (hβ : orderOf β = 2)
    (hin : β ∈ (MulAut.conj : projectiveSL d F →* MulAut (projectiveSL d F)).range)
    {S : Subgroup (fixedSubgroup β)} (hSn : S.Normal) (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a) (φS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    False := by
  classical
  have hβ2 : β ^ 2 = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  have hβ1 : β ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hβ
    omega
  have : IsSimpleGroup (projectiveSL d F) := isSimpleGroup_projectiveSL hd
  have hnabP : ∃ x y : projectiveSL d F, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hSnab
    exact ⟨((x : fixedSubgroup β) : projectiveSL d F), ((y : fixedSubgroup β) : projectiveSL d F),
      fun h => hxy (Subtype.ext (Subtype.ext h))⟩
  have hZ : center (projectiveSL d F) = ⊥ := ComponentInitial.center_eq_bot_of_isSimpleGroup hnabP
  have hconj := OddClassSelector.conj_injective hZ
  set ι := (MulAut.conj : projectiveSL d F →* MulAut (projectiveSL d F)).comp
    (fixedSubgroup β).subtype
  have hιi : Function.Injective ι := hconj.comp (Subgroup.subtype_injective _)
  set X := S.map ι
  have hX : CFSG.Assembly.IsComponentOf X (inner (projectiveSL d F) ⊓ centralizer {β}) := by
    have h1 := SymmetricLocal.isComponentOf_map_of_injective _ hconj
      (isComponentOf_map_subtype S hSn hSs hSnab)
    rwa [Subgroup.map_map, OddClassSelector.map_conj_fixedSubgroup hconj β] at h1
  have eX : X ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (S.equivMapOfInjective ι hιi).symm.trans φS
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) hd
  obtain ⟨B, σ, ε, hε, hβB⟩ := hform β
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hβB
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hβB
      exact inner_false hℓ hℓ2 he hF hd hβB hβ1 hβ2 hX hn hK eX
    · exact field_false hℓ hℓ2 he hF hd hσ hβB hβ2 hX hn hK eX
  · rw [pow_one] at hβB
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hβB
      obtain ⟨y, hy⟩ := hin
      apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := F) hd
      obtain ⟨g, rfl⟩ := proj_surjective d F y
      have h2 : dualAut d F = (conjAut d F B)⁻¹ * conjAut d F (SpecialLinearGroup.toGL g) := by
        rw [conjAut_toGL, hy, hβB, inv_mul_cancel_left]
      rw [h2]
      exact mul_mem (inv_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup B)))
        (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _))
    · exact graph_field_false hℓ hℓ2 he hF hd hσ hβB hβ2 hX hn hK eX

end OddLinearInner

end CFSG.LocalAnalysis.EvenBN.GMSK

namespace CFSG.CGT.PushingUpLit.K1R

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.EvenBN.GMSK
open CFSG.LocalAnalysis.EvenBN.GMSK.OddClassicalRankOne
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem innerKernelSelector_oddLinearTwo :
    InnerKernelSelector fun D _ => ∃ p f : ℕ, p ≠ 2 ∧ LieModel D .PSL 2 p f := by
  refine InnerKernelSelector.of_false ?_
  intro D _ _ _ ⟨p, f, hp2, hD⟩ n hn K _ _ hK α hα hin S hSα hSn hSK _
  have hC : StatedClassicalModel D .PSL 2 p f := statedClassicalModel_of_lieModel (by decide) hD
  exact (odd_linear_two_involution_fixed_normal_even_SL2_square_five hC hp2 hn K hK α hα S hSα hSn
    hSK).2.2.2.1 hin

theorem innerKernelSelector_oddHigherLinear :
    InnerKernelSelector fun D _ => ∃ d p f : ℕ, p ≠ 2 ∧ 3 ≤ d ∧ LieModel D .PSL d p f := by
  refine InnerKernelSelector.of_false ?_
  intro D _ _ _ ⟨d, p, f, hp, hd, hM⟩ n hn K _ _ hK α hα hin S hSα hSn hSK _
  obtain ⟨⟨hprime, hf, -, -, -⟩, F₀, _, _, hF₀, ⟨θ₀⟩⟩ :=
    statedClassicalModel_of_lieModel (by decide) hM
  obtain ⟨hSs, hSnab, ⟨φS⟩, -⟩ := subgroupOf_fixedRoot_data hn hK hSα hSK
  set η₀ := θ₀.trans
    (CFSG.ComponentClassification.SymmetricLocal.statedProjEquivProjectiveSL d F₀)
  have : Finite F₀ :=
    Nat.finite_of_card_ne_zero (by rw [hF₀]; exact pow_ne_zero _ hprime.ne_zero)
  have hint : ∀ x, η₀ (α x) = MulAut.congr η₀ α (η₀ x) := fun x => by
    change η₀ (α x) = η₀ (α (η₀.symm (η₀ x)))
    rw [MulEquiv.symm_apply_apply]
  have hfix := CFSG.ComponentClassification.OddClassSelector.map_fixedSubgroup_of_comm η₀ α
    (MulAut.congr η₀ α) hint
  let eF : fixedSubgroup α ≃* fixedSubgroup (MulAut.congr η₀ α) :=
    ((fixedSubgroup α).equivMapOfInjective η₀.toMonoidHom η₀.injective).trans
      (MulEquiv.subgroupCongr hfix)
  set S' := (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).map eF.toMonoidHom
  let eS : S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)) ≃* S' :=
    (S.subgroupOf _).equivMapOfInjective eF.toMonoidHom eF.injective
  refine OddLinearInner.projective_inner_false hprime hp hf hF₀ hd hn
    (by rw [Nat.card_eq_fintype_card, hK]) (β := MulAut.congr η₀ α)
    (by rw [MulEquiv.orderOf_eq]; exact hα)
    ((CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic.congr_mem_inner_iff η₀ α).2 hin)
    (S := S') (hSn.map _ eF.surjective) eS.symm.isSimpleGroup ?_ (eS.symm.trans φS)
  obtain ⟨a, b, hab⟩ := hSnab
  exact ⟨eS a, eS b, fun h' => hab (eS.injective (by rw [map_mul, map_mul, h']))⟩

end CFSG.CGT.PushingUpLit.K1R
