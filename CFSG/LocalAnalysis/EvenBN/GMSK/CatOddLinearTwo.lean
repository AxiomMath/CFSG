module

public import CFSG.LocalAnalysis.EvenBN.GMSK.Selector
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoInvolutionStructure
import CFSG.LocalAnalysis.SteinbergBTOddClassicalScalarQuotientSL2
import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem odd_linear_two_involution_fixed_normal_even_SL2_square_five {D : Type} [Group D]
    {p f : ℕ} (hD : StatedClassicalModel D .PSL 2 p f) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n)
    (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n) (α : MulAut D)
    (hα : orderOf α = 2) (S : Subgroup D) (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    p = 5 ∧ f = 2 ∧ n = 2 ∧ α ∉ (MulAut.conj : D →* MulAut D).range ∧
      ∃ (F₀ : Type) (_ : Field F₀) (_ : Fintype F₀), Fintype.card F₀ = 5 ∧
        Nonempty (α.toMonoidHom.eqLocus (MonoidHom.id D) ≃* Matrix.ProjGenLinGroup (Fin 2) F₀) := by
  obtain ⟨⟨hp, hf, -⟩, F, _, _, hF, ⟨e⟩⟩ := hD
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨φ⟩ := hSK
  have hKn : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  let ψ : D ≃* coordinateG F :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans (pslEquivCoordinateG F))
  set β : MulAut (coordinateG F) := MulAut.congr ψ α with hβ
  set a : coordinateE F := (coordinateConjugationEquiv F).symm β with ha_def
  have ha : coordinateConjugation F a = β := (coordinateConjugationEquiv F).apply_symm_apply β
  have haord : orderOf (a : Equiv.Perm (Omega F)) = 2 := by
    rw [Subgroup.orderOf_coe, ha_def, MulEquiv.orderOf_eq, hβ, MulEquiv.orderOf_eq, hα]
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id D)).map ψ.toMonoidHom =
      CatalogueBLinearTwoInvolution.fixedGroup F (a : Equiv.Perm (Omega F)) := by
    ext y
    change (∃ x, α x = x ∧ ψ x = y) ↔
      (y : Equiv.Perm (Omega F)) ∈ Subgroup.centralizer {(a : Equiv.Perm (Omega F))}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy : β y = y ↔ (y : Equiv.Perm (Omega F)) * a = a * y := by
      rw [← ha]
      constructor
      · intro h
        have h' := congrArg Subtype.val h
        rw [coordinateConjugation_apply_coe] at h'
        calc (y : Equiv.Perm (Omega F)) * a = a * y * (a : Equiv.Perm (Omega F))⁻¹ * a := by
              rw [h']
          _ = a * y := by group
      · intro h
        apply Subtype.ext
        rw [coordinateConjugation_apply_coe, ← h]
        group
    rw [← hy]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ψ (α (ψ.symm (ψ x))) = ψ x
      rw [MulEquiv.symm_apply_apply, hx]
    · intro h
      refine ⟨ψ.symm y, ?_, ψ.apply_symm_apply y⟩
      have h' : ψ (α (ψ.symm y)) = y := h
      rw [← ψ.symm_apply_apply (α (ψ.symm y)), h']
  let Φ : α.toMonoidHom.eqLocus (MonoidHom.id D) ≃*
      CatalogueBLinearTwoInvolution.fixedGroup F (a : Equiv.Perm (Omega F)) :=
    ((α.toMonoidHom.eqLocus (MonoidHom.id D)).equivMapOfInjective ψ.toMonoidHom
      ψ.injective).trans (MulEquiv.subgroupCongr hmap)
  set S₁ := (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).map Φ.toMonoidHom
  have hS₁n : S₁.Normal := hSn.map _ Φ.surjective
  let eS₁ : S₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    ((S.subgroupOf _).equivMapOfInjective Φ.toMonoidHom Φ.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hSα).trans φ)
  have h4 : ∃ s : Finset K, s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) K) := by
    obtain ⟨x, y, hxy⟩ := sl2_exists_mul_ne (K := K)
    refine nontrivial_of_ne x 1 fun hx => hxy ?_
    rw [hx, one_mul, mul_one]
  have : Group.IsPerfect S₁ := Group.IsPerfect.ofSurjective (f := eS₁.symm.toMonoidHom)
    eS₁.symm.surjective
  have : Nontrivial S₁ := eS₁.toEquiv.nontrivial
  have haD : (a : Equiv.Perm (Omega F)) ∉ coordinateD F := by
    intro haD
    have := CatalogueBLinearTwoInvolution.linear_involution_fixedGroup_solvable F p f hp hodd hF
      _ haD haord
    exact Group.IsPerfect.not_isSolvable S₁ inferInstance
  obtain ⟨σ, -, heven, -, hcard0, ⟨E⟩⟩ :=
    CatalogueBLinearTwoInvolution.nonlinear_involution_fixedGroup_structure F p f hp hodd hf hF a
      haord haD
  set F₀ := CatalogueBLinearTwoFixed.fixedField F σ
  have hoddF₀ : Odd (Nat.card F₀) := by rw [hcard0]; exact hodd.pow
  set S₀ := S₁.map E.symm.toMonoidHom
  let eS₀ : S₀ ≃* S₁ := (S₁.equivMapOfInjective E.symm.toMonoidHom E.symm.injective).symm
  have : Group.IsPerfect S₀ := Group.IsPerfect.ofSurjective (f := eS₀.symm.toMonoidHom)
    eS₀.symm.surjective
  have : Nontrivial S₀ := eS₀.toEquiv.nontrivial
  have hS₀sub : S₀.IsSubnormal := (hS₁n.map _ E.symm.surjective).isSubnormal
  obtain ⟨-, hS₀eq, -⟩ :=
    CatalogueBLinearTwo.coordinateD_perfect_subnormal_classification F₀ hoddF₀ S₀ hS₀sub
  let φ₀ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀ ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (pslEquivCoordinateG F₀).trans ((Subgroup.subgroupOfEquivOfLe (coordinateG_le_D F₀)).symm.trans
      ((MulEquiv.subgroupCongr hS₀eq.symm).trans (eS₀.trans eS₁)))
  obtain ⟨hn2, h5, -⟩ := CFSG.LocalAnalysis.SteinbergBT.linear_scalar_quotient_SL2 hoddF₀ hn K
    hKn le_rfl (Subgroup.center _)
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 F₀).ge φ₀
  rw [hcard0] at h5
  obtain ⟨rfl, hf2⟩ := Nat.prime_five.pow_eq_iff.1 h5
  have hcard5 : Nat.card F₀ = 5 := by rw [hcard0, hf2, pow_one]
  let : Fintype F₀ := Fintype.ofFinite F₀
  refine ⟨rfl, by obtain ⟨k, hk⟩ := heven; omega, hn2, ?_, F₀, inferInstance, inferInstance,
    by rw [← Nat.card_eq_fintype_card, hcard5],
    ⟨Φ.trans (E.symm.trans (pglEquivCoordinateD F₀).symm)⟩⟩
  rintro ⟨d, hd⟩
  apply haD
  have hconj : β = MulAut.conj (ψ d) := by
    rw [hβ, ← hd]
    refine MulEquiv.ext fun x => ?_
    change ψ (d * ψ.symm x * d⁻¹) = ψ d * x * (ψ d)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hag : a = ⟨ψ d, (coordinateG_le_D F).trans (coordinateD_le_E F) (ψ d).property⟩ :=
    coordinateConjugation_injective F (ha.trans (hconj.trans (coordinateConjugation_on_G F _).symm))
  rw [hag]
  exact coordinateG_le_D F (ψ d).property

theorem fixedRootSelector_oddLinearTwo :
    FixedRootSelector fun D _ => ∃ p f : ℕ, p ≠ 2 ∧ LieModel D .PSL 2 p f := by
  rintro D _ _ - ⟨p, f, hp2, hD⟩ n hn K _ _ hK α hα S hSα hSn hSK -
  have hC : StatedClassicalModel D .PSL 2 p f := by
    rcases hD with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by decide)
  obtain ⟨rfl, rfl, rfl, -⟩ :=
    odd_linear_two_involution_fixed_normal_even_SL2_square_five hC hp2 hn K hK α hα S hSα hSn hSK
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl hD)))⟩)))

end CFSG.LocalAnalysis.EvenBN.GMSK
