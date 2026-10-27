module

public import CFSG.CGT.PushingUpLit.CGT6K1.InnerBase
public import CFSG.LocalAnalysis.SteinbergBMOddG2InnerFixedNoSimple
import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank

theorem chevalleyG2Model_of_lieModel {D : Type} [Group D] {m p f : ℕ}
    (h : LieModel D .G2 m p f) : m = 0 ∧ ChevalleyExceptionalModel D .G2 p f :=
  (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 h

theorem congr_ne_one_and_sq_eq_one_of_orderOf {G H : Type*} [Group G] [Group H] (ψ : G ≃* H)
    {α : MulAut G} (hα : orderOf α = 2) :
    MulAut.congr ψ α ≠ 1 ∧ MulAut.congr ψ α ^ 2 = 1 := by
  rw [← MulEquiv.orderOf_eq (MulAut.congr ψ) α] at hα
  exact ⟨fun h => by rw [h, orderOf_one] at hα; omega, hα ▸ pow_orderOf_eq_one _⟩

theorem exists_normal_simple_fixed_congr {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (α : MulAut A) (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id A))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) :
    ∃ S' : Subgroup ((MulAut.congr φ α).toMonoidHom.eqLocus (MonoidHom.id B)), S'.Normal ∧
      IsSimpleGroup S' ∧ ∃ a b : S', a * b ≠ b * a := by
  have hmap := CFSG.LocalAnalysis.SteinbergBM.map_eqLocus_mulAut_congr φ α
  obtain ⟨S', hS'n, hS's, hS'nab, -⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.exists_normal_simple_of_mulEquiv
      (((α.toMonoidHom.eqLocus _).equivMapOfInjective _ φ.injective).trans
        (MulEquiv.subgroupCongr hmap)) S hSn hSs hSnab
  exact ⟨S', hS'n, hS's, hS'nab⟩

theorem inner_G2_fixed_root_exclusion
    {D : Type} [Group D] {m p f : ℕ} (hD : LieModel D .G2 m p f) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 2 ≤ n) (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n) (α : MulAut D)
    (hα : orderOf α = 2) (hin : α ∈ (MulAut.conj : D →* MulAut D).range) (S : Subgroup D)
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) : False := by
  obtain ⟨-, ⟨hp, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := chevalleyG2Model_of_lieModel hD
  let ψ : D ≃* adjointGroup .G2 F :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)
  obtain ⟨x, rfl⟩ := hin
  obtain ⟨hβ1, hβ2⟩ := congr_ne_one_and_sq_eq_one_of_orderOf ψ hα
  obtain ⟨hSs, hSnab, -⟩ := fixedRoot_simple hn hK hSα hSK
  obtain ⟨S', hS'n, hS's, hS'nab⟩ := exists_normal_simple_fixed_congr ψ _ _ hSn hSs hSnab
  refine CFSG.LocalAnalysis.SteinbergBM.not_normal_simple_of_inner_diagonal (g := ψ x) (a := 1)
    (by rw [hF]; exact (hp.odd_of_ne_two hp2).pow) (fun h => ?_) hβ2 hβ1 S' hS'n hS's hS'nab
  rw [CFSG.LieType.Chevalley.rootDiagUnit_one]
  simp only [inv_one, mul_one]
  change ((ψ (x * ψ.symm h * x⁻¹) : adjointGroup .G2 F) : ModGL .G2 F) = _
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  simp

end CFSG.CGT.PushingUpLit.CGT6K1
