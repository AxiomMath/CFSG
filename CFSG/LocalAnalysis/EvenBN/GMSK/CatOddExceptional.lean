module

public import CFSG.LocalAnalysis.EvenBN.GMSK.Selector
public import CFSG.LocalAnalysis.SteinbergBMOddG2FixedSL2Boundary
public import CFSG.LocalAnalysis.SteinbergCAOddResidualExceptionalNoSL2
public import CFSG.LocalAnalysis.SteinbergCATrialityFixedNoSL2
public import CFSG.LocalAnalysis.SteinbergSFReeTitsNoNormalSL2
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.SteinbergCA (exists_normal_even_SL2_of_mulEquiv)

namespace OddExceptional

theorem fixedRoot_subgroupOf {D : Type*} [Group D] {n : ℕ} (hn : 2 ≤ n) {K : Type*} [Field K]
    [Fintype K] (hK : Fintype.card K = 2 ^ n) {α : MulAut D} {S : Subgroup D}
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    IsSimpleGroup (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))) ∧
      (∃ a b : S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)), a * b ≠ b * a) ∧
      Nonempty (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨φ⟩ := hSK
  let e := (Subgroup.subgroupOfEquivOfLe hSα).trans φ
  have h4 : 4 ≤ Fintype.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := sl2_isSimpleGroup (two_eq_zero_of_card (by omega) hK) h4
  obtain ⟨a, b, hab⟩ := sl2_exists_mul_ne (K := K)
  exact ⟨e.isSimpleGroup, ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by
    rw [map_mul, map_mul, h]))⟩, ⟨e⟩⟩

theorem ne_one_and_sq_eq_one_of_orderOf_eq_two {G : Type*} [Monoid G] {α : G}
    (hα : orderOf α = 2) : α ≠ 1 ∧ α ^ 2 = 1 :=
  ⟨fun h => by rw [h, orderOf_one] at hα; omega, hα ▸ pow_orderOf_eq_one α⟩

theorem congr_ne_one_and_sq_eq_one {G H : Type*} [Group G] [Group H] (ψ : G ≃* H)
    {α : MulAut G} (hα : orderOf α = 2) :
    MulAut.congr ψ α ≠ 1 ∧ MulAut.congr ψ α ^ 2 = 1 := by
  rw [← MulEquiv.orderOf_eq (MulAut.congr ψ) α] at hα
  exact ne_one_and_sq_eq_one_of_orderOf_eq_two hα

theorem chevalleyExceptionalModel_of_lieModel {D : Type} [Group D] {t : StatedLieTag}
    {m p f : ℕ} (ht : t ∈ chevalleyExceptionalTags) (h : LieModel D t m p f) :
    m = 0 ∧ ChevalleyExceptionalModel D t p f :=
  (CFSG.Blueprint.LieModel.chevalleyExceptional_iff ht).1 h

theorem reeTitsModel_of_lieModel {D : Type} [Group D] {t : StatedLieTag} {m p f : ℕ}
    (ht : t ∈ reeTitsTags) (h : LieModel D t m p f) : m = 0 ∧ ReeTitsModel D t p f :=
  CFSG.Blueprint.LieModel.reeTitsModel h ht

end OddExceptional

open OddExceptional

theorem odd_G2_fixed_root_survivor
    {D : Type} [Group D] {m p f : ℕ} (hD : LieModel D .G2 m p f) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 2 ≤ n) (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n)
    (α : MulAut D) (hα : orderOf α = 2) (S : Subgroup D)
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    n = 3 ∧ LieModel D .G2 0 3 1 := by
  obtain ⟨rfl, ⟨hp, hf, -⟩, F, _, _, hF, ⟨e⟩⟩ :=
    chevalleyExceptionalModel_of_lieModel (by decide) hD
  let ψ : D ≃* adjointGroup .G2 F :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)
  obtain ⟨hβ1, hβ2⟩ := congr_ne_one_and_sq_eq_one ψ hα
  obtain ⟨hSs, hSnab, ⟨eS⟩⟩ := fixedRoot_subgroupOf hn hK hSα hSK
  obtain ⟨S', hS'n, hS's, hS'nab, hS'K⟩ :=
    exists_normal_even_SL2_of_mulEquiv ψ α _ hSn hSs hSnab eS
  have hKn : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨rfl, rfl, hK8, -⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.odd_G2_involution_fixed_normal_even_SL2_parameter_boundary
      hp hp2 hf F hF _ hβ1 hβ2 hn K hKn S' hS'n hS's hS'nab hS'K
  refine ⟨Nat.pow_right_injective le_rfl ?_, hD⟩
  change 2 ^ n = 2 ^ 3
  rw [← hKn, hK8]

theorem odd_residual_exceptional_fixed_root_exclusion
    {D : Type} [Group D] [Finite D] {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) {m p f : ℕ}
    (hD : LieModel D t m p f) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K]
    [Fintype K] (hK : Fintype.card K = 2 ^ n) (α : MulAut D) (hα : orderOf α = 2)
    (S : Subgroup D) (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) : False := by
  have htE : t ∈ chevalleyExceptionalTags := by
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨-, hCE⟩ := chevalleyExceptionalModel_of_lieModel htE hD
  obtain ⟨hα1, hα2⟩ := ne_one_and_sq_eq_one_of_orderOf_eq_two hα
  obtain ⟨hSs, hSnab, ⟨eS⟩⟩ := fixedRoot_subgroupOf hn hK hSα hSK
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
    (two_eq_zero_of_card (by omega) hK)
  exact (SteinbergCA.odd_residual_exceptional_involution_fixed_groups_have_no_normal_even_SL2
    hp2 ht hCE α hα1 hα2 hn K (by rw [Nat.card_eq_fintype_card, hK]) _ hSn hSs hSnab).false eS

theorem triality_fixed_root_exclusion
    {D : Type} [Group D] {m p f : ℕ} (hD : LieModel D .trialityD4 m p f) {n : ℕ} (hn : 2 ≤ n)
    (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n) (α : MulAut D)
    (hα : orderOf α = 2) (S : Subgroup D) (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) : False := by
  obtain ⟨-, ⟨hp, hf, -⟩, F, _, _, hF, σ₀, hσ₀, ⟨e⟩⟩ :=
    chevalleyExceptionalModel_of_lieModel (by decide) hD
  let σ : F ≃+* F := RingEquiv.ofBijective σ₀
    ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  have hσσ₀ : σ.toRingHom = σ₀ := RingHom.ext fun _ => rfl
  have hσ : ∀ c, σ c = c ^ (p ^ f) := hσ₀
  have hF3 : Nat.card F = (p ^ f) ^ 3 := hF
  rw [← hσσ₀] at e
  obtain ⟨hβ1, hβ2⟩ := congr_ne_one_and_sq_eq_one e hα
  obtain ⟨hSs, hSnab, ⟨eS⟩⟩ := fixedRoot_subgroupOf hn hK hSα hSK
  obtain ⟨S', hS'n, hS's, hS'nab, ⟨eS'⟩⟩ :=
    exists_normal_even_SL2_of_mulEquiv e α _ hSn hSs hSnab eS
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
    (two_eq_zero_of_card (by omega) hK)
  exact (SteinbergCA.triality_involution_fixed_groups_have_no_normal_even_SL2_derivedCentralQuotient
    hp hf F hF3 σ hσ _ hβ1 hβ2 hn K (by rw [Nat.card_eq_fintype_card, hK]) S' hS'n hS's
    hS'nab).false eS'

theorem ree_tits_fixed_root_exclusion
    {D : Type} [Group D] (hDs : IsSimpleGroup D) {t : StatedLieTag} (ht : t ∈ reeTitsTags)
    {m p f : ℕ} (hD : LieModel D t m p f) {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K]
    [Fintype K] (hK : Fintype.card K = 2 ^ n) (α : MulAut D) (hα : orderOf α = 2)
    (S : Subgroup D) (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) : False := by
  obtain ⟨-, hRT⟩ := reeTitsModel_of_lieModel ht hD
  obtain ⟨hα1, hα2⟩ := ne_one_and_sq_eq_one_of_orderOf_eq_two hα
  obtain ⟨hSs, hSnab, ⟨eS⟩⟩ := fixedRoot_subgroupOf hn hK hSα hSK
  have hDnab : ∃ a b : D, a * b ≠ b * a := by
    obtain ⟨φ⟩ := hSK
    obtain ⟨a, b, hab⟩ := sl2_exists_mul_ne (K := K)
    refine ⟨φ.symm a, φ.symm b, fun h => hab (φ.symm.injective (Subtype.ext ?_))⟩
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, h]
  exact (SymplecticFourStandard.Ree_Tits_involution_fixed_groups_have_no_normal_even_SL2
    D hDs hDnab K hn (by rw [Nat.card_eq_fintype_card, hK]) t p f hRT α hα1 hα2 _ hSn hSs
    hSnab).false eS

theorem fixedRootSelector_oddExceptional :
    FixedRootSelector fun D _ => ∃ (t : StatedLieTag) (m p f : ℕ), t ∉ classicalTags ∧
      p ≠ 2 ∧ LieModel D t m p f := by
  rintro D _ _ hDs ⟨t, m, p, f, htc, hp2, hD⟩ n hn K _ _ hK α hα S hSα hSn hSK -
  cases t
  case G2 => exact Or.inr (Or.inr (Or.inr (Or.inr
    (odd_G2_fixed_root_survivor hD hp2 hn K hK α hα S hSα hSn hSK))))
  case trialityD4 => exact (triality_fixed_root_exclusion hD hn K hK α hα S hSα hSn hSK).elim
  case twistedB2 =>
    rcases hD with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hSz⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (hp2 hSz.1).elim
  all_goals first
    | exact absurd htc (by decide)
    | exact (odd_residual_exceptional_fixed_root_exclusion (by decide) hD hp2 hn K hK α hα S hSα
        hSn hSK).elim
    | exact (ree_tits_fixed_root_exclusion hDs (by decide) hD hn K hK α hα S hSα hSn hSK).elim

end CFSG.LocalAnalysis.EvenBN.GMSK
