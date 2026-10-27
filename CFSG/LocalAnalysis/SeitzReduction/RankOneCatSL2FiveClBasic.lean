module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListOrth

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification

namespace FiveCl

section Components


theorem eq_of_component_statedSp {k : Type} [Field k] [Finite k] {j : ℕ} (hj : 1 ≤ j)
    (hk : Nat.card k = 5 ^ j) {m : ℕ} (hm : 1 ≤ m) {M : Subgroup (StatedSp m k)}
    (hM : IsComponent M) (hMm : LieModel (M ⧸ center M) .PSL 2 2 2) : m = 1 ∧ j = 1 := by
  have hp : (5 : ℕ).Prime := by norm_num
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    refine ⟨rfl, ?_⟩
    have hodd : Odd (Nat.card k) := by rw [hk]; exact FiveList.odd_five_pow j
    have hk2 : Nat.card k ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
    have hk3 : Nat.card k ≠ 3 := by rw [hk]; exact FiveList.five_pow_ne_three j
    let e := ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k
    have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 k le_rfl (Or.inr hk2)
      (Or.inr hk3)
    have hq := LocalCores.isQuasisimple_of_mulEquiv e hSL
    obtain rfl := OddClassSelector.eq_top_of_isComponent_of_quasisimple hq hM
    let φ : (⊤ : Subgroup (StatedSp 1 k)) ≃* SpecialLinearGroup (Fin 2) k :=
      Subgroup.topEquiv.trans e.symm
    let E : (⊤ : Subgroup (StatedSp 1 k)) ⧸ center (⊤ : Subgroup (StatedSp 1 k)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
      QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
    obtain ⟨hadm, hmod⟩ := FiveList.lieModel_of_equiv_psl_two hp hj hk hk2 hk3 E
    obtain ⟨-, -, h5⟩ := eq_five_of_lieModel_PSL_two_two hMm (by norm_num) hadm hmod
    exact eq_one_of_five_pow_eq_five h5
  · obtain ⟨hadm, hmod⟩ := FiveList.lieModel_of_isComponent_statedSp hp (by norm_num) hj hk hm2 hM
    obtain ⟨h1, -, -⟩ := eq_five_of_lieModel_PSL_two_two hMm (by norm_num) hadm hmod
    exact absurd h1 (by decide)

theorem eq_of_component_isometryGroup {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {j : ℕ} (hj : 1 ≤ j) (hk : Nat.card k = 5 ^ j)
    (B : LinearMap.BilinForm k W) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hW : 0 < Module.finrank k W)
    {M : Subgroup (CatalogueBAlternatingIsometry.isometryGroup B)} (hM : IsComponent M)
    (hMm : LieModel (M ⧸ center M) .PSL 2 2 2) : j = 1 ∧ Module.finrank k W = 2 := by
  obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B hB hnd
  obtain ⟨e⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp B hB hnd hdm
  have hM' := LocalCores.isComponent_map_mulEquiv e hM
  have hM'm := FiveList.lieModel_centerQuotient_of_mulEquiv
    (M.equivMapOfInjective e.toMonoidHom e.injective) hMm
  obtain ⟨h1, h2⟩ := eq_of_component_statedSp hj hk (by omega) hM' hM'm
  exact ⟨h2, by omega⟩

theorem eq_of_component_GL {k : Type} [Field k] [Finite k] {j : ℕ} (hj : 1 ≤ j)
    (hk : Nat.card k = 5 ^ j) {n : ℕ} (hn : 1 ≤ n) {M : Subgroup (GL (Fin n) k)}
    (hM : IsComponent M) (hMm : LieModel (M ⧸ center M) .PSL 2 2 2) : n = 2 ∧ j = 1 := by
  obtain ⟨hadm, hmod⟩ := FiveList.lieModel_of_isComponent_GL (by norm_num) hj hk hn hM
  obtain ⟨-, h2, h5⟩ := eq_five_of_lieModel_PSL_two_two hMm (by norm_num) hadm hmod
  exact ⟨h2, eq_one_of_five_pow_eq_five h5⟩

theorem eq_of_component_unitary {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {sigma : E ≃+* E} {e : ℕ} (he : 1 ≤ e) (hE : Nat.card E = (5 ^ e) ^ 2)
    (hW : 2 ≤ Module.finrank E W) (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hsig : ∀ z, sigma z = z ^ (5 ^ e))
    {L : Subgroup (CatalogueBUnitaryIsometry.isometryGroup h)} (hL : IsComponent L)
    (hLm : LieModel (L ⧸ center L) .PSL 2 2 2) : Module.finrank E W = 2 ∧ e = 1 := by
  have hp : (5 : ℕ).Prime := by norm_num
  have hfix := CatLeafProof.OddInner.card_fixedSubfield hsigma hne hE
  have h3 : 5 ^ e ≠ 3 := FiveList.five_pow_ne_three e
  have hodd : Odd (5 ^ e) := FiveList.odd_five_pow e
  have h2 : 5 ^ e ≠ 2 := fun h' => absurd (h' ▸ hodd) (by decide)
  rcases Nat.lt_or_ge (Module.finrank E W) 3 with hW3 | hW3
  · have hd : Module.finrank E W = 2 := by omega
    refine ⟨hd, ?_⟩
    have hquasi := CatalogueBUnitaryIsometry.specialIsometry_two_quasisimple h hsym hnd hsigma
      hne hd (by rw [hfix]; exact h2) (by rw [hfix]; exact h3)
    obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
      sigma h hsym hnd hsigma hne hd
    obtain rfl :=
      LocalAnalysis.ComponentInitial.CentralQuotientLift.eq_of_isComponent_of_quasisimple
        hquasi (Abelianization.commutator_subset_ker _) hL
    let E' := QuotientGroup.congr _ _ eSL (Subgroup.map_center_eq eSL)
    obtain ⟨hadm, hmod⟩ := FiveList.lieModel_of_equiv_psl_two hp he hfix (by rw [hfix]; exact h2)
      (by rw [hfix]; exact h3) E'
    obtain ⟨-, -, h5⟩ := eq_five_of_lieModel_PSL_two_two hLm (by norm_num) hadm hmod
    exact eq_one_of_five_pow_eq_five h5
  · exfalso
    have hadm : StatedLieAdmissible .PSU (Module.finrank E W) 5 e :=
      ⟨hp, he, hW3, fun h' => h2 (Prod.mk.inj h').2⟩
    obtain ⟨eX⟩ := OddClassSelector.nonempty_quotient_psu hp (by norm_num) he hE hW3 h hsym hnd
      hsigma hne hsig hL (MonoidHom.id L) Function.surjective_id (fun x hx => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
        rw [hx]
        exact one_mem _)
    have hmod : LieModel (L ⧸ center L) .PSU (Module.finrank E W) 5 e :=
      Or.inl ⟨by decide, hadm, E, inferInstance, inferInstance, hE, ⟨eX⟩⟩
    obtain ⟨h1, -, -⟩ := eq_five_of_lieModel_PSL_two_two hLm (by norm_num) hadm hmod
    exact absurd h1 (by decide)

end Components

end FiveCl

end CFSG.SeitzReduction.RankOne
