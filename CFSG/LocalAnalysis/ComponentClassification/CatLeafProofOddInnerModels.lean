module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerComp
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSU
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryAllDimensionsTwo
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import CFSG.LieType.Universal.SpecialLinear

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.OddInner

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem three_le_pow {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hj : 1 ≤ j) : 3 ≤ p ^ j := by
  have := hp.two_le
  have h3 : 3 ≤ p := by omega
  exact h3.trans (Nat.le_self_pow (by omega) p)

theorem five_le_pow {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hj : 1 ≤ j) (h3 : p ^ j ≠ 3) :
    5 ≤ p ^ j := by
  have h := three_le_pow hp hp2 hj
  obtain ⟨t, ht⟩ : Odd (p ^ j) := (hp.odd_of_ne_two hp2).pow
  omega

theorem admissible_PSp {p j m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hj : 1 ≤ j) (hm : 2 ≤ m) :
    StatedLieAdmissible .PSp m p j := by
  refine ⟨hp, hj, hm, fun h => ?_⟩
  have h1 : p ^ j = 2 := (Prod.mk.inj h).2
  have := three_le_pow hp hp2 hj
  omega

theorem admissible_PSL {p j n : ℕ} (hp : p.Prime) (hj : 1 ≤ j) (hn : 2 ≤ n)
    (h2 : n ≠ 2 ∨ p ^ j ≠ 2) (h3 : n ≠ 2 ∨ p ^ j ≠ 3) : StatedLieAdmissible .PSL n p j := by
  refine ⟨hp, hj, hn, fun h => ?_, fun h => ?_⟩
  · obtain ⟨hn', hq⟩ := Prod.mk.inj h
    rcases h2 with h2 | h2 <;> contradiction
  · obtain ⟨hn', hq⟩ := Prod.mk.inj h
    rcases h3 with h3 | h3 <;> contradiction

theorem oddLie_statedSp_self {k : Type} [Field k] [Finite k] {p j m : ℕ}
    (hadm : StatedLieAdmissible .PSp m p j) (hk : Nat.card k = p ^ j) :
    OddLieCentralQuotient p (StatedSp m k) :=
  ⟨.PSp, m, j, hadm, Or.inl ⟨by decide,
    LieType.Universal.Symplectic.statedClassicalModel_center_quotient m k hadm hk⟩⟩

theorem oddLie_SL {k : Type} [Field k] [Finite k] {p j n : ℕ}
    (hadm : StatedLieAdmissible .PSL n p j) (hk : Nat.card k = p ^ j) :
    OddLieCentralQuotient p (Matrix.SpecialLinearGroup (Fin n) k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  exact ⟨.PSL, m + 1, j, hadm, Or.inl ⟨by decide,
    LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient m k hadm hk⟩⟩

theorem oddLie_statedSp {k : Type} [Field k] [Finite k] {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hj : 1 ≤ j) (hk : Nat.card k = p ^ j) {m : ℕ} (hm : 1 ≤ m) {L : Subgroup (StatedSp m k)}
    (hL : IsComponent L) : OddLieCentralQuotient p L := by
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    let e := ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k
    by_cases h3 : p ^ j = 3
    · have : Group.IsSolvable (StatedSp 1 k) :=
        LieType.HighestRoot.isSolvable_of_mulEquiv (hk.trans h3) e.symm
      exact absurd hL (not_isComponent_of_isSolvable L)
    · have hq5 := five_le_pow hp hp2 hj h3
      have hadm : StatedLieAdmissible .PSL 2 p j :=
        admissible_PSL hp hj le_rfl (Or.inr (by omega)) (Or.inr h3)
      have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 k le_rfl
        (Or.inr (by rw [hk]; omega)) (Or.inr (by rw [hk]; exact h3))
      exact oddLie_of_isQuasisimple (LocalCores.isQuasisimple_of_mulEquiv e hSL)
        (oddLieCentralQuotient_of_mulEquiv e.symm (oddLie_SL hadm hk)) hL
  · have hadm := admissible_PSp hp hp2 hj hm2
    exact oddLie_of_isQuasisimple
      (LieType.Universal.Symplectic.isQuasisimple_of_admissible m k hadm hk)
      (oddLie_statedSp_self hadm hk) hL

theorem oddLie_isometryGroup {k W : Type} [Field k] [Finite k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hj : 1 ≤ j)
    (hk : Nat.card k = p ^ j) (B : LinearMap.BilinForm k W) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hW : 0 < Module.finrank k W)
    {L : Subgroup (CatalogueBAlternatingIsometry.isometryGroup B)} (hL : IsComponent L) :
    OddLieCentralQuotient p L := by
  obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B hB hnd
  obtain ⟨e⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp B hB hnd hdm
  exact oddLieCentralQuotient_of_component_equiv e
    (fun M hM => oddLie_statedSp hp hp2 hj hk (by omega) hM) hL

theorem oddLie_GL {k : Type} [Field k] [Finite k] {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j)
    (hk : Nat.card k = p ^ j) {n : ℕ} (hn : 1 ≤ n) {L : Subgroup (GL (Fin n) k)}
    (hL : IsComponent L) : OddLieCentralQuotient p L := by
  by_cases hsmall : n = 1 ∨ n = 2 ∧ (Nat.card k = 2 ∨ Nat.card k = 3)
  · have := CatalogueBGeneralLinear.generalLinear_small_solvable n k hsmall
    exact absurd hL (not_isComponent_of_isSolvable L)
  obtain ⟨hn2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters n k hn hsmall
  have : Group.IsPerfect L := hL.1.1
  have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
  obtain rfl := CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange n k hn2 h22 h23
    L hL.2
  have hadm : StatedLieAdmissible .PSL n p j :=
    admissible_PSL hp hj hn2 (by rw [← hk]; exact h22) (by rw [← hk]; exact h23)
  exact oddLieCentralQuotient_of_mulEquiv
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm (oddLie_SL hadm hk)

theorem card_fixedSubfield {E : Type} [Field E] [Finite E] {sigma : E ≃+* E}
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) {q : ℕ} (hE : Nat.card E = q ^ 2) :
    Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) = q := by
  have h1 := CatalogueBLinearTwoDescent.fixedSubfield_finrank E sigma hsigma hne
  let _ : Fintype E := Fintype.ofFinite E
  let _ : Fintype (CatalogueBLinearTwoDescent.fixedSubfield E sigma) := Fintype.ofFinite _
  have h2 := Module.card_eq_pow_finrank (K := CatalogueBLinearTwoDescent.fixedSubfield E sigma)
    (V := E)
  rw [h1, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hE] at h2
  exact (Nat.pow_left_injective two_ne_zero h2).symm

theorem oddLie_unitary {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {sigma : E ≃+* E} {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 2 ≤ Module.finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e))
    {L : Subgroup (CatalogueBUnitaryIsometry.isometryGroup h)} (hL : IsComponent L) :
    OddLieCentralQuotient ℓ L := by
  have hq3 := three_le_pow hℓ hℓ2 he
  have hfix := card_fixedSubfield hsigma hne hE
  rcases Nat.lt_or_ge (Module.finrank E W) 3 with hW3 | hW3
  · have hd : Module.finrank E W = 2 := by omega
    by_cases h3 : ℓ ^ e = 3
    · have := CatalogueBUnitaryIsometry.isometry_two_three_solvable h hsym hnd hsigma hne hd
        (hfix.trans h3)
      exact absurd hL (not_isComponent_of_isSolvable L)
    · have hq5 := five_le_pow hℓ hℓ2 he h3
      have hquasi := CatalogueBUnitaryIsometry.specialIsometry_two_quasisimple h hsym hnd hsigma
        hne hd (by rw [hfix]; omega) (by rw [hfix]; exact h3)
      obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
        sigma h hsym hnd hsigma hne hd
      have hadm : StatedLieAdmissible .PSL 2 ℓ e :=
        admissible_PSL hℓ he le_rfl (Or.inr (by omega)) (Or.inr h3)
      exact oddLie_of_commutator_le hquasi (Abelianization.commutator_subset_ker _)
        (oddLieCentralQuotient_of_mulEquiv eSL (oddLie_SL hadm hfix)) hL
  · have hadm : StatedLieAdmissible .PSU (Module.finrank E W) ℓ e :=
      ⟨hℓ, he, hW3, fun h' => by have := (Prod.mk.inj h').2; omega⟩
    obtain ⟨eX⟩ := OddClassSelector.nonempty_quotient_psu hℓ hℓ2 he hE hW3 h hsym hnd hsigma
      hne hsig hL (MonoidHom.id L) Function.surjective_id (fun x hx => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
        rw [hx]
        exact one_mem _)
    exact ⟨.PSU, Module.finrank E W, e, hadm, Or.inl ⟨by decide, hadm, E, inferInstance,
      inferInstance, hE, ⟨eX⟩⟩⟩

end CFSG.ComponentClassification.CatLeafProof.OddInner
