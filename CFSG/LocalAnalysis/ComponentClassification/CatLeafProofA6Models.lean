module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Toral
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerModels
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentCover

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def A6Safe (L : Type*) [Group L] : Prop :=
  Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) → IsPGroup 2 (center L)

theorem a6Safe_of_mulEquiv {L M : Type*} [Group L] [Group M] (e : L ≃* M) (h : A6Safe M) :
    A6Safe L := by
  rintro ⟨eA⟩
  exact (h ⟨(QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)).trans eA⟩).of_equiv
    (Subgroup.centerCongr e).symm

theorem a6Safe_of_isEmpty {L : Type*} [Group L]
    (h : IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 6))) : A6Safe L :=
  fun ⟨eA⟩ => (h.false eA).elim

theorem a6Safe_of_cover {M L : Type*} [Group M] [Group L] (hM : IsQuasisimple M) (σ : M →* L)
    (hσ : Function.Surjective σ) (hker : σ.ker ≤ center M) (h : A6Safe M) : A6Safe L := by
  rintro ⟨eA⟩
  obtain ⟨e⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hM σ hσ hker
  exact isPGroup_center_of_cover hM.1 σ hσ hker (h ⟨e.trans eA⟩)

theorem a6CentreForm_of_isSolvable {G : Type} [Group G] [Group.IsSolvable G] : A6CentreForm G :=
  fun L hL _ => absurd hL (OddInner.not_isComponent_of_isSolvable L)

theorem a6CentreForm_of_isQuasisimple {G : Type} [Group G] (hG : IsQuasisimple G)
    (h : A6Safe G) : A6CentreForm G := by
  intro L hL
  obtain rfl := OddClassSelector.eq_top_of_isComponent_of_quasisimple hG hL
  exact a6Safe_of_mulEquiv Subgroup.topEquiv h

theorem a6CentreForm_of_commutator_le {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hS : IsQuasisimple S) (hSX : _root_.commutator X ≤ S) (h : A6Safe S) : A6CentreForm X := by
  intro L hL
  obtain rfl := LocalAnalysis.ComponentInitial.CentralQuotientLift.eq_of_isComponent_of_quasisimple
    hS hSX hL
  exact h

theorem a6CentreForm_prod {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂]
    (h₁ : A6CentreForm G₁) (h₂ : A6CentreForm G₂) : A6CentreForm (G₁ × G₂) := by
  intro L hL
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      hL with h2 | h1
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component (MulEquiv.refl _) hL h2
    exact a6Safe_of_mulEquiv (MonoidHom.ofInjective hρi) (h₁ _ hρc)
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component MulEquiv.prodComm hL h1
    exact a6Safe_of_mulEquiv (MonoidHom.ofInjective hρi) (h₂ _ hρc)

theorem a6Safe_SL
    {k : Type} [Field k] [Finite k] {p j n : ℕ} (hadm : StatedLieAdmissible .PSL n p j)
    (hp2 : p ≠ 2) (hk : Nat.card k = p ^ j) : A6Safe (Matrix.SpecialLinearGroup (Fin n) k) := by
  intro hA
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hm : Blueprint.LieModel (SL(m + 1, k) ⧸ center SL(m + 1, k)) .PSL (m + 1) p j :=
    Or.inl ⟨by decide,
      LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient m k hadm hk⟩
  obtain ⟨-, h2, -⟩ := lieModel_of_a6 hA hadm hp2 hm
  obtain rfl : m = 1 := by omega
  classical
  have := Fintype.ofFinite k
  exact isPGroup_center_SL k

theorem a6CentreForm_GL
    {k : Type} [Field k] [Finite k] {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hj : 1 ≤ j)
    (hk : Nat.card k = p ^ j) {n : ℕ} (hn : 1 ≤ n) : A6CentreForm (GL (Fin n) k) := by
  intro L hL
  by_cases hsmall : n = 1 ∨ n = 2 ∧ (Nat.card k = 2 ∨ Nat.card k = 3)
  · have := CatalogueBGeneralLinear.generalLinear_small_solvable n k hsmall
    exact absurd hL (OddInner.not_isComponent_of_isSolvable L)
  obtain ⟨hn2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters n k hn hsmall
  have : Group.IsPerfect L := hL.1.1
  have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
  obtain rfl := CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange n k hn2 h22 h23
    L hL.2
  have hadm : StatedLieAdmissible .PSL n p j :=
    OddInner.admissible_PSL hp hj hn2 (by rw [← hk]; exact h22) (by rw [← hk]; exact h23)
  exact a6Safe_of_mulEquiv
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm (a6Safe_SL hadm hp2 hk)

theorem a6CentreForm_statedSp
    {k : Type} [Field k] [Finite k] {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hj : 1 ≤ j) (hk : Nat.card k = p ^ j) {m : ℕ} (hm : 1 ≤ m) : A6CentreForm (StatedSp m k) := by
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    let e := ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k
    by_cases h3 : p ^ j = 3
    · have : Group.IsSolvable (StatedSp 1 k) :=
        LieType.HighestRoot.isSolvable_of_mulEquiv (hk.trans h3) e.symm
      exact a6CentreForm_of_isSolvable
    · have hq5 := OddInner.five_le_pow hp hp2 hj h3
      have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 k le_rfl
        (Or.inr (by rw [hk]; omega)) (Or.inr (by rw [hk]; exact h3))
      exact a6CentreForm_of_isQuasisimple (LocalCores.isQuasisimple_of_mulEquiv e hSL)
        fun _ => isPGroup_center_of_mulEquiv_SL e.symm
  · have hadm := OddInner.admissible_PSp hp hp2 hj hm2
    exact a6CentreForm_of_isQuasisimple
      (LieType.Universal.Symplectic.isQuasisimple_of_admissible m k hadm hk)
      (a6Safe_of_isEmpty (isEmpty_a6_of_lieModel (MulEquiv.refl _) hadm hp2
        (Or.inl ⟨by decide,
          LieType.Universal.Symplectic.statedClassicalModel_center_quotient m k hadm hk⟩)
        fun h => absurd h.1 (by decide)))

theorem a6CentreForm_isometryGroup
    {k W : Type} [Field k] [Finite k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hj : 1 ≤ j)
    (hk : Nat.card k = p ^ j) (B : LinearMap.BilinForm k W) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hW : 0 < Module.finrank k W) :
    A6CentreForm (CatalogueBAlternatingIsometry.isometryGroup B) := by
  obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B hB hnd
  obtain ⟨e⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp B hB hnd hdm
  exact a6CentreForm_of_mulEquiv e (a6CentreForm_statedSp hp hp2 hj hk (by omega))

theorem a6CentreForm_unitary
    {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {sigma : E ≃+* E} {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 2 ≤ Module.finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e)) :
    A6CentreForm (CatalogueBUnitaryIsometry.isometryGroup h) := by
  have hq3 := OddInner.three_le_pow hℓ hℓ2 he
  have hfix := OddInner.card_fixedSubfield hsigma hne hE
  rcases Nat.lt_or_ge (Module.finrank E W) 3 with hW3 | hW3
  · have hd : Module.finrank E W = 2 := by omega
    by_cases h3 : ℓ ^ e = 3
    · have := CatalogueBUnitaryIsometry.isometry_two_three_solvable h hsym hnd hsigma hne hd
        (hfix.trans h3)
      exact a6CentreForm_of_isSolvable
    · have hq5 := OddInner.five_le_pow hℓ hℓ2 he h3
      have hquasi := CatalogueBUnitaryIsometry.specialIsometry_two_quasisimple h hsym hnd hsigma
        hne hd (by rw [hfix]; omega) (by rw [hfix]; exact h3)
      obtain ⟨-, -, eSL, -⟩ := CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
        sigma h hsym hnd hsigma hne hd
      exact a6CentreForm_of_commutator_le hquasi (Abelianization.commutator_subset_ker _)
        fun _ => isPGroup_center_of_mulEquiv_SL eSL
  · have hadm : StatedLieAdmissible .PSU (Module.finrank E W) ℓ e :=
      ⟨hℓ, he, hW3, fun h' => by have := (Prod.mk.inj h').2; omega⟩
    intro L hL
    obtain ⟨eX⟩ := OddClassSelector.nonempty_quotient_psu hℓ hℓ2 he hE hW3 h hsym hnd hsigma
      hne hsig hL (MonoidHom.id L) Function.surjective_id (fun x hx => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
        rw [hx]
        exact one_mem _)
    exact a6Safe_of_isEmpty (isEmpty_a6_of_lieModel (MulEquiv.refl _) hadm hℓ2
      (Or.inl ⟨by decide, hadm, E, inferInstance, inferInstance, hE, ⟨eX⟩⟩)
      fun h' => absurd h'.1 (by decide))

end CFSG.ComponentClassification.CatLeafProof
