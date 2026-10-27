module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUAnti

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Module Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.ComponentClassification.CatFactsL4U4 UnitaryOut StabU OIU CFSG.Assembly.LowTwoRank

section Tau

variable {k : Type*} [Field k]

theorem tau_conj_left (U : SpecialLinearGroup (Fin 2) k) :
    tau * specialRho (U, 1) * tau⁻¹ = specialRho (1, (SpecialLinearGroup.transpose U)⁻¹) := by
  rw [tau_inv]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change ((specialRho (U, 1)).val X.transpose).transpose = (specialRho (1, _)).val X
  rw [specialRho_apply, specialRho_apply]
  simp [Matrix.transpose_mul]

theorem tau_conj_right (W : SpecialLinearGroup (Fin 2) k) :
    tau * specialRho (1, W) * tau⁻¹ = specialRho ((SpecialLinearGroup.transpose W)⁻¹, 1) := by
  rw [tau_inv]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change ((specialRho (1, W)).val X.transpose).transpose = (specialRho (_, 1)).val X
  rw [specialRho_apply, specialRho_apply]
  simp [Matrix.transpose_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_transpose]

theorem tau_swap_left (x : DeterminantIsometries k) (hx : x ∈ determinantLeftFactor k) :
    tau * x * tau⁻¹ ∈ determinantRightFactor k := by
  obtain ⟨U, rfl⟩ := hx
  exact ⟨(SpecialLinearGroup.transpose U)⁻¹, (tau_conj_left U).symm⟩

theorem tau_swap_right (x : DeterminantIsometries k) (hx : x ∈ determinantRightFactor k) :
    tau * x * tau⁻¹ ∈ determinantLeftFactor k := by
  obtain ⟨W, rfl⟩ := hx
  exact ⟨(SpecialLinearGroup.transpose W)⁻¹, (tau_conj_right W).symm⟩

end Tau

theorem conj_comm_of_swap {G : Type*} [Group G] {L R Y : Subgroup G} {t : G}
    (hcomm : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) (hLR : ∀ x ∈ L, t * x * t⁻¹ ∈ R)
    (hRL : ∀ x ∈ R, t * x * t⁻¹ ∈ L) (hY : Y = L ∨ Y = R) :
    ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, t * y₁ * t⁻¹ * y₂ = y₂ * (t * y₁ * t⁻¹) := by
  intro y₁ hy₁ y₂ hy₂
  rcases hY with rfl | rfl
  · exact (hcomm _ hy₂ _ (hLR _ hy₁)).symm
  · exact hcomm _ (hRL _ hy₁) _ hy₂

theorem swap_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) {L R : Subgroup G} {t : G}
    (hLR : ∀ x ∈ L, t * x * t⁻¹ ∈ R) :
    ∀ y ∈ L.map e.toMonoidHom, e t * y * (e t)⁻¹ ∈ R.map e.toMonoidHom := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨_, hLR x hx, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]

theorem exists_swap_of_equiv {U H : Type*} [Group U] [Group H] {F : Subgroup U} (Φ : F ≃* H)
    {L R : Subgroup H} {t : H} (hcomm : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x)
    (hLR : ∀ x ∈ L, t * x * t⁻¹ ∈ R) (hRL : ∀ x ∈ R, t * x * t⁻¹ ∈ L) {Y : Subgroup U}
    (hYF : Y ≤ F) (hY : (Y.subgroupOf F).map Φ.toMonoidHom = L ∨
      (Y.subgroupOf F).map Φ.toMonoidHom = R) :
    ∃ T ∈ F, ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, T * y₁ * T⁻¹ * y₂ = y₂ * (T * y₁ * T⁻¹) := by
  have key := conj_comm_of_swap hcomm hLR hRL hY
  refine ⟨(Φ.symm t : U), (Φ.symm t).2, ?_⟩
  intro y₁ hy₁ y₂ hy₂
  have h1 := key (Φ ⟨y₁, hYF hy₁⟩) ⟨_, hy₁, rfl⟩ (Φ ⟨y₂, hYF hy₂⟩) ⟨_, hy₂, rfl⟩
  have h3 : Φ.symm t * ⟨y₁, hYF hy₁⟩ * (Φ.symm t)⁻¹ * ⟨y₂, hYF hy₂⟩ =
      ⟨y₂, hYF hy₂⟩ * (Φ.symm t * ⟨y₁, hYF hy₁⟩ * (Φ.symm t)⁻¹) := by
    apply Φ.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h1
  exact congrArg Subtype.val h3

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem anti_dichotomy (hp2 : p ≠ 2) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1) {c : K}
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = c • 1)
    {Y : Subgroup (sesqUnitaryGroup (stdHermForm h 4))}
    (hY : CFSG.Assembly.IsComponentOf Y
      (FixedCommutingProduct.fixedSubgroup (GSThmB.Catalog7L4EU.antiConjA h hAu)))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) {m : ℕ} (hXm : Blueprint.LieModel (X ⧸ center X) .PSL 2 p m) :
    c = 1 ∧
      ((∃ T ∈ FixedCommutingProduct.fixedSubgroup (GSThmB.Catalog7L4EU.antiConjA h hAu),
          ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, T * y₁ * T⁻¹ * y₂ = y₂ * (T * y₁ * T⁻¹)) ∨
        ∃ (E' : Type) (_ : Field E') (_ : Finite E'), Nat.card E' = Nat.card h.fixedField ^ 2 ∧
          Nonempty (X ⧸ center X ≃* GorensteinWalter.PSL2 E')) := by
  classical
  have hodd : Odd p := h.prime.odd_of_ne_two hp2
  have : Finite K := h.finite
  have : CharP K p := h.charP
  have hK : Nat.card h.fixedField = p ^ f := h.card_fixedField
  have hKodd : Odd (Nat.card h.fixedField) := by rw [hK]; exact hodd.pow
  have hτ₀ := StabU.antiunitaryMap_bijective h A
  have hτ₀B := StabU.stdHermForm_antiunitaryMap h hAu
  have hz0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hAA
    have h1 := congrArg Matrix.det hAA
    rw [det_mul, det_zero, show (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      h.bar.mapMatrix (A : Matrix (Fin 4) (Fin 4) K) from rfl, ← RingHom.map_det] at h1
    have hA0 : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    exact mul_ne_zero hA0 (fun h0 => hA0 ((map_eq_zero h.bar).1 h0)) h1
  have hμ : ∀ v, antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)
      (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) v) = ((Units.mk0 c hz0 : Kˣ) : K) • v :=
    StabU.antiunitaryMap_sq h _ hAA
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by rw [Module.finrank_fin_fun]; norm_num) (stdHermForm_isSymm h 4)
    (stdHermForm_separatingLeft h 4) _ hτ₀ hτ₀B (Units.mk0 c hz0) hμ
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY := Subgroup.subgroupOfEquivOfLe hY.1
  have hσ₁k := OddClassSelector.ker_comp_le_center eY.toMonoidHom eY.injective σ hσk
  have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
    have h1 := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at h1
    exact two_ne_zero_of_odd h hp2 h1
  rcases hμ1 with hμ1 | hμ1
  swap
  ·
    exfalso
    obtain ⟨-, hfinW, -, -, hB2⟩ := hall b t hb ht
    have : Module.Finite h.fixedField
        (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))) :=
      finite_conjFixed
    obtain ⟨B', -, halt, hnd, -, Φ, -⟩ := hB2 hμ1
    let F := (fixedCommutingEquiv h _ hτ₀ hτ₀B).trans Φ
    have hq := CatalogueBAlternatingIsometry.isometry_quasisimple_of_four_le B' halt hnd
      (by rw [hfinW, Module.finrank_fin_fun]) hKodd
    have hYtop := OddClassSelector.eq_top_of_isComponent_of_quasisimple hq
      (isComponent_map_of_isComponent F hY₁)
    obtain ⟨m', hd, ⟨eSp⟩⟩ :=
      CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B' halt hnd
    have heq := CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := m')
      (K := h.fixedField)
    let τ : StatedSp m' h.fixedField ≃* Y.subgroupOf
        (FixedCommutingProduct.fixedSubgroup (GSThmB.Catalog7L4EU.antiConjA h hAu)) :=
      (((MulEquiv.subgroupCongr heq).trans eSp.symm).trans
        ((MulEquiv.subgroupCongr hYtop).trans Subgroup.topEquiv).symm).trans
          ((Y.subgroupOf _).equivMapOfInjective F.toMonoidHom F.injective).symm
    have hm : 2 ≤ m' := by rw [hfinW, Module.finrank_fin_fun] at hd; omega
    have hns := (OddSelector.not_small_source_of_sp_cover hm h.prime hp2 h.one_le hK
      ((σ.comp eY.toMonoidHom).comp τ.toMonoidHom)
      (OddClassSelector.ker_comp_le_center τ.toMonoidHom τ.injective _ hσ₁k)).1 p m hp2
    exact hns (GSThmB.statedClassicalModel_of_lieModel_ne_zero (by norm_num) hXm)
  have hc1 : c = 1 := by
    have := congrArg Units.val hμ1
    simpa using this
  refine ⟨hc1, ?_⟩
  have hb1 : h.norm ((1 : Kˣ) : K) = (((Units.mk0 c hz0)⁻¹ : Kˣ) : K) := by
    rw [hμ1, inv_one, Units.val_one, UnitaryFieldData.norm, map_one, one_mul]
  obtain ⟨-, hfinW, -, hB1, -⟩ := hall 1 t hb1 ht
  have : Module.Finite h.fixedField (fixW h (A : Matrix (Fin 4) (Fin 4) K)) := finite_conjFixed
  have hdim : finrank h.fixedField (fixW h (A : Matrix (Fin 4) (Fin 4) K)) = 4 := by
    rw [hfinW, Module.finrank_fin_fun]
  obtain ⟨B', -, hsym, hnd, Φ, -⟩ := hB1 hμ1
  have hQ' : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
    rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
    exact hnd
  let Φ' : FixedCommutingProduct.fixedSubgroup (GSThmB.Catalog7L4EU.antiConjA h hAu) ≃*
      TauCeti.QuadraticMap.orthogonalGroup (CatalogueBOrthogonalDescent.originalQuadratic B') :=
    (fixedCommutingEquiv h _ hτ₀ hτ₀B).trans
      (Φ.trans (MulEquiv.subgroupCongr (isometryGroup_eq_orthogonalGroup B' hsym h2)))
  have hY' := isComponent_map_of_isComponent Φ' hY₁
  let eYY' : Y ≃* (Y.subgroupOf _).map Φ'.toMonoidHom :=
    eY.symm.trans ((Y.subgroupOf _).equivMapOfInjective _ Φ'.injective)
  have : Group.IsPerfect Y := ⟨hY.2.2.1⟩
  by_cases hsplit : ∃ S : Submodule h.fixedField (fixW h (A : Matrix (Fin 4) (Fin 4) K)),
      finrank h.fixedField S = 2 ∧
        ∀ x ∈ S, CatalogueBOrthogonalDescent.originalQuadratic B' x = 0
  ·
    left
    obtain ⟨hq5, -⟩ :=
      GSThmB.Catalog7L4EU.component_equiv_sl_of_split _ hQ' hKodd hdim hsplit hY'
    obtain ⟨-, -, -, hsplitm, -, -, -⟩ :=
      orthogonal_low_dimensional_fixed_derived_component_coverage _ hQ'
        (Or.inl ⟨hKodd, Or.inr (Or.inl hdim)⟩)
    obtain ⟨-, e₀, -, -, hsup, hq₁, hq₂, hn₁, hn₂, hcomm⟩ :=
      hsplitm hdim hsplit (by omega) (by omega)
    have hcomp : ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup
        (CatalogueBOrthogonalDescent.originalQuadratic B')), CFSG.IsQuasisimple M →
        M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup
          (CatalogueBOrthogonalDescent.originalQuadratic B')) →
        (M.subgroupOf (commutator (TauCeti.QuadraticMap.orthogonalGroup
          (CatalogueBOrthogonalDescent.originalQuadratic B')))).Normal →
        CFSG.IsComponent M := fun M hMq hMle hMn =>
      ⟨hMq, Subgroup.IsSubnormal.trans hMle hMn.isSubnormal
        (Subgroup.Normal.isSubnormal inferInstance)⟩
    have hL := hcomp _ hq₁ (hsup ▸ le_sup_left) hn₁
    have hR := hcomp _ hq₂ (hsup ▸ le_sup_right) hn₂
    have hYLR := GSThmB.Catalog7L4EU.eq_or_eq_of_isComponent hL hR hsup hY'
    exact exists_swap_of_equiv Φ' hcomm (swap_map e₀.symm (tau_swap_left (k := h.fixedField)))
      (swap_map e₀.symm (tau_swap_right (k := h.fixedField))) hY.1 hYLR
  ·
    right
    obtain ⟨hquasi, E', _, _, hE', ⟨eC⟩⟩ :=
      GSThmB.Catalog7L4EU.commutator_equiv_psl_of_nonsplit _ hQ' hKodd hdim hsplit
    have hYeq := LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hY' hquasi
    have h3K : 3 ≤ Nat.card h.fixedField := by
      rw [hK]
      have h3p : 3 ≤ p := by have := h.prime.two_le; omega
      exact h3p.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
    have h3 : 3 < Nat.card E' := by rw [hE']; nlinarith
    exact ⟨E', inferInstance, inferInstance, hE',
      GSThmB.Catalog7L4EU.center_quotient_equiv_of_psl h3 σ hσs hσk
        ((eYY'.trans (MulEquiv.subgroupCongr hYeq)).trans eC)⟩

end CFSG.ComponentClassification.HarrisLit.C3
