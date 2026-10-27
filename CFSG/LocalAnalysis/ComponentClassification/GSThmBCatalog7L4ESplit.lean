module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitCase

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

namespace Catalog7L4E

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

variable {k : Type} [Field k] [Finite k]

variable {A : Type} [Group A] {a : A} {L : Subgroup A}

theorem split_component_factor {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = ℓ ^ e) {ρ : A →* MulAut (projectiveSL 4 k)}
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 4) k} (hρa : ρ a = conjAut 4 k B * dualAut 4 k)
    (hB : (B : Matrix (Fin 4) (Fin 4) k)ᵀ = B)
    (hsplit : ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
      ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ x = 0) :
    5 ≤ Nat.card k ∧ ∃ ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k,
      (∀ v, v ⬝ᵥ (((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v) = (ψ v).det) ∧
      (L.map ρ = (splitLeftHom ψ).range.map (conjAut 4 k) ∨
        L.map ρ = (splitRightHom ψ).range.map (conjAut 4 k)) := by
  classical
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  rw [hρa] at hL₁
  obtain ⟨hXh, hmap, -⟩ := graph_component_lift (by norm_num) B hL₁
  set Xh := ⁅(L.map ρ).comap (conjAut 4 k), (L.map ρ).comap (conjAut 4 k)⁆ with hXhdef
  set R : GL (Fin 4) k := B⁻¹ with hRdef
  set O := CatalogueBGraphForm.isometryGroup 4 k R with hOdef
  have hR : (R : Matrix (Fin 4) (Fin 4) k)ᵀ = R := transpose_inv_eq_of_transpose_eq hB
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQdef
  have hQ : Q.polarBilin.Nondegenerate :=
    CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk2 R hR
  have hdim : Module.finrank k (Fin 4 → k) = 4 := Module.finrank_fin_fun k
  set eO := matrixOrthogonalEquiv hk2 R hR with heO
  set f : TauCeti.QuadraticMap.orthogonalGroup Q →* GL (Fin 4) k :=
    O.subtype.comp eO.toMonoidHom with hf
  have hfi : Function.Injective f := O.subtype_injective.comp eO.injective
  have hfr : (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).map f = O := by
    rw [← MonoidHom.range_eq_map, hf, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      eO.surjective, ← MonoidHom.range_eq_map, range_subtype]
  have hcov := orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ
    (Or.inr (Or.inr ⟨hdim, hsplit⟩))
  have hXq := (AssemblyBPredicates.isQuasisimple_iff_native Xh).1 hXh.2.2
  have hq3 : Nat.card k ≠ 3 := by
    intro hq3
    obtain ⟨hexc, -⟩ := hcov
    obtain ⟨hprime, -⟩ := hexc (Or.inr ⟨⟨hdim, hsplit⟩, Or.inr hq3⟩)
    have : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) :=
      isSolvable_of_prime_dvd_card_eq_or_eq hprime
    have : Group.IsSolvable O :=
      Group.isSolvable_of_isSolvable_injective (f := eO.symm.toMonoidHom) eO.symm.injective
    have : Group.IsSolvable Xh :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXh.1)
        (Subgroup.inclusion_injective hXh.1)
    have : Nontrivial Xh := CFSG.LocalCores.isQuasisimple_nontrivial hXq
    have : Group.IsPerfect Xh := hXq.1
    exact Group.IsPerfect.not_isSolvable Xh inferInstance
  have hq2 : Nat.card k ≠ 2 := by
    intro h
    rw [h] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  have hq5 : 5 ≤ Nat.card k := by
    have h1 : 2 ≤ Nat.card k := by
      rw [hk]
      exact hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
    have h4 : Nat.card k ≠ 4 := fun h => by
      rw [h] at hodd
      exact (Nat.not_odd_iff_even.mpr (by decide)) hodd
    omega
  obtain ⟨-, -, -, hsplitm, -, -, -⟩ := hcov
  obtain ⟨ψ, e, hQψ, hψe, hsup, hq₁, hq₂, hn₁, hn₂, -⟩ := hsplitm hdim hsplit hq2 hq3
  refine ⟨hq5, ψ, fun v => ?_, ?_⟩
  · have h := hQψ v
    rw [hQdef, CatalogueBLinearHigherB.matrixQuadraticForm, LinearMap.BilinMap.toQuadraticMap_apply,
      CatalogueBLinearHigherB.matrixForm_apply] at h
    exact h
  have hfe : ∀ d : DeterminantIsometries k, f (e.symm d) = linearConjGL ψ d.val := by
    intro d
    apply eq_of_mulVec_eq
    intro v
    rw [linearConjGL_mulVec]
    change ((eO (e.symm d) : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v = _
    rw [matrixOrthogonalEquiv_mulVec]
    have h1 := hψe (e.symm d) (ψ v)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h1
    rw [h1, LinearEquiv.symm_apply_apply]
  have hL₁r : ((determinantLeftFactor k).map e.symm.toMonoidHom).map f =
      (splitLeftHom ψ).range := by
    rw [determinantLeftFactor, MonoidHom.range_eq_map, Subgroup.map_map, Subgroup.map_map,
      MonoidHom.range_eq_map]
    congr 1
    ext U : 1
    exact hfe _
  have hL₂r : ((determinantRightFactor k).map e.symm.toMonoidHom).map f =
      (splitRightHom ψ).range := by
    rw [determinantRightFactor, MonoidHom.range_eq_map, Subgroup.map_map, Subgroup.map_map,
      MonoidHom.range_eq_map]
    congr 1
    ext W : 1
    exact hfe _
  have hcomp : ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.IsQuasisimple M → M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) →
      (M.subgroupOf (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))).Normal →
      CFSG.Assembly.IsComponentOf (M.map f) O := by
    intro M hMq hMle hMn
    have hM : CFSG.Assembly.IsComponentOf M ⊤ := by
      refine ⟨le_top, CFSG.Assembly.IsSubnormal.step hMle hMn
        (CFSG.Assembly.IsSubnormal.step le_top ?_ (CFSG.Assembly.IsSubnormal.refl _)),
        (AssemblyBPredicates.isQuasisimple_iff_native M).2 hMq⟩
      exact Subgroup.Normal.subgroupOf inferInstance _
    have := SymmetricLocal.isComponentOf_map_of_injective f hfi hM
    rwa [hfr] at this
  have hc₁ := hcomp _ hq₁ (hsup ▸ le_sup_left) hn₁
  have hc₂ := hcomp _ hq₂ (hsup ▸ le_sup_right) hn₂
  rw [hL₁r] at hc₁
  rw [hL₂r] at hc₂
  have hcommO : (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).map f = ⁅O, O⁆ := by
    rw [hf, ← Subgroup.map_map, ← Subgroup.map_subtype_commutator]
    congr 1
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eO.surjective]
  have hD : ⁅O, O⁆ = (splitLeftHom ψ).range ⊔ (splitRightHom ψ).range := by
    rw [← hcommO, hsup, Subgroup.map_sup, hL₁r, hL₂r]
  have hXhD : Xh ≤ ⁅O, O⁆ := by
    have : Group.IsPerfect Xh := ⟨hXh.2.2.1⟩
    rw [← Subgroup.commutator_eq_self (H := Xh)]
    exact Subgroup.commutator_mono hXh.1 hXh.1
  have hX : Xh = (splitLeftHom ψ).range ∨ Xh = (splitRightHom ψ).range := by
    rcases isComponentOf_eq_or_commute hXh hc₁ with h1 | h1
    · exact Or.inl h1
    rcases isComponentOf_eq_or_commute hXh hc₂ with h2 | h2
    · exact Or.inr h2
    exfalso
    have h1' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    have h2' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
    refine not_commute_of_isQuasisimple hXh.2.2 fun x hx y hy => ?_
    have hle : (splitLeftHom ψ).range ⊔ (splitRightHom ψ).range ≤ centralizer {x} :=
      sup_le (fun z hz => mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp (h1' hx)) z hz))
        (fun z hz => mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp (h2' hx)) z hz))
    have hy' := hle (hD ▸ hXhD hy)
    exact (mem_centralizer_singleton_iff.mp hy').symm
  rw [← hmap]
  rcases hX with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h])

omit [Finite k] in
theorem iso_of_factor {ρ : A →* MulAut (projectiveSL 4 k)} (hinj : Function.Injective ρ)
    {φ : SpecialLinearGroup (Fin 2) k →* GL (Fin 4) k}
    (hL : L.map ρ = φ.range.map (conjAut 4 k))
    (hker : ((conjAut 4 k).comp φ).ker = center (SpecialLinearGroup (Fin 2) k)) :
    Nonempty (L ≃* GorensteinWalter.PSL2 k) := by
  have hr : ((conjAut 4 k).comp φ).range = L.map ρ := by rw [MonoidHom.range_comp, hL]
  exact ⟨(L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hr.symm).trans
    ((QuotientGroup.quotientKerEquivRange _).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)))⟩

theorem ker_splitLeft (ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k) :
    ((conjAut 4 k).comp (splitLeftHom ψ)).ker = center (SpecialLinearGroup (Fin 2) k) := by
  ext U
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, conjAut_eq_one_iff (by norm_num),
    Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨t, ht⟩
    have hU := (splitLeftHom_eq_scalar_iff ψ U t).mp ht.symm
    refine ⟨t, ?_, ?_⟩
    · have h1 := congrArg Matrix.det hU
      rw [U.2, det_smul, det_one, mul_one, Fintype.card_fin] at h1
      exact h1.symm
    · rw [hU, Matrix.smul_one_eq_diagonal]
      rfl
  · rintro ⟨r, hr, hU⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [Fintype.card_fin] at hr
      norm_num at hr
    refine ⟨Units.mk0 r hr0, ((splitLeftHom_eq_scalar_iff ψ U _).mpr ?_).symm⟩
    rw [← hU, Units.val_mk0]
    change Matrix.scalar (Fin 2) r = r • (1 : Matrix (Fin 2) (Fin 2) k)
    rw [Matrix.smul_one_eq_diagonal]
    rfl

theorem ker_splitRight (ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k) :
    ((conjAut 4 k).comp (splitRightHom ψ)).ker = center (SpecialLinearGroup (Fin 2) k) := by
  ext U
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, conjAut_eq_one_iff (by norm_num)]
  constructor
  · rintro ⟨t, ht⟩
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact splitRightHom_eq_scalar ψ ht.symm g
  · intro hU
    obtain ⟨r, hr, hUr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hU
    rw [Fintype.card_fin] at hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      norm_num at hr
    have hrr : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hr)
    refine ⟨Units.mk0 r hr0, eq_of_mulVec_eq fun v => ?_⟩
    have hUi : ((U⁻¹ : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
        r • (1 : Matrix (Fin 2) (Fin 2) k) := by
      rw [Matrix.SpecialLinearGroup.coe_inv, ← hUr, Matrix.scalar_apply,
        Matrix.adjugate_diagonal]
      rw [Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      simp
    rw [splitRightHom_mulVec, hUi, Matrix.mul_smul, Matrix.mul_one, map_smul,
      LinearEquiv.symm_apply_apply, GeneralLinearGroup.coe_scalar, Units.val_mk0]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem split_component_iso {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = ℓ ^ e) {ρ : A →* MulAut (projectiveSL 4 k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 4) k} (hρa : ρ a = conjAut 4 k B * dualAut 4 k)
    (hB : (B : Matrix (Fin 4) (Fin 4) k)ᵀ = B)
    (hsplit : ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
      ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ x = 0) :
    5 ≤ Nat.card k ∧ Nonempty (L ≃* GorensteinWalter.PSL2 k) := by
  obtain ⟨h5, ψ, -, hL⟩ := split_component_factor hℓ hℓ2 he hk hL₁ hρa hB hsplit
  refine ⟨h5, ?_⟩
  rcases hL with hL | hL
  · exact iso_of_factor hinj hL (ker_splitLeft ψ)
  · exact iso_of_factor hinj hL (ker_splitRight ψ)

end Catalog7L4E

end CFSG.ComponentClassification.OddSelector
