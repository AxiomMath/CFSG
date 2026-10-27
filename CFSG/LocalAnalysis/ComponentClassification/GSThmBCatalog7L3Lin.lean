module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorULinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBPureGraph
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L3Orth

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

namespace Catalog7L3

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Matrices

variable {k : Type} [Field k]

theorem false_of_transpose_eq_neg (htwo : (2 : k) ≠ 0) (B : GL (Fin 3) k)
    (hB : (B : Matrix (Fin 3) (Fin 3) k)ᵀ = -B) : False := by
  have h1 := congrArg Matrix.det hB
  rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at h1
  have h2 : (2 : k) * (B : Matrix (Fin 3) (Fin 3) k).det = 0 := by
    linear_combination h1
  have hdet : (B : Matrix (Fin 3) (Fin 3) k).det ≠ 0 := by
    have := B.isUnit.map (Matrix.detMonoidHom (n := Fin 3) (R := k))
    exact this.ne_zero
  rcases mul_eq_zero.mp h2 with h | h
  · exact htwo h
  · exact hdet h

theorem isSquare_of_sq_eq_scalar {B : GL (Fin 3) k} {μ : kˣ}
    (hμ : GeneralLinearGroup.scalar (Fin 3) μ = B ^ 2) : IsSquare μ.val := by
  have h1 := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k).det) hμ
  simp only [GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val, Matrix.det_pow,
    Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at h1
  set d := (B : Matrix (Fin 3) (Fin 3) k).det with hd
  have hμ0 : (μ : k) ≠ 0 := μ.ne_zero
  refine ⟨d * (μ : k)⁻¹, ?_⟩
  field_simp
  linear_combination h1

end Matrices

section Inner

variable {A : Type} [Group A] [Finite A] {a : A} {L : Subgroup A}

theorem inner_false (ha : orderOf a = 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    {k : Type} [Field k] (hk : Nat.card k = ℓ ^ e) {ρ : A →* MulAut (projectiveSL 3 k)}
    (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ) (inner (projectiveSL 3 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 3) k} (hρa : ρ a = conjAut 3 k B) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f) (hZ : Odd (Nat.card (center L))) :
    False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hm3 : 3 ≤ 3 := le_rfl
  have h2 : conjAut 3 k (B ^ 2) = 1 := by
    rw [map_pow, ← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨μ, hμ⟩ := (conjAut_eq_one_iff hm3 _).mp h2
  have hB1 : ∀ c : kˣ, B ≠ GeneralLinearGroup.scalar (Fin 3) c := by
    intro c hc
    have h1 : ρ a = 1 := by rw [hρa, hc, conjAut_scalar]
    rw [← map_one ρ] at h1
    rw [hinj h1, orderOf_one] at ha
    omega
  rw [hρa] at hL₁
  obtain ⟨hXh, hmap, -⟩ := inner_component_lift hm3 B hL₁
  obtain ⟨r₀, hr₀⟩ := isSquare_of_sq_eq_scalar hμ
  have hr0 : r₀ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr₀
    exact μ.ne_zero hr₀
  set c₀ : kˣ := Units.mk0 r₀ hr0
  have hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin 3) (c₀ ^ 2) := by
    rw [← hμ]
    congr 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hr₀, sq]
  obtain ⟨r, hr2, ⟨eX⟩, hXi⟩ := square_component_sl hm3 htwo hsq hB1 hXh
  obtain ⟨eL⟩ := mulEquiv_of_lift_injective hinj hmap hXi
  set eLS := eL.trans eX
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · exact not_rank_or_odd_center_of_sl_two hk2 eLS (Or.inr hZ)
  · have hker : eLS.symm.toMonoidHom.ker ≤ center (SpecialLinearGroup (Fin r) k) := by
      intro x hx
      have : x = 1 := eLS.symm.injective (by rw [map_one]; exact hx)
      rw [this]
      exact one_mem _
    exact false_of_not_small_source
      (not_small_source_of_sl_cover hr3 hℓ hℓ2 he hk eLS.symm.toMonoidHom hker) hp2
      (Or.inl hsrc)

end Inner

section Graph

variable {A : Type} [Group A] {a : A} {L : Subgroup A}

theorem eq_one_of_mem_center_psl2 {k : Type} [Field k] [Finite k] (h3 : 3 < Nat.card k)
    {X : Type*} [Group X] (eX : X ≃* GorensteinWalter.PSL2 k) {z : X} (hz : z ∈ center X) :
    z = 1 := by
  have hZ := center_projectiveSL_two_eq_bot (E := k) (by omega)
  set e₁ := eX.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 k)
  have hz' : e₁ z ∈ center (projectiveSL 2 k) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e₁.surjective g
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) g']
  rw [hZ, mem_bot] at hz'
  exact e₁.injective (hz'.trans (map_one e₁).symm)

theorem graph_symm_iso {k : Type} [Field k] [Finite k] (hk2 : ringChar k ≠ 2)
    {ρ : A →* MulAut (projectiveSL 3 k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ) (inner (projectiveSL 3 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 3) k} (hρa : ρ a = conjAut 3 k B * dualAut 3 k)
    (hB : (B : Matrix (Fin 3) (Fin 3) k)ᵀ = B) :
    3 < Nat.card k ∧ Nonempty (L ≃* GorensteinWalter.PSL2 k) := by
  classical
  rw [hρa] at hL₁
  obtain ⟨hXh, hmap, -⟩ := graph_component_lift (le_refl 3) B hL₁
  set Xh := ⁅(L.map ρ).comap (conjAut 3 k), (L.map ρ).comap (conjAut 3 k)⁆ with hXhdef
  set R : GL (Fin 3) k := B⁻¹ with hRdef
  have hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R :=
    CatalogueBLinearHigherB.transpose_inv_of_transpose_eq B hB
  set I := CatalogueBGraphForm.isometryGroup 3 k R with hI
  let e : I ≃* TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBLinearHigherB.matrixQuadraticForm R) :=
    (CatalogueBLinearHigherB.isometryGroupEquiv R).symm.trans
      (MulEquiv.subgroupCongr (CatalogueBLinearHigherB.orthogonalGroup_matrixQuadraticForm hk2 R
        hR).symm)
  have hcomp : CFSG.IsComponent (Xh.subgroupOf I) :=
    (isComponentOf_iff_isComponent_subgroupOf hXh.1).mp hXh
  set Y := (Xh.subgroupOf I).map e.toMonoidHom with hY
  let eY : Xh.subgroupOf I ≃* Y := (Xh.subgroupOf I).equivMapOfInjective e.toMonoidHom e.injective
  have : Group.IsPerfect (Xh.subgroupOf I) := hcomp.1.1
  have : Group.IsPerfect Y := Group.IsPerfect.ofSurjective (f := eY.toMonoidHom) eY.surjective
  have hne : Y ≠ ⊥ := by
    have : Nontrivial (Xh.subgroupOf I) := CFSG.LocalCores.isQuasisimple_nontrivial hcomp.1
    have : Nontrivial Y := eY.symm.toEquiv.nontrivial
    exact Y.nontrivial_iff_ne_bot.mp inferInstance
  have hsn : Y.IsSubnormal := hcomp.2.map e.surjective
  have hodd : Odd (Nat.card k) := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two k hk2
  obtain ⟨h3, ⟨eP⟩⟩ := GSThmB.Catalog7L3.orthThree_perfect_subnormal hodd
    (CatalogueBLinearHigherB.matrixQuadraticForm R)
    (CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk2 R hR)
    (by rw [Module.finrank_fin_fun]) Y hne hsn
  let eX : Xh ≃* GorensteinWalter.PSL2 k := ((subgroupOfEquivOfLe hXh.1).symm.trans eY).trans eP
  have hXi : Function.Injective ((conjAut 3 k).comp Xh.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨t, ht⟩ := (conjAut_eq_one_iff (le_refl 3) _).mp hx
    have hx' : (x : GL (Fin 3) k) = GeneralLinearGroup.scalar (Fin 3) t := ht.symm
    apply eq_one_of_mem_center_psl2 h3 eX
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : GL (Fin 3) k) * (x : GL (Fin 3) k) = (x : GL (Fin 3) k) * g
    rw [hx']
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    exact ((Matrix.scalar_commute (t : k) (fun _ => Commute.all _ _) _).symm).eq
  obtain ⟨eL⟩ := mulEquiv_of_lift_injective hinj hmap hXi
  exact ⟨h3, ⟨eL.trans eX⟩⟩

end Graph

section GraphField

variable {A : Type} [Group A] {a : A} {L : Subgroup A}

theorem graph_field_false (ha : orderOf a = 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    {k : Type} [Field k] (hk : Nat.card k = ℓ ^ e) {ρ : A →* MulAut (projectiveSL 3 k)}
    (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ) (inner (projectiveSL 3 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 3) k} {σ : k ≃+* k} (hσ : σ ≠ 1)
    (hρa : ρ a = conjAut 3 k B * fieldAut 3 k σ * dualAut 3 k) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hα2 : (conjAut 3 k B * fieldAut 3 k σ * dualAut 3 k) ^ 2 = 1 := by
    rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨heven, hσx, H, hH⟩ :=
    UnitaryHigher.linear_graph_field_involution_descent hℓ he hk (le_refl 3) B σ hσ hα2
  have hg : 1 ≤ e / 2 := by obtain ⟨r, hr⟩ := heven; omega
  have hKe : Nat.card k = ℓ ^ (2 * (e / 2)) := by
    rw [hk]
    congr 1
    obtain ⟨r, hr⟩ := heven
    omega
  have hud : UnitaryFieldData ℓ (e / 2) k := ⟨hℓ, hg, hKe⟩
  have hσbar : ∀ x, σ x = hud.bar x := fun x => by rw [hσx, hud.bar_apply]
  obtain ⟨-, ⟨ι, -⟩, hNinn, -, hNC, hNnormal, hCN⟩ :=
    linear_graph_field_full_centralizer_rigidity hud (n := 3) (le_refl 3) σ hσbar
  set χ := conjAut 3 k H with hχ
  set β := fieldAut 3 k σ * dualAut 3 k with hβ
  set N := (unitarySU ℓ (e / 2) k 3).map (conjAut 3 k) with hNdef
  have hρa' : ρ a = χ * β * χ⁻¹ := by rw [hρa, hH]
  have hY : (OuterAutomorphisms.inner (projectiveSL 3 k) ⊓ centralizer {ρ a}).map
      (MulAut.conj χ⁻¹).toMonoidHom =
        OuterAutomorphisms.inner (projectiveSL 3 k) ⊓ centralizer {β} := by
    rw [map_conj_inner_inf_centralizer, hρa']
    congr 3
    group
  set L₀ := (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom with hL₀def
  have hL₀ : CFSG.Assembly.IsComponentOf L₀
      (OuterAutomorphisms.inner (projectiveSL 3 k) ⊓ centralizer {β}) := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [hY] at this
  have := finite_mulAut_projectiveSL (k := k) 3
  have hL₀N : CFSG.Assembly.IsComponentOf L₀ N := by
    refine isComponentOf_of_normal_of_comm (le_inf hNinn hNC)
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNC hNnormal hy.2) ?_ hL₀
    intro x _ hx y _ hy
    rw [hCN] at hx hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self β i j).eq
  have hK2 : Nat.card k = (ℓ ^ (e / 2)) ^ 2 := by rw [hKe, ← pow_mul, mul_comm]
  have eU : unitaryPSU hud 3 ≃* StatedProj (StatedSU 3 (ℓ ^ (e / 2)) k) :=
    unitaryPSUEquiv hud (by omega)
  have hnq : (3, ℓ ^ (e / 2)) ≠ (3, 2) := fun h => by
    have h2 := congrArg Prod.snd h
    simp only at h2
    have : ℓ ∣ 2 := by
      rw [← h2]
      exact dvd_pow_self ℓ (by omega)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp this)
  have : IsSimpleGroup (StatedProj (StatedSU 3 (ℓ ^ (e / 2)) k)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU k ℓ (e / 2) hK2 3
      (le_refl 3) hnq
  have : IsSimpleGroup (unitaryPSU hud 3) := eU.isSimpleGroup
  have hNs : IsSimpleGroup N := ι.symm.isSimpleGroup
  have hL₀eq : L₀ = N := eq_of_isComponentOf_simple hNs hL₀N
  have hLimg : L.map ρ = N.map (MulAut.conj χ).toMonoidHom := by
    rw [← hL₀eq, hL₀def, map_conj_inv_map_conj]
  have eL : L ≃* unitaryPSU hud 3 :=
    ((L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hLimg).trans
      ((N.equivMapOfInjective _ (MulAut.conj χ).injective).symm))).trans ι.symm
  have hLnab : ∃ x y : L, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := exists_ne_commute_of_isQuasisimple hL₁.2.2
    set eρ := L.equivMapOfInjective ρ hinj
    refine ⟨eρ.symm x, eρ.symm y, fun hc => hxy ?_⟩
    have := congrArg eρ hc
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  have : IsSimpleGroup L := eL.isSimpleGroup
  have eZ : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_isSimpleGroup hLnab)).trans
      QuotientGroup.quotientBot
  have hk2 : (2 : k) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq k ℓ]; exact hℓ2)
  obtain ⟨a', b', ha', hb', hab'⟩ := OddClassSelector.exists_antifixed_sq_add_sq hud hℓ2
  have hsigU : CatalogueBUnitaryTwo.unitaryFieldConjugation ℓ (e / 2) hud.card_eq_sq =
      CFSG.LieType.BorelTits.unitaryInvolution k ℓ (e / 2) :=
    RingEquiv.ext fun z => by
      rw [CatalogueBUnitaryTwo.unitaryFieldConjugation_apply,
        CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rw [hsigU] at ha' hb'
  have hSU : CFSG.LieType.Universal.Unitary.SUid
      (CFSG.LieType.BorelTits.unitaryInvolution k ℓ (e / 2)) 3 = StatedSU 3 (ℓ ^ (e / 2)) k :=
    CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK2 3
  obtain ⟨φq, hφq⟩ := OddClassSelector.exists_quaternion_statedProj hk2 _ (le_refl 3) hSU ha' hb'
    hab'
  set ψ := (eZ.trans (eL.trans eU)).symm with hψ
  exact not_psl_two_odd_of_quaternion (ψ.toMonoidHom.comp φq) (ψ.injective.comp hφq) hp2 hsrc

end GraphField

section Main

variable {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]

theorem psl3_component_iso (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2)
    {L : Subgroup A} (hLW : L ≤ W)
    (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hZ : Odd (Nat.card (center L))) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ e)
    (φ : W ≃* projectiveSL 3 k) :
    3 < Nat.card k ∧ Nonempty (L ≃* GorensteinWalter.PSL2 k) := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hZP := center_projectiveSL_eq_bot (k := k) (le_refl 3)
  obtain ⟨ρ, hinj, hρW, -, -⟩ := socle_extension hCW φ hZP
  obtain ⟨-, -, -, hL₁⟩ := socle_images φ hinj hρW hLW hL
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) (le_refl 3)
  obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ a)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      exact (inner_false ha hℓ hℓ2 he hk hinj hL₁ hρa hp2 hsrc hZ).elim
    · exact (field_case_false ha (le_refl 3) hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2
        (Or.inl hsrc)).elim
  · rw [pow_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      have hα2 : (conjAut 3 k B * dualAut 3 k) ^ 2 = 1 := by
        rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
      rcases transpose_eq_or_eq_neg_of_pureGraph (le_refl 3) B hα2 with hB | hB
      · exact graph_symm_iso hk2 hinj hL₁ hρa hB
      · exact (false_of_transpose_eq_neg htwo B hB).elim
    · exact (graph_field_false ha hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc).elim

end Main

end Catalog7L3

end CFSG.ComponentClassification.OddSelector
