module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.TwoSevenOddCore
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed

public section

open scoped MatrixGroups commutatorElement

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Matrix CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (mem_coordinateG_iff
  sl_eq_of_coordinateGLAction_eq coordinateGLAction_mem_G fieldExtension_mem_E
  fieldExtension_mem_G_iff even_linear_two_involution_normal_forms
  linear_two_automorphism_semilinear_isomorphism)

namespace CaseAAux

section Coordinates

variable (F : Type) [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def slCoordHom : SpecialLinearGroup (Fin 2) F →* coordinateG F where
  toFun A := ⟨coordinateGLAction F (SpecialLinearGroup.toGL A),
    coordinateGLAction_mem_G (Units.ext (by
      rw [GeneralLinearGroup.val_det_apply]; exact A.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by simp)

@[expose] noncomputable def slCoord : SpecialLinearGroup (Fin 2) F ≃* coordinateG F :=
  MulEquiv.ofBijective (slCoordHom F)
    ⟨fun A B h => sl_eq_of_coordinateGLAction_eq (congrArg Subtype.val h), fun g => by
      obtain ⟨A, hA⟩ := mem_coordinateG_iff.mp g.2
      exact ⟨A, Subtype.ext hA⟩⟩

variable {F}

theorem coe_slCoord (A : SpecialLinearGroup (Fin 2) F) :
    ((slCoord F A : coordinateG F) : Equiv.Perm (Omega F)) =
      coordinateGLAction F (SpecialLinearGroup.toGL A) := rfl

theorem fieldExtension_conj_slCoord (σ : F ≃+* F) (A : SpecialLinearGroup (Fin 2) F) :
    fieldExtension F σ * (slCoord F A : Equiv.Perm (Omega F)) * (fieldExtension F σ)⁻¹ =
      (slCoord F (SpecialLinearGroup.map σ.toRingHom A) : Equiv.Perm (Omega F)) := by
  rw [coe_slCoord, coe_slCoord, CFSG.Wreathed.CentralSL2.fieldExtension_conj_coordinateGLAction]
  congr 1
  ext i j
  rfl

end Coordinates

section Embedding

variable {F : Type} [Field F] [Finite F]

theorem exists_coordinate_embedding {X : Type*} [Group X] {D : Subgroup X} [D.Normal]
    (hfaith : ∀ h : X, (∀ x ∈ D, h⁻¹ * x * h = x) → h = 1) (e : D ≃* coordinateG F) :
    ∃ a : X →* Equiv.Perm (Omega F), Function.Injective a ∧ (∀ x, a x ∈ coordinateE F) ∧
      ∀ (d : X) (hd : d ∈ D), a d = (e ⟨d, hd⟩ : Equiv.Perm (Omega F)) := by
  obtain ⟨c, hc1, hc2, -⟩ := linear_two_automorphism_semilinear_isomorphism F
  let δ : X →* MulAut (coordinateG F) :=
    { toFun := fun n => e.symm.trans ((MulAut.conjNormal n).trans e)
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hδ : ∀ (n : X) (g : coordinateG F), ((δ n g : coordinateG F) : Equiv.Perm (Omega F)) =
      (e (MulAut.conjNormal n (e.symm g)) : Equiv.Perm (Omega F)) := fun n g => rfl
  let a₀ : X →* coordinateE F := c.symm.toMonoidHom.comp δ
  have ha_inj : Function.Injective a₀ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have h1 : δ n = 1 := by
      have := congrArg c hn
      simpa [a₀] using this
    refine inv_eq_one.mp (hfaith n⁻¹ fun x hx => ?_)
    have h2 := congrArg (fun φ : MulAut (coordinateG F) => φ (e ⟨x, hx⟩)) h1
    simp only [δ, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
    have h3 := congrArg Subtype.val (e.injective h2)
    simp only [MulAut.conjNormal_apply] at h3
    simpa using h3
  have ha_D : ∀ (d : X) (hd : d ∈ D), ((a₀ d : coordinateE F) : Equiv.Perm (Omega F)) =
      (e ⟨d, hd⟩ : Equiv.Perm (Omega F)) := by
    intro d hd
    have hGE : ((e ⟨d, hd⟩ : coordinateG F) : Equiv.Perm (Omega F)) ∈ coordinateE F :=
      (coordinateG_le_D F).trans (coordinateD_le_E F) (e ⟨d, hd⟩).2
    have h1 : δ d = MulAut.conj (e ⟨d, hd⟩) := by
      ext g
      rw [hδ, MulAut.conj_apply]
      have h2 : MulAut.conjNormal d (e.symm g) = ⟨d, hd⟩ * e.symm g * (⟨d, hd⟩ : D)⁻¹ :=
        Subtype.ext (by simp [MulAut.conjNormal_apply])
      rw [h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have h3 : a₀ d = ⟨_, hGE⟩ := by
      apply c.injective
      change c (c.symm (δ d)) = _
      rw [MulEquiv.apply_symm_apply, h1, hc2]
    rw [h3]
  refine ⟨(coordinateE F).subtype.comp a₀, (coordinateE F).subtype_injective.comp ha_inj,
    fun x => (a₀ x).2, fun d hd => ha_D d hd⟩


open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog in
theorem exists_coordinate_field [CharP F 2] {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ (2 * f))
    {X : Type*} [Group X] {D : Subgroup X} [D.Normal]
    (hfaith : ∀ h : X, (∀ x ∈ D, h⁻¹ * x * h = x) → h = 1) (e : D ≃* coordinateG F)
    {t : X} (ht : orderOf t = 2) {J : Subgroup X} (hJD : J ≤ D)
    (hJt : ∀ j ∈ J, j * t = t * j) (hJ : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) :
    ∃ (σ : F ≃+* F) (a : X →* Equiv.Perm (Omega F)), (∀ x, σ x = x ^ 2 ^ f) ∧
      orderOf σ = 2 ∧ Nat.card (CFSG.ComponentClassification.CatalogueBLinearTwoFixed.fixedField
        F σ) = 2 ^ f ∧ Function.Injective a ∧ (∀ x, a x ∈ coordinateE F) ∧
      (∀ d ∈ D, a d ∈ coordinateG F) ∧ (∀ g ∈ coordinateG F, ∃ d ∈ D, a d = g) ∧
      a t = fieldExtension F σ := by
  obtain ⟨a, ha_inj, haE, haD⟩ := exists_coordinate_embedding hfaith e
  have haG : ∀ d ∈ D, a d ∈ coordinateG F := fun d hd => by
    rw [haD d hd]; exact (e ⟨d, hd⟩).2
  have hnf := (even_linear_two_involution_normal_forms (K := F) (f := 2 * f) (by omega)
    hF).2.2.2.2.2.2.2.2.2
  have hot : orderOf (a t) = 2 := by rw [orderOf_injective a ha_inj, ht]
  rcases hnf (a t) (haE t) hot with ⟨-, h, hh, hht⟩ |
    ⟨-, -, σ, hσ1, hσ2, hσx, -, -, ⟨h, hh, hht⟩, k, hkset, hkcard⟩
  ·
    exfalso
    have hhE : h ∈ coordinateE F := coordinateD_le_E F (coordinateG_le_D F hh)
    have htr : ∀ j ∈ J, ∃ b : F, h⁻¹ * a j * h = translation F b := by
      intro j hj
      have hjG : h⁻¹ * a j * h ∈ coordinateG F :=
        mul_mem (mul_mem (inv_mem hh) (haG j (hJD hj))) hh
      have hmem : h⁻¹ * a j * h ∈ coordinateE F ⊓ Subgroup.centralizer {translation F 1} := by
        refine Subgroup.mem_inf.mpr ⟨coordinateD_le_E F (coordinateG_le_D F hjG), ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hc : a j * a t = a t * a j := by rw [← map_mul, ← map_mul, hJt j hj]
        rw [hht] at hc
        calc h⁻¹ * a j * h * translation F 1 =
            h⁻¹ * (a j * (h * translation F 1 * h⁻¹)) * h := by group
          _ = h⁻¹ * ((h * translation F 1 * h⁻¹) * a j) * h := by rw [hc]
          _ = translation F 1 * (h⁻¹ * a j * h) := by group
      obtain ⟨b, φ, hbφ⟩ := mem_inf_centralizer_translation_one_iff.mp hmem
      have hφG : fieldExtension F φ ∈ coordinateG F := by
        have : fieldExtension F φ = (translation F b)⁻¹ * (h⁻¹ * a j * h) := by
          rw [hbφ]; group
        rw [this]
        exact mul_mem (inv_mem (CFSG.LinearGroups.translation_mem_coordinateG b)) hjG
      rw [fieldExtension_mem_G_iff] at hφG
      subst hφG
      refine ⟨b, ?_⟩
      rw [hbφ, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.fieldExtension_one, mul_one]
    obtain ⟨x, hx, y, hy, hxy⟩ := hJ
    obtain ⟨b, hb⟩ := htr x hx
    obtain ⟨c, hc⟩ := htr y hy
    apply hxy
    apply ha_inj
    have hxe : a x = h * translation F b * h⁻¹ := by rw [← hb]; group
    have hye : a y = h * translation F c * h⁻¹ := by rw [← hc]; group
    rw [map_mul, map_mul, hxe, hye]
    calc h * translation F b * h⁻¹ * (h * translation F c * h⁻¹) =
        h * (translation F b * translation F c) * h⁻¹ := by group
      _ = h * (translation F c * translation F b) * h⁻¹ := by
          rw [translation_mul_translation, translation_mul_translation, add_comm]
      _ = h * translation F c * h⁻¹ * (h * translation F b * h⁻¹) := by group
  ·
    have hhE : h ∈ coordinateE F := coordinateD_le_E F (coordinateG_le_D F hh)
    have hf2 : 2 * f / 2 = f := by omega
    rw [hf2] at hσx hkcard
    have hk : CFSG.ComponentClassification.CatalogueBLinearTwoFixed.fixedField F σ = k := by
      ext x
      rw [CFSG.ComponentClassification.CatalogueBLinearTwoFixed.mem_fixedField_iff,
        ← SetLike.mem_coe, hkset, Set.mem_ofPred_eq]
    refine ⟨σ, (MulAut.conj h⁻¹).toMonoidHom.comp a, hσx, ?_, by rw [hk, hkcard], ?_,
      fun x => ?_, fun d hd => ?_, fun g hg => ?_, ?_⟩
    · exact orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
    · exact (MulAut.conj h⁻¹).injective.comp ha_inj
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact mul_mem (mul_mem (inv_mem hhE) (haE x)) hhE
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact mul_mem (mul_mem (inv_mem hh) (haG d hd)) hh
    · have hg' : h * g * h⁻¹ ∈ coordinateG F := mul_mem (mul_mem hh hg) (inv_mem hh)
      refine ⟨(e.symm ⟨_, hg'⟩ : X), (e.symm ⟨_, hg'⟩).2, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [haD _ (e.symm ⟨_, hg'⟩).2]
      simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]
      group
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        hht]
      group


open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
  CFSG.ComponentClassification.CatalogueBLinearTwoFixed in
theorem map_eq_subfieldGImage [CharP F 2] {f : ℕ} {σ : F ≃+* F} (hσ2 : orderOf σ = 2)
    (hk : Nat.card (fixedField F σ) = 2 ^ f) {X : Type*} [Group X]
    {D : Subgroup X} {a : X →* Equiv.Perm (Omega F)} (ha_inj : Function.Injective a)
    (haG : ∀ d ∈ D, a d ∈ coordinateG F) {t : X}
    (hat : a t = fieldExtension F σ) {J : Subgroup X} (hJD : J ≤ D)
    (hJt : ∀ j ∈ J, j * t = t * j) (hJcard : Nat.card J = 2 ^ f * ((2 ^ f) ^ 2 - 1)) :
    J.map a = subfieldGImage (fixedField F σ) := by
  have hle : J.map a ≤ subfieldGImage (fixedField F σ) := by
    rw [subfieldGImage_eq_centralizer hσ2]
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨haG j (hJD hj), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hat, ← map_mul, ← map_mul, hJt j hj]
  have hcard : Nat.card (subfieldGImage (fixedField F σ)) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [subfieldGImage_eq, ← Nat.card_congr (subfieldCoordinateEquivImage F _).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coordinateD_eq_G,
      ← Nat.card_congr (slCoord (fixedField F σ)).toEquiv,
      CFSG.GorensteinWalter.sl2_card_formula, hk]
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [hcard, Subgroup.card_map_of_injective ha_inj, hJcard])

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
  CFSG.ComponentClassification.CatalogueBLinearTwoFixed in
theorem eq_one_of_commute_subfield [CharP F 2] {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ (2 * f)) {σ : F ≃+* F} (hσx : ∀ x, σ x = x ^ 2 ^ f)
    (hσ2 : orderOf σ = 2) (hk : Nat.card (fixedField F σ) = 2 ^ f) {X : Type*} [Group X]
    {D : Subgroup X} {a : X →* Equiv.Perm (Omega F)} (ha_inj : Function.Injective a)
    (haE : ∀ x, a x ∈ coordinateE F) (haG : ∀ d ∈ D, a d ∈ coordinateG F) {t : X}
    (hat : a t = fieldExtension F σ) {J : Subgroup X} (hJD : J ≤ D)
    (hJt : ∀ j ∈ J, j * t = t * j) (hJcard : Nat.card J = 2 ^ f * ((2 ^ f) ^ 2 - 1)) {y : X}
    (hy : ∀ j ∈ J, y * j = j * y) (hodd : Odd (orderOf y)) : y = 1 := by
  have heq := map_eq_subfieldGImage hσ2 hk ha_inj haG hat hJD hJt hJcard
  have hyC : a y ∈ coordinateE F ⊓
      Subgroup.centralizer (subfieldGImage (fixedField F σ) : Set (Equiv.Perm (Omega F))) := by
    refine Subgroup.mem_inf.mpr ⟨haE y, ?_⟩
    rw [← heq, Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, ← map_mul, hy j hj]
  rw [inf_centralizer_subfieldGImage hf hF hσx] at hyC
  have h2 : (fieldExtension F σ) ^ 2 = 1 := by
    rw [sq]; exact fieldExtension_sq_eq_one hσ2
  have hdvd : orderOf (a y) ∣ 2 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyC
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, h2,
      _root_.one_zpow]
  rw [orderOf_injective a ha_inj] at hdvd
  have h1 : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

end Embedding

end CaseAAux


open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.OddStandard.Seitz77 (Datum)
open CaseAAux
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog (subfieldGImage)
open CFSG.ComponentClassification.CatalogueBLinearTwoFixed (fixedField)

theorem CaseAAux.card_map_of_injOn {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) {S : Subgroup X}
    (hS : ∀ x ∈ S, φ x = 1 → x = 1) : Nat.card (S.map φ) = Nat.card S := by
  have hinj : Function.Injective (φ.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hS x x.2 hx)
  calc Nat.card (S.map φ) = Nat.card (φ.comp S.subtype).range := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
    _ = Nat.card S := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

namespace WData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}

section CaseA

variable {f : ℕ} {w : WData d Vi (2 ^ f)} {K : Type} [Field K] {D : LeviData A Vi K}

theorem CaseA.exists_coordinateG (hA : w.CaseA f D.lev.range) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ (2 * f) ∧
      Nonempty (normalClosure (w.Ltil D.lev.range : Set w.Ntil) ≃* coordinateG F) := by
  obtain ⟨-, -, -, hDE, -, -, -⟩ := hA.layer
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.layer w.Ntil) .PSL 2 2 (2 * f) := by
    rcases hA.model with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  exact ⟨F, inferInstance, inferInstance, hF, ⟨(MulEquiv.subgroupCongr hDE).trans
    (e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
      (pslEquivCoordinateG F)))⟩⟩

variable [Finite G]

theorem projTil_injOn_Lbar {f' : ℕ} (hf : 3 ≤ f') {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f')) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f'))
    [Finite K] (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f') :
    ∀ x ∈ w.Lbar D.lev.range, w.projTil x = 1 → x = 1 := by
  have : CharP K 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hKc
  obtain ⟨hsimp, -, hE, -, -, -, -⟩ := w.lbar_data hf hR hW hN hKc D
  intro x hx h1
  exact w.Lbar_inf_oddCore D hE hx ((QuotientGroup.eq_one_iff _).mp h1)

theorem card_Ltil {f' : ℕ} (hf : 3 ≤ f') {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f')) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f'))
    [Finite K] (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f') :
    Nat.card (w.Ltil D.lev.range) = 2 ^ f' * ((2 ^ f') ^ 2 - 1) := by
  rw [Ltil, card_map_of_injOn _ (w.projTil_injOn_Lbar hf hR hW hN D hKc),
    Nat.card_congr (w.lbarEquiv D).toEquiv, CFSG.GorensteinWalter.sl2_card_formula, hKc]

theorem exists_Ltil_mul_ne {f' : ℕ} (hf : 3 ≤ f') {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f')) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f'))
    [Finite K] (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f') :
    ∃ x ∈ w.Ltil D.lev.range, ∃ y ∈ w.Ltil D.lev.range, x * y ≠ y * x := by
  have : CharP K 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hKc
  obtain ⟨-, ⟨x, y, hxy⟩, -⟩ := w.lbar_data hf hR hW hN hKc D
  refine ⟨w.projTil x, ⟨x, x.2, rfl⟩, w.projTil y, ⟨y, y.2, rfl⟩, fun he => hxy ?_⟩
  have h1 : w.projTil ((x : w.Nbar) * y * ((y : w.Nbar) * x)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, he, mul_inv_cancel]
  have h2 := w.projTil_injOn_Lbar hf hR hW hN D hKc _
    (mul_mem (mul_mem x.2 y.2) (inv_mem (mul_mem y.2 x.2))) h1
  exact Subtype.ext (mul_inv_eq_one.mp h2)

theorem CaseA.exists_field {f' : ℕ} (hf : 3 ≤ f') {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f')) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    {w : WData d Vi (2 ^ f')}
    [Finite K] {D : LeviData A Vi K} (hKc : Nat.card K = 2 ^ f') (hA : w.CaseA f' D.lev.range) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (σ : F ≃+* F)
      (a : w.Ntil →* Equiv.Perm (Omega F)),
      Nat.card F = 2 ^ (2 * f') ∧ (∀ x, σ x = x ^ 2 ^ f') ∧ orderOf σ = 2 ∧
      Function.Injective a ∧ (∀ x, a x ∈ coordinateE F) ∧
      (∀ x ∈ normalClosure (w.Ltil D.lev.range : Set w.Ntil), a x ∈ coordinateG F) ∧
      (∀ g ∈ coordinateG F, ∃ x ∈ normalClosure (w.Ltil D.lev.range : Set w.Ntil), a x = g) ∧
      a w.ttil = fieldExtension F σ ∧
      Nat.card (fixedField F σ) = 2 ^ f' ∧
      (w.Ltil D.lev.range).map a = subfieldGImage (fixedField F σ) ∧
      ∀ y : w.Ntil, (∀ j ∈ w.Ltil D.lev.range, y * j = j * y) → Odd (orderOf y) → y = 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hA.exists_coordinateG
  have : CharP F 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hF
  obtain ⟨-, -, -, -, -, -, hfaith⟩ := hA.layer
  have hJt : ∀ j ∈ w.Ltil D.lev.range, j * w.ttil = w.ttil * j := fun j hj =>
    Subgroup.mem_centralizer_iff.mp (w.ttil_mem_centralizer D) j hj
  obtain ⟨σ, a, hσx, hσ2, hk, ha_inj, haE, haG, haS, hat⟩ :=
    exists_coordinate_field (by omega) hF hfaith e w.orderOf_ttil
      (Subgroup.le_normalClosure : w.Ltil D.lev.range ≤ _) hJt
      (w.exists_Ltil_mul_ne hf hR hW hN D hKc)
  exact ⟨F, inferInstance, inferInstance, inferInstance, σ, a, hF, hσx, hσ2, ha_inj, haE, haG,
    haS, hat, hk, map_eq_subfieldGImage hσ2 hk ha_inj haG hat
      (Subgroup.le_normalClosure : w.Ltil D.lev.range ≤ _) hJt (w.card_Ltil hf hR hW hN D hKc),
    fun y hy hodd => eq_one_of_commute_subfield (by omega) hF hσx hσ2 hk ha_inj haE
      haG hat (Subgroup.le_normalClosure : w.Ltil D.lev.range ≤ _) hJt
      (w.card_Ltil hf hR hW hN D hKc) hy hodd⟩

omit [Finite G] in
theorem map_Ebar_projTil (w : WData d Vi (2 ^ f)) (L : Subgroup G) :
    (w.Ebar L).map w.projTil = normalClosure (w.Ltil L : Set w.Ntil) := by
  rw [Ebar, map_normalClosure _ _ (QuotientGroup.mk'_surjective _), ← coe_map]

omit [Finite G] in
theorem commutator_Ebar [Finite K] [CharP K 2] (hK : 3 ≤ Nat.card K) (w : WData d Vi (2 ^ f))
    (D : LeviData A Vi K) :
    ⁅w.Ebar D.lev.range, w.Ebar D.lev.range⁆ = w.Ebar D.lev.range := by
  have hLperf : ⁅w.Lbar D.lev.range, w.Lbar D.lev.range⁆ = w.Lbar D.lev.range := by
    obtain ⟨μ, hμ⟩ := exists_unit_ne_one (K := K) hK
    have hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ :=
      Matrix.SL2.commutator_eq_top μ.ne_zero (sq_ne_one_of_charTwo hμ)
    rw [← w.range_levBar D, MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, hperf]
  refine le_antisymm (commutator_le_left _ _) (normalClosure_le_normal ?_)
  intro x hx
  have hx' : x ∈ ⁅w.Lbar D.lev.range, w.Lbar D.lev.range⁆ := by rw [hLperf]; exact hx
  exact commutator_mono le_normalClosure le_normalClosure hx'

end CaseA

end WData

structure CaseACoord {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}
    (f : ℕ) (w : WData d Vi (2 ^ f)) (L : Subgroup G) where
  F : Type
  [instField : Field F]
  [instFinite : Finite F]
  [instCharP : CharP F 2]
  card : Nat.card F = 2 ^ (2 * f)
  σ : F ≃+* F
  σ_apply : ∀ x, σ x = x ^ 2 ^ f
  orderOf_σ : orderOf σ = 2
  a : w.Ntil →* Equiv.Perm (Omega F)
  a_injective : Function.Injective a
  a_mem : ∀ x, a x ∈ coordinateE F
  a_layer : ∀ x ∈ normalClosure (w.Ltil L : Set w.Ntil), a x ∈ coordinateG F
  a_layer_onto : ∀ g ∈ coordinateG F, ∃ x ∈ normalClosure (w.Ltil L : Set w.Ntil), a x = g
  a_t : a w.ttil = fieldExtension F σ
  card_fixed : Nat.card (fixedField F σ) = 2 ^ f
  a_Ltil : (w.Ltil L).map a = subfieldGImage (fixedField F σ)
  odd_eq_one : ∀ y : w.Ntil, (∀ j ∈ w.Ltil L, y * j = j * y) → Odd (orderOf y) → y = 1
  ψ : w.Ebar L ≃* Matrix.SpecialLinearGroup (Fin 2) F
  slCoord_ψ : ∀ x : w.Ebar L,
    ((slCoord F (ψ x) : coordinateG F) : Equiv.Perm (Omega F)) = a (w.projTil x)

attribute [instance] CaseACoord.instField CaseACoord.instFinite CaseACoord.instCharP

namespace WData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}
  {f : ℕ} {w : WData d Vi (2 ^ f)} {K : Type} [Field K] [Finite K] {D : LeviData A Vi K}

theorem CaseA.nonempty_coord
    (hf : 3 ≤ f) {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (hKc : Nat.card K = 2 ^ f)
    (hA : w.CaseA f D.lev.range)
    (hO : ⁅standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥) :
    Nonempty (CaseACoord f w D.lev.range) := by
  have : CharP K 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hKc
  have hK3 : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨F, _, _, _, σ, a₀, hF, hσx, hσ2, ha_inj, haE, haG, haS, hat, hk, hLt, hodd⟩ :=
    hA.exists_field hf hR hW hN hKc
  set Eb := w.Ebar D.lev.range with hEb
  have hmapE := map_Ebar_projTil w D.lev.range
  have hmem : ∀ x : Eb, a₀ (w.projTil x) ∈ coordinateG F := fun x =>
    haG _ (hmapE ▸ ⟨x, x.2, rfl⟩)
  let π₀ : Eb →* coordinateG F :=
    { toFun := fun x => ⟨a₀ (w.projTil x), hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  let π : Eb →* Matrix.SpecialLinearGroup (Fin 2) F := (slCoord F).symm.toMonoidHom.comp π₀
  have hπs : Function.Surjective π := by
    intro A'
    obtain ⟨y, hy, hya⟩ := haS _ (slCoord F A').2
    rw [← hmapE] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨⟨x, hx⟩, ?_⟩
    change (slCoord F).symm (π₀ ⟨x, hx⟩) = A'
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hya
  have hker : ∀ x : Eb, π x = 1 → (x : w.Nbar) ∈ standardComponentOddCore w.Nbar := by
    intro x hx
    have h1 : π₀ x = 1 := by
      have := congrArg (slCoord F) hx
      simpa [π] using this
    have h2 : a₀ (w.projTil x) = 1 := congrArg Subtype.val h1
    have h3 : w.projTil x = 1 := ha_inj (by rw [h2, map_one])
    exact (QuotientGroup.eq_one_iff _).mp h3
  have hcen : π.ker ≤ Subgroup.center Eb := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxO := hker x hx
    have h1 : ⁅(x : w.Nbar), (y : w.Nbar)⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hxO y.2
      rw [hO] at this
      exact this
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact Subtype.ext h1.symm
  have hF5 : 5 ≤ Nat.card F := by
    rw [hF]
    calc 5 ≤ 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF9 : Nat.card F ≠ 9 := by
    rw [hF]
    intro h9
    have : 2 ∣ 9 := h9 ▸ dvd_pow_self 2 (by omega)
    omega
  obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_exists_section_of_central
    hF5 hF9 hπs hcen
  have : Group.IsPerfect Eb := by
    constructor
    apply Subgroup.map_injective Eb.subtype_injective
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, commutator_Ebar hK3 w D]
  have hbot := CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section π hcen s hs
  have hπi : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hbot
  let ψ : Eb ≃* Matrix.SpecialLinearGroup (Fin 2) F := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  refine ⟨CaseACoord.mk (F := F) hF σ hσx hσ2 a₀ ha_inj haE haG haS hat hk hLt hodd ψ
    fun x => ?_⟩
  change ((slCoord F ((slCoord F).symm (π₀ x)) : coordinateG F) : Equiv.Perm (Omega F)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

end WData

namespace CaseACoord

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}
  {f : ℕ} {w : WData d Vi (2 ^ f)} {L : Subgroup G} (C : CaseACoord f w L)

instance : (w.Ebar L).Normal := normalClosure_normal

theorem conj_t_mem (x : w.Ebar L) : w.tbar * (x : w.Nbar) * w.tbar⁻¹ ∈ w.Ebar L :=
  (inferInstance : (w.Ebar L).Normal).conj_mem _ x.2 _

theorem slCoord_ψ_coe (x : w.Ebar L) :
    (slCoord C.F (C.ψ x) : Equiv.Perm (Omega C.F)) = C.a (w.projTil x) := C.slCoord_ψ x

theorem ψ_conj_t (x : w.Ebar L) :
    C.ψ ⟨_, conj_t_mem x⟩ = SpecialLinearGroup.map C.σ.toRingHom (C.ψ x) := by
  apply (slCoord C.F).injective
  apply Subtype.ext
  rw [C.slCoord_ψ_coe, ← fieldExtension_conj_slCoord, C.slCoord_ψ_coe, ← C.a_t]
  change C.a (w.projTil (w.tbar * (x : w.Nbar) * w.tbar⁻¹)) = _
  rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]

include C in
theorem eq_one_of_projTil (x : w.Ebar L) (hx : w.projTil (x : w.Nbar) = 1) : x = 1 := by
  apply C.ψ.injective
  apply (slCoord C.F).injective
  apply Subtype.ext
  rw [C.slCoord_ψ_coe, hx, map_one, map_one, map_one]
  rfl

variable {K : Type} [Field K] {D : LeviData A Vi K}

theorem ψ_Lbar_pow (C : CaseACoord f w D.lev.range) {x : w.Nbar}
    (hx : x ∈ w.Lbar D.lev.range) (i j : Fin 2) :
    ((C.ψ ⟨x, le_normalClosure hx⟩ : SpecialLinearGroup (Fin 2) C.F) :
        Matrix (Fin 2) (Fin 2) C.F) i j ^ 2 ^ f =
      (C.ψ ⟨x, le_normalClosure hx⟩ : SpecialLinearGroup (Fin 2) C.F) i j := by
  have ht : w.tbar * x * w.tbar⁻¹ = x := by
    rw [← mem_centralizer_singleton_iff.mp (w.Lbar_le_centralizer D hx), mul_inv_cancel_right]
  have h1 := C.ψ_conj_t ⟨x, le_normalClosure hx⟩
  have h2 : (⟨_, conj_t_mem ⟨x, le_normalClosure hx⟩⟩ : w.Ebar D.lev.range) =
      ⟨x, le_normalClosure hx⟩ := Subtype.ext ht
  rw [h2] at h1
  have h3 := congrArg (fun M : SpecialLinearGroup (Fin 2) C.F =>
    (M : Matrix (Fin 2) (Fin 2) C.F) i j) h1
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, C.σ_apply] at h3
  exact h3.symm

end CaseACoord

namespace WData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}
  {f : ℕ} {w : WData d Vi (2 ^ f)} {K : Type} [Field K] {D : LeviData A Vi K}

theorem tor_mem_N {q : ℕ} (w : WData d Vi q) (D : LeviData A Vi K) (l : Kˣ) : D.tor l ∈ w.N :=
  w.levi_norm ⟨D.tor_mem l, D.tor_mem_normalizer l⟩

end WData

namespace CaseACoord

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}
  {f : ℕ} {w : WData d Vi (2 ^ f)} {K : Type} [Field K] {D : LeviData A Vi K}

theorem projTil_tor [Finite K] (C : CaseACoord f w D.lev.range) (hKc : Nat.card K = 2 ^ f)
    (l : Kˣ) :
    w.projTil (w.projBar ⟨D.tor l, w.tor_mem_N D l⟩) = 1 := by
  apply C.odd_eq_one
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨B, hB⟩ := mem_subgroupOf.mp hz
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    change D.tor l * (z : G) = (z : G) * D.tor l
    rw [← hB]
    exact D.tor_comm l B
  · have h1 : orderOf l ∣ 2 ^ f - 1 := by
      have := orderOf_dvd_natCard l
      rwa [Nat.card_units, hKc] at this
    have h2 : orderOf (⟨D.tor l, w.tor_mem_N D l⟩ : w.N) ∣ orderOf l := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have h3 : orderOf (w.projTil (w.projBar ⟨D.tor l, w.tor_mem_N D l⟩)) ∣
        orderOf (⟨D.tor l, w.tor_mem_N D l⟩ : w.N) :=
      (orderOf_map_dvd _ _).trans (orderOf_map_dvd _ _)
    have hf1 : f ≠ 0 := by
      rintro rfl
      have h0 := Finite.one_lt_card (α := K)
      rw [hKc, pow_zero] at h0
      exact lt_irrefl _ h0
    have hodd : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' hf1).mpr even_two) odd_one
    exact hodd.of_dvd_nat (h3.trans (h2.trans h1))

end CaseACoord

end CFSG.LocalAnalysis.EvenBN.LinearThree
