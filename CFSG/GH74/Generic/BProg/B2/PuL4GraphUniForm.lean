module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUAnti
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUMat

public section

namespace CFSG.GH74.Generic.BProg.B2

open Subgroup Module CFSG CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

namespace PuL4GraphUniForm

theorem sp_component_cover {k : Type} [Field k] [Finite k] {W : Type} [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {ℓ j : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hk : Nat.card k = ℓ ^ j) (B : BilinForm k W) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hdim : finrank k W = 4) {H : Type*} [Group H]
    (F : H ≃* CatalogueBAlternatingIsometry.isometryGroup B) {Y : Subgroup H}
    (hY : CFSG.IsComponent Y) {X : Type} [Group X] (σ : Y →* X) (hσk : σ.ker ≤ center Y) :
    ∃ ρ : StatedSp 2 k →* X, ρ.ker ≤ center (StatedSp 2 k) ∧
      (Function.Surjective σ → Function.Surjective ρ) := by
  classical
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have hq := CatalogueBAlternatingIsometry.isometry_quasisimple_of_four_le B hB hnd (by omega) hodd
  have hYtop := OddClassSelector.eq_top_of_isComponent_of_quasisimple hq
    (isComponent_map_of_isComponent F hY)
  obtain ⟨m, hd, ⟨eSp⟩⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B hB hnd
  have heq := CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := m) (K := k)
  let τ : StatedSp m k ≃* Y :=
    (((MulEquiv.subgroupCongr heq).trans eSp.symm).trans
      ((MulEquiv.subgroupCongr hYtop).trans Subgroup.topEquiv).symm).trans
        (Y.equivMapOfInjective F.toMonoidHom F.injective).symm
  have hm : m = 2 := by omega
  subst hm
  exact ⟨σ.comp τ.toMonoidHom, OddClassSelector.ker_comp_le_center τ.toMonoidHom τ.injective σ hσk,
    fun hs => hs.comp τ.surjective⟩

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.ComponentClassification.RestrictedStd
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  CFSG.ComponentClassification.GSThmB.Catalog7L4EU CFSG.LinearGroups Matrix
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem uni_anti_cases (hp : p ≠ 2) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1) {z : K}
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = z • 1)
    {Y : Subgroup (sesqUnitaryGroup (stdHermForm h 4))}
    (hY : CFSG.Assembly.IsComponentOf Y (fixedSubgroup (antiConjA h hAu)))
    {X : Type} [Group X] (σ : Y →* X) (hσs : Function.Surjective σ) (hσk : σ.ker ≤ center Y) :
    (5 ≤ Nat.card h.fixedField ∧
      Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField)) ∨
    (∃ (E' : Type) (_ : Field E') (_ : Finite E'), Nat.card E' = Nat.card h.fixedField ^ 2 ∧
      Nonempty (X ≃* GorensteinWalter.PSL2 E')) ∨
    (∃ ρ : StatedSp 2 h.fixedField →* X, ρ.ker ≤ center (StatedSp 2 h.fixedField)) := by
  classical
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have : Finite K := h.finite
  have : CharP K p := h.charP
  have hK : Nat.card h.fixedField = p ^ f := h.card_fixedField
  have hKodd : Odd (Nat.card h.fixedField) := by rw [hK]; exact hodd.pow
  have hτ₀ := CatFactsL4U4.StabU.antiunitaryMap_bijective h A
  have hτ₀B := CatFactsL4U4.StabU.stdHermForm_antiunitaryMap h hAu
  have hz0 : z ≠ 0 := by
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
      (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) v) = ((Units.mk0 z hz0 : Kˣ) : K) • v :=
    CatFactsL4U4.StabU.antiunitaryMap_sq h _ hAA
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by rw [Module.finrank_fin_fun]; norm_num) (stdHermForm_isSymm h 4)
    (stdHermForm_separatingLeft h 4) _ hτ₀ hτ₀B (Units.mk0 z hz0) hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField
      (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))) :=
    finite_conjFixed
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY := Subgroup.subgroupOfEquivOfLe hY.1
  have hσ₁k := OddClassSelector.ker_comp_le_center eY.toMonoidHom eY.injective σ hσk
  have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
    have h1 := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at h1
    exact two_ne_zero_of_odd h hp h1
  have : Group.IsPerfect Y := ⟨hY.2.2.1⟩
  rcases hμ1 with hμ1 | hμ1
  swap
  ·
    right; right
    obtain ⟨B', -, halt, hnd, -, Φ, -⟩ := hB2 hμ1
    obtain ⟨ρ, hρk, -⟩ := sp_component_cover h.prime hp hK B' halt hnd
      (by rw [hfinW, Module.finrank_fin_fun])
      ((fixedCommutingEquiv h _ hτ₀ hτ₀B).trans Φ) hY₁ (σ.comp eY.toMonoidHom) hσ₁k
    exact ⟨ρ, hρk⟩
  obtain ⟨B', hB'v, hsym, hnd, Φ, -⟩ := hB1 hμ1
  have hQ' : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
    rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
    exact hnd
  have hdim : Module.finrank h.fixedField
      (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))) = 4 := by
    rw [hfinW, Module.finrank_fin_fun]
  let Φ' : fixedSubgroup (antiConjA h hAu) ≃*
      TauCeti.QuadraticMap.orthogonalGroup (CatalogueBOrthogonalDescent.originalQuadratic B') :=
    (fixedCommutingEquiv h _ hτ₀ hτ₀B).trans
      (Φ.trans (MulEquiv.subgroupCongr (isometryGroup_eq_orthogonalGroup B' hsym h2)))
  have hY' := isComponent_map_of_isComponent Φ' hY₁
  let eYY' : Y ≃* (Y.subgroupOf (fixedSubgroup (antiConjA h hAu))).map Φ'.toMonoidHom :=
    eY.symm.trans ((Y.subgroupOf _).equivMapOfInjective _ Φ'.injective)
  by_cases hsplit : ∃ S : Submodule h.fixedField
      (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))),
      Module.finrank h.fixedField S = 2 ∧
        ∀ x ∈ S, CatalogueBOrthogonalDescent.originalQuadratic B' x = 0
  · left
    obtain ⟨hq5, ⟨eSL⟩⟩ := component_equiv_sl_of_split _ hQ' hKodd hdim hsplit hY'
    exact ⟨hq5, ⟨eYY'.trans eSL⟩⟩
  · right; left
    obtain ⟨hquasi, E', _, _, hE', ⟨eC⟩⟩ :=
      commutator_equiv_psl_of_nonsplit _ hQ' hKodd hdim hsplit
    have hYeq := LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hY' hquasi
    have h3K : 3 ≤ Nat.card h.fixedField := by
      rw [hK]
      have h3p : 3 ≤ p := by have := h.prime.two_le; omega
      exact h3p.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
    have h3 : 3 < Nat.card E' := by rw [hE']; nlinarith
    let eYP : Y ≃* GorensteinWalter.PSL2 E' :=
      (eYY'.trans (MulEquiv.subgroupCongr hYeq)).trans eC
    have hZ : center Y = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      exact (mem_bot).mpr (OddSelector.Catalog7L3.eq_one_of_mem_center_psl2 h3 eYP hw)
    have hinj : Function.Injective σ :=
      (MonoidHom.ker_eq_bot_iff σ).mp (le_bot_iff.mp (hσk.trans hZ.le))
    exact ⟨E', inferInstance, inferInstance, hE',
      ⟨(MulEquiv.ofBijective σ ⟨hinj, hσs⟩).symm.trans eYP⟩⟩

end PuL4GraphUniForm

end CFSG.GH74.Generic.BProg.B2
