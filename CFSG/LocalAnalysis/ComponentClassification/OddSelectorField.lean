module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSL
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem false_of_not_small_source {X : Type} [Group X]
    (hX : (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel X .PSL 2 p f) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧ ¬ StatedClassicalModel X .PSL 3 2 2)
    {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel X .PSL 2 p f ∨ Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel X .PSL 3 2 2) : False := by
  rcases hsrc with h | h | h
  · exact hX.1 p f hp2 h
  · exact not_nonempty_iff.mpr hX.2.1 h
  · exact hX.2.2 h

theorem finite_mulAut_projectiveSL {k : Type*} [Field k] [Finite k] (m : ℕ) :
    Finite (MulAut (projectiveSL m k)) :=
  Finite.of_injective (fun χ : MulAut (projectiveSL m k) => (χ : projectiveSL m k → _))
    (fun _ _ h => MulEquiv.ext (congrFun h))

theorem map_conj_inv_map_conj {G : Type*} [Group G] (χ : G) (X : Subgroup G) :
    (X.map (MulAut.conj χ⁻¹).toMonoidHom).map (MulAut.conj χ).toMonoidHom = X := by
  rw [Subgroup.map_map]
  have hid : (MulAut.conj χ).toMonoidHom.comp (MulAut.conj χ⁻¹).toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
  rw [hid, Subgroup.map_id]

variable {A : Type} [Group A] {a : A} {L : Subgroup A}

theorem field_case_false (ha : orderOf a = 2) {m ℓ e : ℕ} (hm : 3 ≤ m) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ e)
    {ρ : A →* MulAut (projectiveSL m k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (inner (projectiveSL m k) ⊓ centralizer {ρ a}))
    {B : GL (Fin m) k} {σ : k ≃+* k} (hσ : σ ≠ 1)
    (hρa : ρ a = conjAut m k B * fieldAut m k σ) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have hα2 : (conjAut m k B * fieldAut m k σ) ^ 2 = 1 := by
    rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨heven, hσx, H, hH⟩ := linear_field_involution_descent hℓ he hk hm B σ hσ hα2
  have hρa' : ρ a = conjAut m k H * fieldAut m k σ * (conjAut m k H)⁻¹ := hρa.trans hH
  obtain ⟨-, ⟨e₁, -⟩, hNinn, -, hNC, hNnormal, hCN⟩ :=
    linear_quadratic_field_full_centralizer_rigidity σ (n := m) hm
  set χ := conjAut m k H with hχ
  set β := fieldAut m k σ with hβ
  set N := (subfieldConj m σ).range with hNdef
  have hY : (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a}).map
      (MulAut.conj χ⁻¹).toMonoidHom =
        OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {β} := by
    rw [map_conj_inner_inf_centralizer, hρa']
    congr 3
    group
  set L₀ := (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom with hL₀def
  have hL₀ : CFSG.Assembly.IsComponentOf L₀
      (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {β}) := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [hY] at this
  have := finite_mulAut_projectiveSL (k := k) m
  have hL₀N : CFSG.Assembly.IsComponentOf L₀ N := by
    refine isComponentOf_of_normal_of_comm (le_inf hNinn hNC)
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNC hNnormal hy.2) ?_ hL₀
    intro x _ hx y _ hy
    rw [hCN] at hx hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self β i j).eq
  have : IsSimpleGroup (projectiveSL m (fixedField k σ)) := isSimpleGroup_projectiveSL hm
  have hNsimple : IsSimpleGroup N := e₁.symm.isSimpleGroup
  have hL₀eq : L₀ = N := eq_of_isComponentOf_simple hNsimple hL₀N
  have hLimg : L.map ρ = N.map (MulAut.conj χ).toMonoidHom := by
    rw [← hL₀eq, hL₀def, map_conj_inv_map_conj]
  have eL : L ≃* projectiveSL m (fixedField k σ) :=
    ((L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hLimg).trans
      ((N.equivMapOfInjective _ (MulAut.conj χ).injective).symm))).trans e₁.symm
  have hσσ : σ ^ 2 = 1 := RingEquiv.ext fun x => by
    have := Fintype.ofFinite k
    rw [pow_two, RingAut.mul_apply, hσx, hσx, ← pow_mul, ← pow_add,
      show e / 2 + e / 2 = e by obtain ⟨r, hr⟩ := heven; omega, ← hk, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
    rfl
  have hk₀ : Nat.card (fixedField k σ) = ℓ ^ (e / 2) := by
    have h1 := fixedField_card_square k σ hσσ hσ
    rw [hk, show e = 2 * (e / 2) by obtain ⟨r, hr⟩ := heven; omega, pow_mul'] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  have hg : 1 ≤ e / 2 := by obtain ⟨r, hr⟩ := heven; omega
  set σ' : SpecialLinearGroup (Fin m) (fixedField k σ) →* L :=
    eL.symm.toMonoidHom.comp (proj m (fixedField k σ)) with hσ'
  have hker : σ'.ker ≤ center (SpecialLinearGroup (Fin m) (fixedField k σ)) := by
    intro x hx
    have hx' : proj m (fixedField k σ) x = 1 := by
      have h1 : eL.symm (proj m (fixedField k σ) x) = 1 := hx
      rwa [MulEquiv.map_eq_one_iff] at h1
    rw [← scalars_eq_center]
    exact proj_eq_one_iff.mp hx'
  exact false_of_not_small_source
    (not_small_source_of_sl_cover hm hℓ hℓ2 hg hk₀ σ' hker) hp2 hsrc

end CFSG.ComponentClassification.OddSelector
