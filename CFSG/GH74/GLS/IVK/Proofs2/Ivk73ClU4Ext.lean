module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Pair
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorULinear

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup Module Matrix CFSG.ComponentClassification.RestrictedStd
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OddClassSelector
open CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

theorem mem_eigenPlus_iff' {l : E} (hl : l ≠ 0) {A : Module.End E V} {v : V} :
    v ∈ eigenPlus l A ↔ A v = l • v := by
  unfold eigenPlus
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  unfold invSMulOp
  rw [LinearMap.smul_apply, inv_smul_eq_iff₀ hl]

theorem mem_eigenMinus_iff' {l : E} (hl : l ≠ 0) {A : Module.End E V} {v : V} :
    v ∈ eigenMinus l A ↔ A v = -(l • v) := by
  unfold eigenMinus
  rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]
  unfold invSMulOp
  rw [LinearMap.smul_apply, inv_smul_eq_iff₀ hl, smul_neg]

variable [FiniteDimensional E V]

theorem su4_linear_paired (h : UnitaryFieldData p f E) (hp : p ≠ 2) (hn : finrank E V = 4)
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {T : sesqUnitaryGroup B} (hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2)
    {Y : Subgroup (sesqUnitaryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (centralizer ({T} : Set (sesqUnitaryGroup B))))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y)
    (hker : ∀ y : Y, σ y = 1 → (y : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B)
    (hs : SmallSource X) : ∃ P : PairedSL h B Y, P.T = T := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  obtain ⟨l, hl0, hAA, hN, hP, hM, hc, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp (by omega) hB hBl hT
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY : Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))) ≃* Y :=
    Subgroup.subgroupOfEquivOfLe hY.1
  rcases hN with hN | hN
  ·
    exfalso
    have hσ₁k := ker_comp_le_center eY.toMonoidHom eY.injective σ hσk
    obtain ⟨-, hsepP, hsepM, e, he⟩ := hsplit hN
    have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
      ⟨fun x y => hB.eq (x : V) (y : V)⟩
    rcases fst_eq_or_snd_eq_of_isComponent_prod (isComponent_map_of_isComponent e hY₁) with
      h2 | h1
    · have h2' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))),
          (e x).2 = 1 := fun x hx => h2 _ (mem_map_of_mem _ hx)
      obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := restrict_component e hY₁ h2'
      have hYF : ∀ y ∈ Y, ∀ w ∈ eigenMinus l (unitaryOp T), unitaryOp y w = w := by
        intro y hy w hw
        have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).2 ⟨w, hw⟩
        rw [h2' _ (eY.symm ⟨y, hy⟩).2] at h4
        exact h4.symm
      refine su_half_false h hp (hsymm _) hsepP (Submodule.one_le_finrank_iff.mpr hP) hM hYF
        (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ σ hσs hσk hker hs
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
    · have h1' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))),
          ((e.trans MulEquiv.prodComm) x).2 = 1 := fun x hx => h1 _ (mem_map_of_mem _ hx)
      obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := restrict_component (e.trans MulEquiv.prodComm) hY₁ h1'
      have hYF : ∀ y ∈ Y, ∀ w ∈ eigenPlus l (unitaryOp T), unitaryOp y w = w := by
        intro y hy w hw
        have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).1 ⟨w, hw⟩
        rw [show (e (eY.symm ⟨y, hy⟩)).1 = 1 from h1' _ (eY.symm ⟨y, hy⟩).2] at h4
        exact h4.symm
      refine su_half_false h hp (hsymm _) hsepM (Submodule.one_le_finrank_iff.mpr hM) hP hYF
        (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ σ hσs hσk hker hs
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
  ·
    obtain ⟨hisoP, -, -, hdim2, -, hpairM, e, hecompat, -, -⟩ := hpaired hN
    have hfin2 : finrank E (eigenPlus l (unitaryOp T)) = 2 := by omega
    let bP : Basis (Fin 2) E (eigenPlus l (unitaryOp T)) := Module.finBasisOfFinrankEq E _ hfin2
    let e' : centralizer ({T} : Set (sesqUnitaryGroup B)) ≃* Matrix.GeneralLinearGroup (Fin 2) E :=
      e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv)
    have hL' := isComponent_map_of_isComponent e' hY₁
    have : Group.IsPerfect ((Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B)))).map
        e'.toMonoidHom) := hL'.1.1
    have : Nontrivial ((Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B)))).map
        e'.toMonoidHom) := CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
    have hcard : Nat.card E = p ^ (2 * f) := h.card
    have hp3 : 3 ≤ p := by
      have := h.prime.two_le
      omega
    have hq : 9 ≤ Nat.card E := by
      rw [hcard]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
        _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right h.prime.pos (by have := h.one_le; omega)
    have hSL : (Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B)))).map e'.toMonoidHom =
        CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinearRange 2 E :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange
        2 E (by norm_num) (Or.inr (by omega)) (Or.inr (by omega)) _ hL'.2
    refine ⟨{
      T := T
      l := l
      l_ne := hl0
      norm_l := hN
      Vp := eigenPlus l (unitaryOp T)
      Vm := eigenMinus l (unitaryOp T)
      isCompl := hc
      Vm_ne := hM
      T_p := fun v hv => (mem_eigenPlus_iff' hl0).1 hv
      T_m := fun v hv => (mem_eigenMinus_iff' hl0).1 hv
      iso_p := hisoP
      pair_m := hpairM
      cp := bP.equivFun
      surj := ?_ }, rfl⟩
    intro g₀
    have h1 : Matrix.SpecialLinearGroup.toGL g₀ ∈
        (Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B)))).map e'.toMonoidHom := by
      rw [hSL]
      exact ⟨g₀, rfl⟩
    obtain ⟨x, hx, hxg⟩ := h1
    refine ⟨((x : centralizer ({T} : Set (sesqUnitaryGroup B))) : sesqUnitaryGroup B),
      Subgroup.mem_subgroupOf.mp hx, fun u => ?_⟩
    have hmat : LinearMap.toMatrix bP bP
        (((e x : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
          Module.End E (eigenPlus l (unitaryOp T)))) = (g₀ : Matrix (Fin 2) (Fin 2) E) := by
      have := congrArg (fun z : Matrix.GeneralLinearGroup (Fin 2) E => (z : Matrix (Fin 2) (Fin 2) E)) hxg
      exact this
    have hrepr : ∀ v : eigenPlus l (unitaryOp T),
        bP.equivFun (((e x : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
          Module.End E (eigenPlus l (unitaryOp T))) v) =
          (g₀ : Matrix (Fin 2) (Fin 2) E) *ᵥ bP.equivFun v := by
      intro v
      rw [Basis.equivFun_apply, Basis.equivFun_apply, ← hmat]
      exact (LinearMap.toMatrix_mulVec_repr bP bP _ v).symm
    have h2 : ((e x : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
        Module.End E (eigenPlus l (unitaryOp T))) (bP.equivFun.symm u) =
          bP.equivFun.symm ((g₀ : Matrix (Fin 2) (Fin 2) E) *ᵥ u) := by
      apply bP.equivFun.injective
      rw [hrepr, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have h3 := LinearMap.congr_fun (hecompat x) (bP.equivFun.symm u)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h2] at h3
    exact h3

end CFSG.GH74.GLS.IVK
