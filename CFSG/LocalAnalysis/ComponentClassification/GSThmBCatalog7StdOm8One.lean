module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedConjugation
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Fac

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed (scalarSigns)

@[expose] def prodBotEquiv {X Y : Type*} [Group X] [Group Y] (L : Subgroup X) :
    L.prod (⊥ : Subgroup Y) ≃* L where
  toFun z := ⟨z.val.1, z.property.1⟩
  invFun l := ⟨(l.val, 1), l.property, Subgroup.one_mem _⟩
  left_inv z := Subtype.ext (Prod.ext rfl (Subgroup.mem_bot.mp z.property.2).symm)
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] def equivOfMapEq {A X Y : Type*} [Group A] [Group X] [Group Y] (ψ : A ≃* X × Y)
    {N : Subgroup A} {L : Subgroup X} (h : N.map ψ.toMonoidHom = L.prod ⊥) : N ≃* L :=
  ((N.equivMapOfInjective ψ.toMonoidHom ψ.injective).trans (MulEquiv.subgroupCongr h)).trans
    (prodBotEquiv L)

@[expose] def centerQuotientCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ center A ≃* B ⧸ center B :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {W W' : Submodule K V}
  {C : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)}
  (ψ : C ≃* TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) ×
    TauCeti.QuadraticMap.orthogonalGroup (Q.comp W'.subtype))
  (hψ : ∀ h (x : W) (y : W'), (ψ.symm h).val.val (x.val + y.val) =
    (h.1.val x).val + (h.2.val y).val)

omit [Finite K] [FiniteDimensional K V] in
include hψ in
theorem ext_left (h) (x : W) : (ψ.symm h).val.val x.val = (h.1.val x).val := by
  have := hψ h x 0
  simpa using this

omit [Finite K] [FiniteDimensional K V] in
include hψ in
theorem ext_right (h) (y : W') : (ψ.symm h).val.val y.val = (h.2.val y).val := by
  have := hψ h 0 y
  simpa using this

omit [Finite K] [FiniteDimensional K V] in
theorem polar_comp_subtype (x y : W) :
    polar (Q.comp W.subtype) x y = polar Q x.val y.val := rfl

omit [Finite K] [FiniteDimensional K V] in
theorem reflect_pair_apply {e₀ e₁ : W} (h₀ : (Q.comp W.subtype) e₀ = 1)
    (h₁ : (Q.comp W.subtype) e₁ = 1) (h₀₁ : polar (Q.comp W.subtype) e₀ e₁ = 0) (x : W) :
    (reflect (Q.comp W.subtype) e₀ * reflect (Q.comp W.subtype) e₁) x =
      x - polar (Q.comp W.subtype) e₀ x • e₀ - polar (Q.comp W.subtype) e₁ x • e₁ := by
  rw [LinearEquiv.mul_apply, reflect_apply (by rw [h₀]; exact one_ne_zero),
    reflect_apply (by rw [h₁]; exact one_ne_zero), h₀, h₁, div_one, div_one,
    polar_sub_right, polar_smul_right, h₀₁, smul_zero, sub_zero]
  abel

omit [Finite K] [FiniteDimensional K V] in
theorem reflect_pair_apply_left {e₀ e₁ : W} (h₀ : (Q.comp W.subtype) e₀ = 1)
    (h₁ : (Q.comp W.subtype) e₁ = 1) (h₀₁ : polar (Q.comp W.subtype) e₀ e₁ = 0) :
    (reflect (Q.comp W.subtype) e₀ * reflect (Q.comp W.subtype) e₁) e₀ = -e₀ := by
  rw [reflect_pair_apply h₀ h₁ h₀₁, OddClassSelector.polar_self_eq, h₀,
    polar_comm, h₀₁, zero_smul, sub_zero, mul_one, two_smul]
  abel

omit [Finite K] [FiniteDimensional K V] in
theorem reflect_pair_apply_right {e₀ e₁ : W} (h₀ : (Q.comp W.subtype) e₀ = 1)
    (h₁ : (Q.comp W.subtype) e₁ = 1) (h₀₁ : polar (Q.comp W.subtype) e₀ e₁ = 0) :
    (reflect (Q.comp W.subtype) e₀ * reflect (Q.comp W.subtype) e₁) e₁ = -e₁ := by
  rw [reflect_pair_apply h₀ h₁ h₀₁, OddClassSelector.polar_self_eq, h₁, h₀₁, zero_smul,
    sub_zero, mul_one, two_smul]
  abel

omit [Finite K] [FiniteDimensional K V] in
theorem reflect_pair_apply_fix {e₀ e₁ x : W} (h₀ : (Q.comp W.subtype) e₀ = 1)
    (h₁ : (Q.comp W.subtype) e₁ = 1) (h₀₁ : polar (Q.comp W.subtype) e₀ e₁ = 0)
    (hx₀ : polar (Q.comp W.subtype) e₀ x = 0) (hx₁ : polar (Q.comp W.subtype) e₁ x = 0) :
    (reflect (Q.comp W.subtype) e₀ * reflect (Q.comp W.subtype) e₁) x = x := by
  rw [reflect_pair_apply h₀ h₁ h₀₁, hx₀, hx₁, zero_smul, zero_smul, sub_zero, sub_zero]

@[expose] def reflectPair (e₀ e₁ : W) :
    TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) :=
  ⟨reflect (Q.comp W.subtype) e₀ * reflect (Q.comp W.subtype) e₁,
    mul_mem (reflect_mem_orthogonalGroup _ e₀) (reflect_mem_orthogonalGroup _ e₁)⟩

omit [Finite K] [FiniteDimensional K V] in
theorem reflectPair_val (e₀ e₁ : W) :
    (reflectPair (Q := Q) e₀ e₁).val = reflect (Q.comp W.subtype) e₀ *
      reflect (Q.comp W.subtype) e₁ := rfl

include hψ in
theorem false_of_commuting (hodd : Odd (Nat.card K))
    (hW : (Q.comp W.subtype).polarBilin.Nondegenerate)
    (hcompl : IsCompl W W') (hdW : 4 ≤ finrank K W) (B' : V →ₗ[K] V) {lam : K}
    (hns : ¬ IsSquare lam) (hB'2 : ∀ v, B' (B' v) = lam • v)
    (hcomm : ∀ h : TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype),
      h ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype)) →
        ∀ v, (ψ.symm (h, 1)).val.val (B' v) = B' ((ψ.symm (h, 1)).val.val v)) : False := by
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨e, he, hQe⟩ := exists_unit_orthogonal_basis hodd hW (by omega)
  set i₀ : Fin (finrank K W) := ⟨0, by omega⟩
  set i₁ : Fin (finrank K W) := ⟨1, by omega⟩
  set i₂ : Fin (finrank K W) := ⟨2, by omega⟩
  have hQ₀ : (Q.comp W.subtype) (e i₀) = 1 := hQe i₀ (by simp [i₀]; omega)
  have hQ₁ : (Q.comp W.subtype) (e i₁) = 1 := hQe i₁ (by simp [i₁]; omega)
  have hQ₂ : (Q.comp W.subtype) (e i₂) = 1 := hQe i₂ (by simp [i₂]; omega)
  have h01 : polar (Q.comp W.subtype) (e i₀) (e i₁) = 0 :=
    he _ _ (by simp [i₀, i₁, Fin.ext_iff])
  have h02 : polar (Q.comp W.subtype) (e i₀) (e i₂) = 0 :=
    he _ _ (by simp [i₀, i₂, Fin.ext_iff])
  have h12 : polar (Q.comp W.subtype) (e i₁) (e i₂) = 0 :=
    he _ _ (by simp [i₁, i₂, Fin.ext_iff])
  set t₁ := reflectPair (Q := Q) (e i₀) (e i₁)
  set t₂ := reflectPair (Q := Q) (e i₀) (e i₂)
  have ht₁ : t₁ ∈ commutator _ := reflect_mul_reflect_mem_commutator h2 hQ₀ hQ₁
  have ht₂ : t₂ ∈ commutator _ := reflect_mul_reflect_mem_commutator h2 hQ₀ hQ₂
  set v₀ : V := (e i₀).val
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ W, ∃ y ∈ W', x + y = B' v₀ :=
    Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top)
  have hstep : ∀ (t : TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype)),
      t ∈ commutator _ → t.val (e i₀) = -(e i₀) →
      (t.val ⟨x, hx⟩ : V) = -x ∧ y = 0 := by
    intro t ht htv
    have h1 := hcomm t ht v₀
    have hg0 : (ψ.symm (t, 1)).val.val v₀ = -v₀ := by
      rw [ext_left ψ hψ (t, 1) (e i₀)]
      change ((t.val (e i₀) : W) : V) = _
      rw [htv]
      rfl
    rw [hg0, map_neg, ← hxy] at h1
    have hg1 : (ψ.symm (t, 1)).val.val (x + y) = (t.val ⟨x, hx⟩ : V) + y := by
      have := hψ (t, 1) ⟨x, hx⟩ ⟨y, hy⟩
      rw [this]
      rfl
    rw [hg1] at h1
    have hsum : ((t.val ⟨x, hx⟩ : V) + x) + (y + y) = 0 := by
      rw [show ((t.val ⟨x, hx⟩ : V) + x) + (y + y) =
        ((t.val ⟨x, hx⟩ : V) + y) + (x + y) by abel, h1]
      abel
    have hW1 : (t.val ⟨x, hx⟩ : V) + x ∈ W := W.add_mem (t.val ⟨x, hx⟩).property hx
    have hW2 : y + y ∈ W' := W'.add_mem hy hy
    have hdis : (t.val ⟨x, hx⟩ : V) + x ∈ W ⊓ W' := ⟨hW1, by
      rw [show (t.val ⟨x, hx⟩ : V) + x = -(y + y) from eq_neg_of_add_eq_zero_left hsum]
      exact W'.neg_mem hW2⟩
    rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hdis
    have hyy : y + y = 0 := by rw [← hsum, hdis, zero_add]
    refine ⟨eq_neg_of_add_eq_zero_left hdis, ?_⟩
    have : (2 : K) • y = 0 := by rw [two_smul]; exact hyy
    exact (smul_eq_zero.mp this).resolve_left h2
  obtain ⟨hx₁, hy0⟩ := hstep t₁ ht₁ (reflect_pair_apply_left hQ₀ hQ₁ h01)
  obtain ⟨hx₂, -⟩ := hstep t₂ ht₂ (reflect_pair_apply_left hQ₀ hQ₂ h02)
  set xW : W := ⟨x, hx⟩
  have hf₁ := reflect_pair_apply hQ₀ hQ₁ h01 xW
  have hf₂ := reflect_pair_apply hQ₀ hQ₂ h02 xW
  have hx₁' : t₁.val xW = -xW := Subtype.ext hx₁
  have hx₂' : t₂.val xW = -xW := Subtype.ext hx₂
  rw [← reflectPair_val, hx₁'] at hf₁
  rw [← reflectPair_val, hx₂'] at hf₂
  have hdiff : polar (Q.comp W.subtype) (e i₁) xW • e i₁ =
      polar (Q.comp W.subtype) (e i₂) xW • e i₂ := by
    have := hf₁.symm.trans hf₂
    have h3 : xW - polar (Q.comp W.subtype) (e i₀) xW • e i₀ -
        polar (Q.comp W.subtype) (e i₁) xW • e i₁ =
        xW - polar (Q.comp W.subtype) (e i₀) xW • e i₀ -
        polar (Q.comp W.subtype) (e i₂) xW • e i₂ := this
    exact sub_right_injective h3
  have hc₁ : polar (Q.comp W.subtype) (e i₁) xW = 0 := by
    have := congrArg (polar (Q.comp W.subtype) (e i₁)) hdiff
    rw [polar_smul_right, polar_smul_right, OddClassSelector.polar_self_eq, hQ₁, h12,
      smul_zero, mul_one, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_right h2
  rw [hc₁, zero_smul, sub_zero] at hf₁
  have hxe : (2 : K) • xW = polar (Q.comp W.subtype) (e i₀) xW • e i₀ := by
    rw [two_smul]
    exact (neg_add_eq_iff_eq_add.mp (eq_sub_iff_add_eq.mp hf₁)).symm
  set β := polar (Q.comp W.subtype) (e i₀) xW / 2
  have hBv : B' v₀ = β • v₀ := by
    rw [← hxy, hy0, add_zero]
    have h1 : xW = β • e i₀ := by
      apply smul_right_injective W h2
      change (2 : K) • xW = (2 : K) • (β • e i₀)
      rw [hxe, smul_smul, mul_div_cancel₀ _ h2]
    exact congrArg Subtype.val h1
  apply hns
  refine ⟨β, ?_⟩
  have hv0 : v₀ ≠ 0 := fun h => e.ne_zero i₀ (Subtype.ext h)
  have h1 := hB'2 v₀
  rw [hBv, map_smul, hBv, smul_smul] at h1
  exact (smul_left_injective K hv0 h1).symm

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
