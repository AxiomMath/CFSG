module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedConjugation
public import CFSG.ClassicalGroups.Orthogonal.Derived

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

section Klein

variable {G : Type*} [Group G]

theorem pow_val_add' {x : G} (hx : x * x = 1) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hv0 : (0 : ZMod 2).val = 0 := rfl
  have hv1 : (1 : ZMod 2).val = 1 := rfl
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl
  · rw [add_zero, hv0, pow_zero, one_mul]
  · rw [zero_add, hv0, pow_zero, one_mul]
  · rw [add_zero, hv0, pow_zero, mul_one]
  · rw [h11, hv0, hv1, pow_zero, pow_one, hx]

@[expose] def kleinHom (x y : G) (hx : x * x = 1) (hy : y * y = 1) (hxy : Commute x y) :
    Multiplicative (ZMod 2 × ZMod 2) →* G where
  toFun v := x ^ (Multiplicative.toAdd v).1.val * y ^ (Multiplicative.toAdd v).2.val
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, pow_val_add' hx, pow_val_add' hy,
      mul_assoc]
    congr 1
    exact (hxy.pow_pow _ _).left_comm _

theorem four_dvd_card_of_klein [Finite G] (H : Subgroup G) {x y : G} (hxH : x ∈ H) (hyH : y ∈ H)
    (hx : x * x = 1) (hy : y * y = 1) (hxy : Commute x y) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hne : x ≠ y) : 4 ∣ Nat.card H := by
  set φ := kleinHom x y hx hy hxy
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hv0 : (0 : ZMod 2).val = 0 := rfl
  have hv1 : (1 : ZMod 2).val = 1 := rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    obtain ⟨⟨a, b⟩, rfl⟩ := Multiplicative.ofAdd.surjective v
    change x ^ a.val * y ^ b.val = 1 at hv
    rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl
    · rfl
    · rw [hv0, hv1, pow_zero, pow_one, one_mul] at hv
      exact absurd hv hy1
    · rw [hv0, hv1, pow_zero, pow_one, mul_one] at hv
      exact absurd hv hx1
    · rw [hv1, pow_one, pow_one] at hv
      exact absurd (show x = y by rw [← mul_one x, ← hy, ← mul_assoc, hv, one_mul]) hne
  have hle : φ.range ≤ H := by
    rintro _ ⟨v, rfl⟩
    exact mul_mem (pow_mem hxH _) (pow_mem hyH _)
  have hcard : Nat.card φ.range = 4 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd]
    simp
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

end Klein

section Image

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {L : Type*} [Group L] (Θ : L ≃* projectiveDerived Q)
  {F : Type*} [Group F] (hF : commutator F = ⊤)
  (f : F →* TauCeti.QuadraticMap.orthogonalGroup Q)

include hF in
theorem mem_omega (a : F) : f a ∈ orthogonalDerived Q := by
  have h : f a ∈ (⊤ : Subgroup F).map f := ⟨a, mem_top a, rfl⟩
  rw [← hF, commutator_def, Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono le_top le_top h

@[expose] def toOmega : F →* orthogonalDerived Q := f.codRestrict _ (mem_omega hF f)

theorem toOmega_val (a : F) : (toOmega hF f a).val = f a := rfl

@[expose] def toL : F →* L :=
  Θ.symm.toMonoidHom.comp
    ((QuotientGroup.mk' ((scalarSigns Q).subgroupOf (orthogonalDerived Q))).comp (toOmega hF f))

theorem toL_apply (a : F) :
    toL Θ hF f a = Θ.symm (QuotientGroup.mk' _ (toOmega hF f a)) := rfl

abbrev imgL : Subgroup L := (toL Θ hF f).range

theorem mem_imgL_of_theta {l : L} {a : F}
    (h : Θ l = QuotientGroup.mk' ((scalarSigns Q).subgroupOf (orthogonalDerived Q))
      (toOmega hF f a)) : l ∈ imgL Θ hF f :=
  ⟨a, by rw [toL_apply, ← h, MulEquiv.symm_apply_apply]⟩

include hF in
theorem imgL_perfect : ⁅imgL Θ hF f, imgL Θ hF f⁆ = imgL Θ hF f := by
  change ⁅(toL Θ hF f).range, (toL Θ hF f).range⁆ = (toL Θ hF f).range
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hF]

theorem toL_eq_one_iff (a : F) : toL Θ hF f a = 1 ↔ f a ∈ scalarSigns Q := by
  rw [toL_apply, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Iff.rfl

theorem imgL_fixed (α : MulAut L) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
    (hconj : ∀ x, Θ (α x) = projectiveConjugation Q A μ hsim (Θ x))
    (hfA : ∀ a v, (f a).val (A v) = A ((f a).val v)) : ∀ x ∈ imgL Θ hF f, α x = x := by
  rintro _ ⟨a, rfl⟩
  apply Θ.injective
  rw [hconj, toL_apply, MulEquiv.apply_symm_apply, projectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [restrictAutomorphism_apply]
  change A * (f a).val * A⁻¹ = (f a).val
  refine LinearEquiv.ext fun v => ?_
  change A ((f a).val (A.symm v)) = (f a).val v
  rw [← hfA, LinearEquiv.apply_symm_apply]

theorem four_dvd_card_imgL [Finite L] {a b : F} (ha : a * a = 1) (hb : b * b = 1)
    (hab : Commute a b) (ha1 : f a ∉ scalarSigns Q) (hb1 : f b ∉ scalarSigns Q)
    (hab1 : f (a * b) ∉ scalarSigns Q) : 4 ∣ Nat.card (imgL Θ hF f) := by
  refine four_dvd_card_of_klein _ ⟨a, rfl⟩ ⟨b, rfl⟩ (by rw [← map_mul, ha, map_one])
    (by rw [← map_mul, hb, map_one]) (hab.map _) (fun h => ha1 ((toL_eq_one_iff Θ hF f a).mp h))
    (fun h => hb1 ((toL_eq_one_iff Θ hF f b).mp h)) (fun h => hab1 ?_)
  exact (toL_eq_one_iff Θ hF f (a * b)).mp (by rw [map_mul, h, ← map_mul, hb, map_one])

end Image

theorem not_mem_scalarSigns {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0) (g : TauCeti.QuadraticMap.orthogonalGroup Q)
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) (hgv : g.val v = -v) (hgw : g.val w = w) :
    g ∉ scalarSigns Q := by
  have hneg : ∀ x : V, x ≠ 0 → x ≠ -x := fun x hx h => by
    rw [eq_neg_iff_add_eq_zero, ← two_smul K] at h
    exact hx ((smul_eq_zero.mp h).resolve_left h2)
  rintro (rfl | rfl)
  · exact hneg v hv hgv
  · rw [QuadraticMap.coe_negOrthogonal] at hgw
    exact hneg w hw hgw.symm

section Reflections

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reflect_comm' {v w : V} (h : polar Q v w = 0) :
    reflect Q v * reflect Q w = reflect Q w * reflect Q v := by
  have h1 := reflect_conj (reflect_mem_orthogonalGroup Q v) w
  rw [reflect_apply_of_polar_eq_zero h] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem reflect_apply_self' {v : V} (hv : Q v ≠ 0) : reflect Q v v = -v := by
  rw [reflect_apply hv, polar_self, nsmul_eq_mul, Nat.cast_ofNat, mul_div_assoc, div_self hv,
    mul_one, two_smul]
  abel

theorem reflect_klein {e₀ e₁ e₂ : V} (h₀ : Q e₀ ≠ 0) (h₁ : Q e₁ ≠ 0) (h₂ : Q e₂ ≠ 0)
    (h01 : polar Q e₀ e₁ = 0) (h02 : polar Q e₀ e₂ = 0) (h12 : polar Q e₁ e₂ = 0) :
    (reflect Q e₀ * reflect Q e₁) * (reflect Q e₀ * reflect Q e₁) = 1 ∧
      (reflect Q e₀ * reflect Q e₂) * (reflect Q e₀ * reflect Q e₂) = 1 ∧
      (reflect Q e₀ * reflect Q e₁) * (reflect Q e₀ * reflect Q e₂) =
        (reflect Q e₀ * reflect Q e₂) * (reflect Q e₀ * reflect Q e₁) ∧
      (reflect Q e₀ * reflect Q e₁) e₁ = -e₁ ∧ (reflect Q e₀ * reflect Q e₁) e₂ = e₂ ∧
      (reflect Q e₀ * reflect Q e₂) e₂ = -e₂ ∧ (reflect Q e₀ * reflect Q e₂) e₁ = e₁ ∧
      ((reflect Q e₀ * reflect Q e₁) * (reflect Q e₀ * reflect Q e₂)) e₁ = -e₁ ∧
      ((reflect Q e₀ * reflect Q e₁) * (reflect Q e₀ * reflect Q e₂)) e₀ = e₀ := by
  have h10 : polar Q e₁ e₀ = 0 := by rw [polar_comm]; exact h01
  have h20 : polar Q e₂ e₀ = 0 := by rw [polar_comm]; exact h02
  have h21 : polar Q e₂ e₁ = 0 := by rw [polar_comm]; exact h12
  have c01 := reflect_comm' (Q := Q) h01
  have c02 := reflect_comm' (Q := Q) h02
  have c12 := reflect_comm' (Q := Q) h12
  have s0 := reflect_mul_self Q e₀
  have s1 := reflect_mul_self Q e₁
  have s2 := reflect_mul_self Q e₂
  have f01 := reflect_apply_of_polar_eq_zero (Q := Q) h01
  have f02 := reflect_apply_of_polar_eq_zero (Q := Q) h02
  have f10 := reflect_apply_of_polar_eq_zero (Q := Q) h10
  have f12 := reflect_apply_of_polar_eq_zero (Q := Q) h12
  have f20 := reflect_apply_of_polar_eq_zero (Q := Q) h20
  have f21 := reflect_apply_of_polar_eq_zero (Q := Q) h21
  have n0 := reflect_apply_self' h₀
  have n1 := reflect_apply_self' h₁
  have n2 := reflect_apply_self' h₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc (reflect Q e₁), ← c01, mul_assoc, s1, mul_one, s0]
  · rw [mul_assoc, ← mul_assoc (reflect Q e₂), ← c02, mul_assoc, s2, mul_one, s0]
  · have e1 : (reflect Q e₀ * reflect Q e₁) * (reflect Q e₀ * reflect Q e₂) =
        reflect Q e₁ * reflect Q e₂ := by
      rw [c01, mul_assoc, ← mul_assoc (reflect Q e₀) (reflect Q e₀), s0, one_mul]
    have e2 : (reflect Q e₀ * reflect Q e₂) * (reflect Q e₀ * reflect Q e₁) =
        reflect Q e₂ * reflect Q e₁ := by
      rw [c02, mul_assoc, ← mul_assoc (reflect Q e₀) (reflect Q e₀), s0, one_mul]
    rw [e1, e2, c12]
  · rw [LinearEquiv.mul_apply, n1, map_neg, f01]
  · rw [LinearEquiv.mul_apply, f12, f02]
  · rw [LinearEquiv.mul_apply, n2, map_neg, f02]
  · rw [LinearEquiv.mul_apply, f21, f01]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, f21, f01, n1,
      map_neg, f01]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, f20, n0, map_neg,
      map_neg, f10, n0, neg_neg]

end Reflections

end CFSG.ComponentClassification.GSThmB.Cent516
