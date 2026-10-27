module

public import CFSG.LargeExtraspecial.S9SevenE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G]

@[expose] noncomputable def cenU (S : Setting G) (g : G) (k : S.M) : Subgroup S.O where
  carrier := {y | y ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g) ∧
    ∀ u ∈ Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)), (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u}
  mul_mem' := by
    rintro x y ⟨hx, hxu⟩ ⟨hy, hyu⟩
    refine ⟨mul_mem hx hy, fun u hu => ?_⟩
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hyu u hu, hxu u hu]
  one_mem' := ⟨one_mem _, fun _ _ => rfl⟩
  inv_mem' := by
    rintro x ⟨hx, hxu⟩
    refine ⟨inv_mem hx, fun u hu => ?_⟩
    conv_lhs => rw [← hxu u hu]
    exact inv_apply_apply_O x u

theorem mem_cenU {S : Setting G} {g : G} {k : S.M} {y : S.O} :
    y ∈ cenU S g k ↔ y ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g) ∧
      ∀ u ∈ Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)), (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u :=
  Iff.rfl

theorem conj_mem_cenU {S : Setting G} {g : G} {k : S.M} {x : S.O}
    (hx : x ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g)) {c : S.O} (hc : c ∈ cenU S g k) :
    x * c * x⁻¹ ∈ cenU S g k := by
  obtain ⟨hcX, hcu⟩ := mem_cenU.mp hc
  refine mem_cenU.mpr ⟨mul_mem (mul_mem hx hcX) (inv_mem hx), fun u hu => ?_⟩
  have h1 := hcu _ (apply_mem_Ut (inv_mem hx) hu)
  change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt)
    (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u)) = u
  rw [h1, apply_inv_apply_O]

namespace Hyp97

variable {S : Setting G} {g : G} {k : S.M} {O : Subgroup S.O} (X : Hyp97 S g k O)
include X

theorem mem_of_mem_Lbar_cenU (hLO : ¬ S.Lbar g ≤ O) {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) {l : S.O} (hl : l ∈ S.Lbar g)
    (hlc : l ∈ cenU S g k) : l ∈ O := by
  by_contra hlO
  obtain ⟨hbU, -⟩ := X.finrank_Ut_eq_two hLO hℓL hℓ
  have h1 := (mem_cenU.mp hlc).2 _ hbU
  have h2 := X.fix_Ut (hℓ l hl hlO) hbU
  have e : l = ℓ * (ℓ⁻¹ * l) := by group
  rw [e, Subgroup.coe_mul, LinearEquiv.mul_apply, h2, X.apply_cl_b_eq hLO hℓL hℓ] at h1
  have h3 : S.cl (g * S.z * g⁻¹) = 0 := by
    have := congrArg (· - S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) h1
    simpa using this
  exact cl_conj_z_ne_zero S X.hyp4.conj_mem X.hyp4.conj_ne h3

theorem mem_of_mem_Lbar_mul_cenU (hLO : ¬ S.Lbar g ≤ O) {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) {ℓ' : S.O} (hℓ'L : ℓ' ∈ S.Lbar ((k : G) * g))
    (hℓ'a : (ℓ' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) + S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) {l' : S.O}
    (hl' : l' ∈ S.Lbar ((k : G) * g)) (hlc : l' ∈ cenU S g k) : l' ∈ O := by
  have hconj := X.exists_conj hLO hℓL hℓ hℓ'L hℓ'a
  have hxX : ℓ * ℓ' ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g) := mul_mem (mem_sup_left hℓL)
    (mem_sup_right hℓ'L)
  rw [hconj] at hl'
  obtain ⟨l, hl, rfl⟩ := hl'
  have hlc' := conj_mem_cenU (inv_mem hxX) hlc
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hlc' ⊢
  rw [show (ℓ * ℓ')⁻¹ * ((ℓ * ℓ') * l * (ℓ * ℓ')⁻¹) * (ℓ * ℓ')⁻¹⁻¹ = l by group] at hlc'
  exact X.normal _ hxX _ (X.mem_of_mem_Lbar_cenU hLO hℓL hℓ hl hlc')

theorem commutator_mem (hLO : ¬ S.Lbar g ≤ O) {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) {ℓ' : S.O} (hℓ'L : ℓ' ∈ S.Lbar ((k : G) * g))
    (hℓ'a : (ℓ' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) + S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) {c : S.O}
    (hc : c ∈ cenU S g k) {y : S.O} (hy : y ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g)) :
    c * y * c⁻¹ * y⁻¹ ∈ O := by
  have H := X.hyp4
  obtain ⟨hcX, hcu⟩ := mem_cenU.mp hc
  obtain ⟨hbU, -⟩ := X.finrank_Ut_eq_two hLO hℓL hℓ
  have hcM : c ∈ S.Mbar := (sup_le (S.Lbar_le_Mbar g) (S.Lbar_le_Mbar _)) hcX
  have hcNa : c ∈ normalizer (S.Lbar g : Set S.O) := by
    have := mem_normalizer_of_fix (S := S) (g := g) (h := 1) H.conj_mem H.conj_ne hcM
      (by simpa using hcu _ (cl_mem_Ut _))
    simpa using this
  have hcNb : c ∈ normalizer (S.Lbar ((k : G) * g) : Set S.O) :=
    mem_normalizer_of_fix H.conj_mem H.conj_ne hcM (hcu _ hbU)
  have hgen : ∀ l, (l ∈ S.Lbar g ∨ l ∈ S.Lbar ((k : G) * g)) → c * l * c⁻¹ * l⁻¹ ∈ O := by
    intro l hl
    have hlX : l ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g) := hl.elim mem_sup_left mem_sup_right
    have hcc : c * l * c⁻¹ * l⁻¹ ∈ cenU S g k := by
      have := mul_mem hc (conj_mem_cenU hlX (inv_mem hc))
      rwa [show c * (l * c⁻¹ * l⁻¹) = c * l * c⁻¹ * l⁻¹ by group] at this
    rcases hl with hl | hl
    · have hmem : c * l * c⁻¹ * l⁻¹ ∈ S.Lbar g :=
        mul_mem ((mem_normalizer_iff.mp hcNa l).mp hl) (inv_mem hl)
      exact X.mem_of_mem_Lbar_cenU hLO hℓL hℓ hmem hcc
    · have hmem : c * l * c⁻¹ * l⁻¹ ∈ S.Lbar ((k : G) * g) :=
        mul_mem ((mem_normalizer_iff.mp hcNb l).mp hl) (inv_mem hl)
      exact X.mem_of_mem_Lbar_mul_cenU hLO hℓL hℓ hℓ'L hℓ'a hmem hcc
  let T : Subgroup S.O :=
    { carrier := {y | y ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g) ∧ c * y * c⁻¹ * y⁻¹ ∈ O}
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
        refine ⟨mul_mem h₁ h₂, ?_⟩
        have := mul_mem h₁' (X.normal _ h₁ _ h₂')
        rwa [show c * y₁ * c⁻¹ * y₁⁻¹ * (y₁ * (c * y₂ * c⁻¹ * y₂⁻¹) * y₁⁻¹) =
          c * (y₁ * y₂) * c⁻¹ * (y₁ * y₂)⁻¹ by group] at this
      one_mem' := ⟨one_mem _, by rw [mul_one, mul_inv_cancel, inv_one, mul_one]; exact one_mem _⟩
      inv_mem' := by
        rintro y ⟨h₁, h₁'⟩
        refine ⟨inv_mem h₁, ?_⟩
        have := X.normal _ (inv_mem h₁) _ (inv_mem h₁')
        rwa [show y⁻¹ * (c * y * c⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ = c * y⁻¹ * c⁻¹ * y⁻¹⁻¹ by group] at this }
  have hLT : S.Lbar g ≤ T := fun l hl => ⟨mem_sup_left hl, hgen l (Or.inl hl)⟩
  have hLbT : S.Lbar ((k : G) * g) ≤ T := fun l hl => ⟨mem_sup_right hl, hgen l (Or.inr hl)⟩
  exact ((sup_le hLT hLbT) hy).2

end Hyp97

end CFSG.LargeExtraspecial.S9
