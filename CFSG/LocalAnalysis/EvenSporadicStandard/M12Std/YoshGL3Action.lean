module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.DivisionRing

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

section Quotient

variable {K V L : Type*} [Field K] [AddCommGroup V] [Module K V] [Group L]

private noncomputable def quotientAction (σ : L →* Module.End K V) {c : V} (hc : ∀ ℓ, σ ℓ c = c) :
    L →* Module.End K (V ⧸ K ∙ c) where
  toFun ℓ := (K ∙ c).mapQ (K ∙ c) (σ ℓ) <| by
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap, hc]
    exact Submodule.mem_span_singleton_self c
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

theorem exists_hom_gl_quotient [Module.Finite K V] {n : ℕ} (hV : Module.finrank K V = n + 1)
    (σ : L →* Module.End K V) {c : V} (hc₀ : c ≠ 0) (hc : ∀ ℓ, σ ℓ c = c) :
    ∃ ρ : L →* GL (Fin n) K, ∀ ℓ, ρ ℓ = 1 ↔ ∀ x, σ ℓ x - x ∈ K ∙ c := by
  have hdim : Module.finrank K (V ⧸ K ∙ c) = n := by
    have h := (K ∙ c).finrank_quotient_add_finrank
    rw [finrank_span_singleton hc₀, hV] at h
    omega
  let b := Module.finBasisOfFinrankEq K (V ⧸ K ∙ c) hdim
  refine ⟨((Matrix.GeneralLinearGroup.toLin' b).symm : _ ≃* _).toMonoidHom.comp
    (quotientAction σ hc).toHomUnits, fun ℓ => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, Units.ext_iff,
    MonoidHom.coe_toHomUnits, Units.val_one, LinearMap.ext_iff]
  constructor
  · intro h x
    have := h (Submodule.Quotient.mk x)
    simpa [quotientAction, Submodule.Quotient.eq] using this
  · intro h q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simpa [quotientAction, Submodule.Quotient.eq] using h x

end Quotient

section ElementaryAbelian

private theorem mul_comm_of_mul_self_eq_one {E : Type*} [Group E] (hsq : ∀ e : E, e * e = 1)
    (a b : E) : a * b = b * a := by
  have h : ∀ x : E, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  calc a * b = (a * b)⁻¹ := (h _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [h, h]

private theorem mem_span_singleton_zmod_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {c x : V} : x ∈ ZMod 2 ∙ c ↔ x = 0 ∨ x = c := by
  have h2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rcases h2 a with rfl | rfl
    · left
      simp
    · right
      simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem exists_hom_gl_three_of_closure_eq_top {E L : Type*} [Group E] [Group L]
    (hsq : ∀ e : E, e * e = 1) (hcard : Nat.card E = 16) {c v₁ v₂ v₃ : E}
    (hcl : Subgroup.closure ({c, v₁, v₂, v₃} : Set E) = ⊤)
    (σ : L →* Monoid.End E) (hσ : ∀ ℓ, σ ℓ c = c) :
    ∃ ρ : L →* GL (Fin 3) (ZMod 2), ∀ ℓ, ρ ℓ = 1 ↔
      ∀ e : E, σ ℓ e * e⁻¹ = 1 ∨ σ ℓ e * e⁻¹ = c := by
  letI : CommGroup E := { ‹Group E› with mul_comm := mul_comm_of_mul_self_eq_one hsq }
  letI : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    exact congrArg Additive.ofMul (hsq (Additive.toMul x))
  haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
  haveI : Module.Finite (ZMod 2) (Additive E) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 2) (Additive E) = 3 + 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    rw [Nat.card_zmod, show Nat.card (Additive E) = 16 from hcard] at h
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num))
  have hc₁ : c ≠ 1 := by
    rintro rfl
    classical
    let t : Finset (Additive E) := {Additive.ofMul v₁, Additive.ofMul v₂, Additive.ofMul v₃}
    have key : ∀ e ∈ Subgroup.closure ({1, v₁, v₂, v₃} : Set E),
        Additive.ofMul e ∈ Submodule.span (ZMod 2) (t : Set (Additive E)) := by
      intro e he
      induction he using Subgroup.closure_induction with
      | mem y hy =>
        rcases hy with rfl | rfl | rfl | rfl
        · exact Submodule.zero_mem _
        · exact Submodule.subset_span (by simp [t])
        · exact Submodule.subset_span (by simp [t])
        · exact Submodule.subset_span (by simp [t])
      | one => exact Submodule.zero_mem _
      | mul y z _ _ hy hz => exact Submodule.add_mem _ hy hz
      | inv y _ hy => exact Submodule.neg_mem _ hy
    have htop : Submodule.span (ZMod 2) (t : Set (Additive E)) = ⊤ :=
      eq_top_iff.2 fun x _ => key (Additive.toMul x) (by rw [hcl]; exact Subgroup.mem_top _)
    have h1 := finrank_span_finset_le_card (R := ZMod 2) t
    rw [Set.finrank, htop, finrank_top, hrank] at h1
    have h2 : t.card ≤ 3 := Finset.card_le_three
    omega
  let τ : L →* Module.End (ZMod 2) (Additive E) :=
    { toFun := fun ℓ => AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (σ ℓ))
      map_one' := LinearMap.ext fun x => by rw [map_one]; rfl
      map_mul' := fun ℓ₁ ℓ₂ => LinearMap.ext fun x => by rw [map_mul]; rfl }
  obtain ⟨ρ, hρ⟩ := exists_hom_gl_quotient hrank τ
    (c := Additive.ofMul c) (by simpa using hc₁) (fun ℓ => congrArg Additive.ofMul (hσ ℓ))
  have hτ : ∀ ℓ (e : E),
      τ ℓ (Additive.ofMul e) - Additive.ofMul e = Additive.ofMul (σ ℓ e * e⁻¹) := by
    intro ℓ e
    rw [← div_eq_mul_inv]
    rfl
  refine ⟨ρ, fun ℓ => (hρ ℓ).trans ⟨fun h e => ?_, fun h x => ?_⟩⟩
  · have := h (Additive.ofMul e)
    rwa [mem_span_singleton_zmod_two, hτ, ofMul_eq_zero, Additive.ofMul.apply_eq_iff_eq] at this
  · obtain ⟨e, rfl⟩ := Additive.ofMul.surjective x
    rw [mem_span_singleton_zmod_two, hτ, ofMul_eq_zero, Additive.ofMul.apply_eq_iff_eq]
    exact h e

end ElementaryAbelian

theorem exists_hom_gl3 {G : Type*} [Group G] (L A : Subgroup G) (c v₁ v₂ v₃ : G)
    (hA : A = Subgroup.closure ({c, v₁, v₂, v₃} : Set G))
    (hcard : Nat.card A = 16)
    (hsq : ∀ a ∈ A, a * a = 1)
    (hLA : ∀ ℓ ∈ L, ∀ a ∈ A, ℓ * a * ℓ⁻¹ ∈ A)
    (hLc : ∀ ℓ ∈ L, ℓ * c * ℓ⁻¹ = c) :
    ∃ ρ : ↥L →* GL (Fin 3) (ZMod 2), ∀ ℓ : ↥L,
      ρ ℓ = 1 ↔ ∀ a ∈ A, ℓ * a * ℓ⁻¹ * a⁻¹ = 1 ∨ ℓ * a * ℓ⁻¹ * a⁻¹ = c := by
  have hgen : ∀ x ∈ ({c, v₁, v₂, v₃} : Set G), x ∈ A := fun x hx =>
    hA ▸ Subgroup.subset_closure hx
  have hcA : c ∈ A := hgen c (by simp)
  have hv₁A : v₁ ∈ A := hgen v₁ (by simp)
  have hv₂A : v₂ ∈ A := hgen v₂ (by simp)
  have hv₃A : v₃ ∈ A := hgen v₃ (by simp)
  let σ : ↥L →* Monoid.End ↥A :=
    { toFun := fun ℓ =>
        { toFun := fun a => ⟨ℓ * a * ℓ⁻¹, hLA ℓ ℓ.2 a a.2⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
      map_one' := Monoid.End.ext _ fun a => Subtype.ext (by
        change ((1 : ↥L) : G) * (a : G) * ((1 : ↥L) : G)⁻¹ = (a : G)
        simp)
      map_mul' := fun ℓ₁ ℓ₂ => Monoid.End.ext _ fun a => Subtype.ext (by
        change ((ℓ₁ * ℓ₂ : ↥L) : G) * (a : G) * ((ℓ₁ * ℓ₂ : ↥L) : G)⁻¹ =
          (ℓ₁ : G) * ((ℓ₂ : G) * (a : G) * (ℓ₂ : G)⁻¹) * (ℓ₁ : G)⁻¹
        simp [mul_assoc]) }
  have hσ_coe : ∀ (ℓ : ↥L) (e : ↥A), ((σ ℓ e : ↥A) : G) = ℓ * e * ℓ⁻¹ := fun _ _ => rfl
  have hcl : Subgroup.closure
      ({⟨c, hcA⟩, ⟨v₁, hv₁A⟩, ⟨v₂, hv₂A⟩, ⟨v₃, hv₃A⟩} : Set ↥A) = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    have himg : A.subtype '' ({⟨c, hcA⟩, ⟨v₁, hv₁A⟩, ⟨v₂, hv₂A⟩, ⟨v₃, hv₃A⟩} : Set ↥A) =
        {c, v₁, v₂, v₃} := by
      simp [Set.image_insert_eq]
    rw [MonoidHom.map_closure, himg, ← hA, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨ρ, hρ⟩ := exists_hom_gl_three_of_closure_eq_top (fun e => Subtype.ext (hsq e e.2))
    hcard hcl σ (fun ℓ => Subtype.ext (hLc ℓ ℓ.2))
  refine ⟨ρ, fun ℓ => (hρ ℓ).trans ⟨fun h a ha => ?_, fun h e => ?_⟩⟩
  · have := h ⟨a, ha⟩
    simpa [Subtype.ext_iff, hσ_coe] using this
  · have := h e e.2
    simpa [Subtype.ext_iff, hσ_coe] using this

end CFSG.EvenSporadicStandard.M12Std.Yosh
