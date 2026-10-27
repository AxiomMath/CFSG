module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
public import CFSG.ClassicalInvolution.Asc77.AscL62Aut

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {K₀ E : Type} [Group K₀] [Group E] (θ : K₀ →* E) {R₀ : Subgroup K₀}

theorem injective_subgroupMap (hker : θ.ker ≤ Subgroup.center K₀)
    (hR : ∀ r ∈ R₀, r ∈ Subgroup.center K₀ → r = 1) : Function.Injective (θ.subgroupMap R₀) := by
  intro r s hrs
  have h1 : θ (r : K₀) = θ (s : K₀) := congrArg Subtype.val hrs
  have h2 : (r : K₀) * (s : K₀)⁻¹ ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := hR _ (R₀.mul_mem r.2 (R₀.inv_mem s.2)) (hker h2)
  exact Subtype.ext (mul_inv_eq_one.mp h3)

@[expose] noncomputable def restrictEquiv (hker : θ.ker ≤ Subgroup.center K₀)
    (hR : ∀ r ∈ R₀, r ∈ Subgroup.center K₀ → r = 1) : R₀ ≃* R₀.map θ :=
  MulEquiv.ofBijective (θ.subgroupMap R₀)
    ⟨injective_subgroupMap θ hker hR, θ.subgroupMap_surjective R₀⟩

theorem coe_restrictEquiv (hker : θ.ker ≤ Subgroup.center K₀)
    (hR : ∀ r ∈ R₀, r ∈ Subgroup.center K₀ → r = 1) (r : R₀) :
    ((restrictEquiv θ hker hR r : R₀.map θ) : E) = θ r :=
  rfl

theorem mem_of_lift [Group.IsPerfect R₀] (hker : θ.ker ≤ Subgroup.center K₀)
    (hR : ∀ r ∈ R₀, r ∈ Subgroup.center K₀ → r = 1) {φ : MulAut E}
    (hφ : ∀ x ∈ R₀.map θ, φ x ∈ R₀.map θ) {α : K₀ →* K₀} (hα : ∀ x, θ (α x) = φ (θ x)) :
    ∀ r ∈ R₀, α r ∈ R₀ := by
  set e := restrictEquiv θ hker hR
  let φL : R₀.map θ →* R₀.map θ :=
    (φ.toMonoidHom.comp (R₀.map θ).subtype).codRestrict (R₀.map θ) fun x => hφ x x.2
  let β : R₀ →* R₀ := e.symm.toMonoidHom.comp (φL.comp e.toMonoidHom)
  have hab : R₀.subtype.comp β = α.comp R₀.subtype :=
    ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect hker _ _ fun r => by
      have h1 : θ ((e.symm (φL (e r)) : R₀) : K₀) = ((φL (e r) : R₀.map θ) : E) := by
        rw [← coe_restrictEquiv θ hker hR, MulEquiv.apply_symm_apply]
      show θ ((e.symm (φL (e r)) : R₀) : K₀) = θ (α r)
      rw [h1, hα]
      rfl
  intro r hr
  have h := DFunLike.congr_fun hab ⟨r, hr⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h
  rw [← h]
  exact (β ⟨r, hr⟩).2

@[expose] def liftRestrict (α : K₀ →* K₀) (hαR : ∀ r ∈ R₀, α r ∈ R₀) : R₀ →* R₀ :=
  (α.comp R₀.subtype).codRestrict R₀ fun r => hαR r r.2

theorem coe_liftRestrict (α : K₀ →* K₀) (hαR : ∀ r ∈ R₀, α r ∈ R₀) (r : R₀) :
    ((liftRestrict α hαR r : R₀) : K₀) = α r :=
  rfl

theorem semilin_restrict {F : Type} [Field F] (hker : θ.ker ≤ Subgroup.center K₀)
    (hR : ∀ r ∈ R₀, r ∈ Subgroup.center K₀ → r = 1) {φ : MulAut E} {α : K₀ →* K₀}
    (hα : ∀ x, θ (α x) = φ (θ x)) (hαR : ∀ r ∈ R₀, α r ∈ R₀) (ι : R₀.map θ ≃* SL(2, F))
    (g : GL (Fin 2) F)
    (hι : ∀ x : R₀.map θ,
      ((ι.symm (Asc77.AscL62.semilinHom g (RingEquiv.refl _) (ι x)) : R₀.map θ) : E) = φ x)
    (r : R₀) :
    ((restrictEquiv θ hker hR).trans ι) (liftRestrict α hαR r) =
      Asc77.AscL62.semilinHom g (RingEquiv.refl _) (((restrictEquiv θ hker hR).trans ι) r) := by
  set e := restrictEquiv θ hker hR
  have h1 : e (liftRestrict α hαR r) =
      ι.symm (Asc77.AscL62.semilinHom g (RingEquiv.refl _) (ι (e r))) := by
    apply Subtype.ext
    rw [hι, coe_restrictEquiv, coe_restrictEquiv, coe_liftRestrict, hα]
  simp only [MulEquiv.trans_apply]
  rw [h1, MulEquiv.apply_symm_apply]

theorem mem_centralizer_of_map [Group.IsPerfect R₀] (hker : θ.ker ≤ Subgroup.center K₀) {x : K₀}
    (hx : θ x ∈ Subgroup.centralizer (R₀.map θ : Set E)) :
    x ∈ Subgroup.centralizer (R₀ : Set K₀) := by
  have hab : ((MulAut.conj x).toMonoidHom.comp R₀.subtype) = R₀.subtype :=
    ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect hker _ _ fun r => by
      have h1 := (Subgroup.mem_centralizer_iff.mp hx) (θ r) ⟨r, r.2, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.coe_subtype, map_mul, map_inv]
      rw [← h1, mul_inv_cancel_right]
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have h := DFunLike.congr_fun hab ⟨r, hr⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_subtype] at h
  calc r * x = x * r * x⁻¹ * x := by rw [h]
    _ = x * r := by group

theorem eq_conj_of_lift (hθ : Function.Surjective θ) {φ : MulAut E} {α : K₀ →* K₀}
    (hα : ∀ x, θ (α x) = φ (θ x)) {y₀ : K₀} (hy : ∀ x, α x = y₀ * x * y₀⁻¹) :
    φ = MulAut.conj (θ y₀) := by
  ext z
  obtain ⟨x, rfl⟩ := hθ z
  rw [← hα, hy, MulAut.conj_apply, map_mul, map_mul, map_inv]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
