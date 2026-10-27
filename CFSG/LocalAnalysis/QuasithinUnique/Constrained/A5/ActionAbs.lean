module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.QuasithinUnique.A5.Action

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem centerless {σ τ : Perm (Fin 5)} (h : ∀ a : Alt5, σ * a * σ⁻¹ = τ * a * τ⁻¹) : σ = τ := by
  have := cent_alt (τ⁻¹ * σ) (by
    intro a ha
    have := h ⟨a, (Equiv.Perm.mem_alternatingGroup.mpr ha)⟩
    simp only at this
    calc τ⁻¹ * σ * a = τ⁻¹ * (σ * a * σ⁻¹) * σ := by group
      _ = τ⁻¹ * (τ * a * τ⁻¹) * σ := by rw [this]
      _ = a * (τ⁻¹ * σ) := by group)
  have h2 : τ⁻¹ * σ = 1 := this
  calc σ = τ * (τ⁻¹ * σ) := by group
    _ = τ := by rw [h2, mul_one]

section

variable {X : Type*} [Group X] (L U : Subgroup X) [L.Normal] [U.Normal]
  (α : ↥L →* Alt5) (hα : Function.Surjective α) (hker : ∀ ℓ : ↥L, α ℓ = 1 ↔ (ℓ : X) ∈ U)

@[expose] noncomputable def psiHom (x : X) : Alt5 →* Alt5 :=
  (α.liftOfSurjective hα) ⟨α.comp (MulAut.conjNormal x).toMonoidHom, by
    intro ℓ hℓ
    rw [MonoidHom.mem_ker] at hℓ ⊢
    show α (MulAut.conjNormal x ℓ) = 1
    rw [hker] at hℓ ⊢
    rw [MulAut.conjNormal_apply]
    exact Subgroup.Normal.conj_mem inferInstance _ hℓ x⟩

theorem psiHom_apply (x : X) (ℓ : ↥L) :
    psiHom L U α hα hker x (α ℓ) = α (MulAut.conjNormal x ℓ) := by
  unfold psiHom
  exact MonoidHom.liftOfRightInverse_comp_apply α _ _ _ ℓ

theorem psiHom_mul (x y : X) (a : Alt5) :
    psiHom L U α hα hker (x * y) a = psiHom L U α hα hker x (psiHom L U α hα hker y a) := by
  obtain ⟨ℓ, rfl⟩ := hα a
  rw [psiHom_apply, psiHom_apply, psiHom_apply, map_mul, MulAut.mul_apply]

theorem psiHom_one (a : Alt5) : psiHom L U α hα hker 1 a = a := by
  obtain ⟨ℓ, rfl⟩ := hα a
  rw [psiHom_apply, map_one]; rfl

@[expose] noncomputable def psiEquiv (x : X) : Alt5 ≃* Alt5 :=
  (psiHom L U α hα hker x).toMulEquiv (psiHom L U α hα hker x⁻¹)
    (by ext a; rw [MonoidHom.comp_apply, ← psiHom_mul, inv_mul_cancel, psiHom_one]; rfl)
    (by ext a; rw [MonoidHom.comp_apply, ← psiHom_mul, mul_inv_cancel, psiHom_one]; rfl)

@[expose] noncomputable def piFun (x : X) : Perm (Fin 5) :=
  Classical.choose (aut_inner (psiEquiv L U α hα hker x))

theorem piFun_spec (x : X) (a : Alt5) :
    ((psiHom L U α hα hker x a : Alt5) : Perm (Fin 5)) =
      piFun L U α hα hker x * a * (piFun L U α hα hker x)⁻¹ :=
  Classical.choose_spec (aut_inner (psiEquiv L U α hα hker x)) a

theorem piFun_one : piFun L U α hα hker 1 = 1 := by
  apply centerless
  intro a
  rw [← piFun_spec, psiHom_one]; simp

theorem piFun_mul (x y : X) :
    piFun L U α hα hker (x * y) = piFun L U α hα hker x * piFun L U α hα hker y := by
  apply centerless
  intro a
  have h1 := piFun_spec L U α hα hker (x * y) a
  rw [psiHom_mul] at h1
  have h2 := piFun_spec L U α hα hker x (psiHom L U α hα hker y a)
  have h3 := piFun_spec L U α hα hker y a
  rw [h2, h3] at h1
  rw [← h1]
  simp only [mul_inv_rev]; group

theorem piFun_alt (ℓ : ↥L) : piFun L U α hα hker (ℓ : X) = ((α ℓ : Alt5) : Perm (Fin 5)) := by
  apply centerless
  intro a
  rw [← piFun_spec]
  obtain ⟨m, rfl⟩ := hα a
  rw [psiHom_apply]
  have : (MulAut.conjNormal (ℓ : X)) m = ℓ * m * ℓ⁻¹ := by
    apply Subtype.ext; rw [MulAut.conjNormal_apply]; simp
  rw [this]
  simp [map_mul, map_inv]

@[expose] noncomputable def piHom : X →* Perm (Fin 5) :=
  MonoidHom.mk' (piFun L U α hα hker) (piFun_mul L U α hα hker)

theorem piHom_apply (x : X) : piHom L U α hα hker x = piFun L U α hα hker x := rfl

variable (β : ↥U ≃* Multiplicative (evenWeight 5))
  (hβ : ∀ (ℓ : ↥L) (u u' : ↥U), (u' : X) = (ℓ : X) * (u : X) * (ℓ : X)⁻¹ →
    Multiplicative.toAdd (β u') = vact ((α ℓ : Alt5) : Perm (Fin 5)) (Multiplicative.toAdd (β u)))

@[expose] noncomputable def fX (x : X) (w : evenWeight 5) : evenWeight 5 :=
  Multiplicative.toAdd (β (MulAut.conjNormal x (β.symm (Multiplicative.ofAdd w))))

theorem fX_add (x : X) (w w' : evenWeight 5) :
    fX U β x (w + w') = fX U β x w + fX U β x w' := by
  unfold fX
  rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul]

theorem fX_inj (x : X) : Function.Injective (fX U β x) := by
  intro w w' h
  unfold fX at h
  have := (Multiplicative.toAdd.injective h)
  have := β.injective this
  have := (MulAut.conjNormal x).injective this
  have := β.symm.injective this
  exact Multiplicative.ofAdd.injective this

theorem fX_bU (x : X) (u : ↥U) :
    fX U β x (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (MulAut.conjNormal x u)) := by
  unfold fX
  simp

include hβ in
theorem pi_compat (x : X) (u u' : ↥U) (h : (u' : X) = x * u * x⁻¹) :
    Multiplicative.toAdd (β u') =
      vact (piFun L U α hα hker x) (Multiplicative.toAdd (β u)) := by
  have hu' : u' = MulAut.conjNormal x u := by
    apply Subtype.ext; rw [MulAut.conjNormal_apply]; exact h
  have hg : ∀ w, vact (piFun L U α hα hker x)⁻¹ (fX U β x w) = w := by
    apply rigid (fun w => vact (piFun L U α hα hker x)⁻¹ (fX U β x w))
    · intro w w'
      show vact _ (fX U β x (w + w')) = vact _ (fX U β x w) + vact _ (fX U β x w')
      rw [fX_add, vact_add]
    · intro w w' h
      apply fX_inj U β x
      have := congrArg (vact (piFun L U α hα hker x)) h
      simpa [← vact_mul, vact_one] using this
    · intro σ hσ w
      show vact _ (fX U β x (vact σ w)) = vact σ (vact _ (fX U β x w))
      obtain ⟨ℓ, hℓ⟩ := hα ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ⟩
      have hℓσ : ((α ℓ : Alt5) : Perm (Fin 5)) = σ := by rw [hℓ]
      set u₀ := β.symm (Multiplicative.ofAdd w) with hu₀
      have hw : w = Multiplicative.toAdd (β u₀) := by simp [hu₀]
      have h1 : vact σ w = Multiplicative.toAdd (β (MulAut.conjNormal (ℓ : X) u₀)) := by
        rw [hβ ℓ u₀ _ (by rw [MulAut.conjNormal_apply]), hℓσ, ← hw]
      have h2 : MulAut.conjNormal x (MulAut.conjNormal (ℓ : X) u₀) =
          MulAut.conjNormal ((MulAut.conjNormal x ℓ : ↥L) : X) (MulAut.conjNormal x u₀) := by
        apply Subtype.ext
        simp only [MulAut.conjNormal_apply]
        group
      have h3 : fX U β x (vact σ w) =
          vact ((piFun L U α hα hker x) * σ * (piFun L U α hα hker x)⁻¹) (fX U β x w) := by
        rw [h1, fX_bU, h2]
        rw [hβ (MulAut.conjNormal x ℓ) (MulAut.conjNormal x u₀) _ rfl]
        rw [hw, fX_bU]
        congr 1
        rw [← psiHom_apply L U α hα hker x ℓ]
        rw [← hℓσ, ← piFun_spec]
      rw [h3, ← vact_mul, ← vact_mul]
      congr 1
      group
  have h5 := hg (Multiplicative.toAdd (β u))
  rw [fX_bU] at h5
  have h6 := congrArg (vact (piFun L U α hα hker x)) h5
  rw [← vact_mul, mul_inv_cancel, vact_one] at h6
  rw [hu']
  exact h6

include hβ in
theorem piHom_eq_of_compat (x : X) {σ : Perm (Fin 5)}
    (hσ : ∀ u u' : ↥U, (u' : X) = x * u * x⁻¹ →
      Multiplicative.toAdd (β u') = vact σ (Multiplicative.toAdd (β u))) :
    σ = piHom L U α hα hker x := by
  have h : ∀ w : evenWeight 5, vact (σ⁻¹ * piHom L U α hα hker x) w = w := by
    intro w
    obtain ⟨u, rfl⟩ : ∃ u : ↥U, Multiplicative.toAdd (β u) = w :=
      ⟨β.symm (Multiplicative.ofAdd w), by simp⟩
    have e : ((MulAut.conjNormal x u : ↥U) : X) = x * u * x⁻¹ := MulAut.conjNormal_apply x u
    have h1 := hσ u _ e
    have h2 := pi_compat L U α hα hker β hβ x u _ e
    have h3 : vact σ (Multiplicative.toAdd (β u)) =
        vact (piHom L U α hα hker x) (Multiplicative.toAdd (β u)) := h1.symm.trans h2
    rw [vact_mul, ← h3, ← vact_mul, inv_mul_cancel, vact_one]
  exact inv_mul_eq_one.mp (vact_faithful h)

include hβ in
theorem piHom_eq_one_iff (x : X) :
    piHom L U α hα hker x = 1 ↔ ∀ u : ↥U, x * (u : X) * x⁻¹ = (u : X) := by
  constructor
  · intro h u
    have e : ((MulAut.conjNormal x u : ↥U) : X) = x * u * x⁻¹ := MulAut.conjNormal_apply x u
    have h2 := pi_compat L U α hα hker β hβ x u _ e
    rw [← piHom_apply, h, vact_one] at h2
    have := β.injective (Multiplicative.toAdd.injective h2)
    rw [← e, this]
  · intro h
    apply vact_faithful
    intro w
    obtain ⟨u, rfl⟩ : ∃ u : ↥U, Multiplicative.toAdd (β u) = w :=
      ⟨β.symm (Multiplicative.ofAdd w), by simp⟩
    exact (pi_compat L U α hα hker β hβ x u u (h u).symm).symm

include hα hker hβ in
theorem exists_pi : ∃ π : X →* Perm (Fin 5),
    (∀ (x : X) (u u' : ↥U), (u' : X) = x * u * x⁻¹ →
      Multiplicative.toAdd (β u') = vact (π x) (Multiplicative.toAdd (β u))) ∧
    (∀ ℓ : ↥L, π (ℓ : X) = ((α ℓ : Alt5) : Perm (Fin 5))) ∧
    (∀ (x : X) (ℓ ℓ' : ↥L), (ℓ' : X) = x * ℓ * x⁻¹ →
      ((α ℓ' : Alt5) : Perm (Fin 5)) = π x * α ℓ * (π x)⁻¹) := by
  refine ⟨piHom L U α hα hker, fun x u u' h => pi_compat L U α hα hker β hβ x u u' h,
    fun ℓ => piFun_alt L U α hα hker ℓ, ?_⟩
  intro x ℓ ℓ' h
  have hℓ' : ℓ' = MulAut.conjNormal x ℓ := by
    apply Subtype.ext; rw [MulAut.conjNormal_apply]; exact h
  rw [hℓ', ← psiHom_apply L U α hα hker x ℓ]
  exact piFun_spec L U α hα hker x (α ℓ)

end

end CFSG.QuasithinUnique.A5.Action
