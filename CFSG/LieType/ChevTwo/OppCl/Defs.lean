module

public import CFSG.LieType.BorelTits.IsotropicKernel
public import CFSG.LieType.BorelTits.OrthogonalForm
import CFSG.LieType.BorelTits.CentralQuotient

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

section Defs

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def semilinGroup (F V : Type) [Field F] [AddCommGroup V] [Module F V] :
    Subgroup (Equiv.Perm V) where
  carrier := {g | (∀ u v, g (u + v) = g u + g v) ∧
    ∃ σ : F ≃+* F, ∀ (c : F) (v : V), g (c • v) = σ c • g v}
  one_mem' := ⟨fun u v => rfl, RingEquiv.refl F, fun c v => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, σ, hσ⟩ ⟨hb, τ, hτ⟩
    refine ⟨fun u v => ?_, τ.trans σ, fun c v => ?_⟩
    · show a (b (u + v)) = a (b u) + a (b v)
      rw [hb, ha]
    · show a (b (c • v)) = σ (τ c) • a (b v)
      rw [hτ, hσ]
  inv_mem' := by
    rintro a ⟨ha, σ, hσ⟩
    refine ⟨fun u v => ?_, σ.symm, fun c v => ?_⟩
    · show a.symm (u + v) = a.symm u + a.symm v
      apply a.injective
      rw [ha, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    · show a.symm (c • v) = σ.symm c • a.symm v
      apply a.injective
      rw [hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply, RingEquiv.apply_symm_apply]

@[expose] def SemiIso (Φ : ReflForm F V) (r : Equiv.Perm V) : Prop :=
  ∃ τ : F ≃+* F, ∀ u v, Φ.β (r u) (r v) = τ (Φ.β u v)

@[expose] def SemiIsoQ (Φ : QuadForm F V) (r : Equiv.Perm V) : Prop :=
  ∃ τ : F ≃+* F, ∀ v, Φ.Q (r v) = τ (Φ.Q v)

variable {H K : Type} [Group H] [Group K]

@[expose] def NormH (ρ : H →* Module.End F V) (r : Equiv.Perm V) : Prop :=
  ∀ h : H, ∃ h' : H, ∀ v, r (ρ h v) = ρ h' (r v)

@[expose] def NormQ (ρ : H →* Module.End F V) (r : Equiv.Perm V) (Q : Subgroup H) : Prop :=
  ∀ x ∈ Q, ∃ x' ∈ Q, ∀ v, r (ρ x v) = ρ x' (r v)

@[expose] def CommR (ρ : H →* Module.End F V) (Rh : Subgroup (Equiv.Perm V)) (x : H) : Prop :=
  ∀ r ∈ Rh, ∀ v, r (ρ x v) = ρ x (r v)

@[expose] def Induces (π : H →* K) (ρ : H →* Module.End F V) (r : Equiv.Perm V)
    (α : MulAut K) : Prop :=
  (∀ h : H, ∃ h' : H, (∀ v, r (ρ h v) = ρ h' (r v)) ∧ α (π h) = π h') ∧
  (∀ h : H, ∃ h' : H, (∀ v, r⁻¹ (ρ h v) = ρ h' (r⁻¹ v)) ∧ α⁻¹ (π h) = π h')

@[expose] def AutLift (P : Equiv.Perm V → Prop) (π : H →* K) (ρ : H →* Module.End F V) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ R : Subgroup (MulAut K), IsPGroup p R →
    ∃ Rh : Subgroup (Equiv.Perm V), Rh ≤ semilinGroup F V ∧ (∀ r ∈ Rh, P r) ∧ IsPGroup p Rh ∧
      (∀ r ∈ Rh, NormH ρ r) ∧ (∀ α ∈ R, ∃ r ∈ Rh, Induces π ρ r α) ∧
      (∀ r ∈ Rh, ∃ α ∈ R, Induces π ρ r α)

@[expose] def RaiseProp (P : Equiv.Perm V → Prop) (ρ : H →* Module.End F V)
    (𝔉 : Subgroup H → ℕ → Submodule F V) (p : ℕ) : Prop :=
  ∀ Rh : Subgroup (Equiv.Perm V), Rh ≤ semilinGroup F V → (∀ r ∈ Rh, P r) → IsPGroup p Rh →
    (∀ r ∈ Rh, NormH ρ r) → ∀ Q : Subgroup H, IsPGroup 2 Q → (∀ r ∈ Rh, NormQ ρ r Q) →
      ∀ x ∈ flagKernel ρ (𝔉 Q), x ≠ 1 → CommR ρ Rh x →
        ∃ y : H, CommR ρ Rh y ∧ y ∉ flagStab ρ (𝔉 Q)

end Defs

section SemiIsoClosure

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem semiIso_one (Φ : ReflForm F V) : SemiIso Φ 1 :=
  ⟨RingEquiv.refl F, fun u v => rfl⟩

theorem semiIso_mul (Φ : ReflForm F V) {r s : Equiv.Perm V} (hr : SemiIso Φ r)
    (hs : SemiIso Φ s) : SemiIso Φ (r * s) := by
  obtain ⟨σ, hσ⟩ := hr
  obtain ⟨τ, hτ⟩ := hs
  exact ⟨τ.trans σ, fun u v => by
    show Φ.β (r (s u)) (r (s v)) = σ (τ (Φ.β u v))
    rw [hσ, hτ]⟩

theorem semiIso_inv (Φ : ReflForm F V) {r : Equiv.Perm V} (hr : SemiIso Φ r) :
    SemiIso Φ r⁻¹ := by
  obtain ⟨σ, hσ⟩ := hr
  refine ⟨σ.symm, fun u v => ?_⟩
  have h := hσ (r⁻¹ u) (r⁻¹ v)
  rw [show r (r⁻¹ u) = u from r.apply_symm_apply u,
    show r (r⁻¹ v) = v from r.apply_symm_apply v] at h
  rw [h, RingEquiv.symm_apply_apply]

theorem semiIsoQ_one (Φ : QuadForm F V) : SemiIsoQ Φ 1 :=
  ⟨RingEquiv.refl F, fun v => rfl⟩

theorem semiIsoQ_mul (Φ : QuadForm F V) {r s : Equiv.Perm V} (hr : SemiIsoQ Φ r)
    (hs : SemiIsoQ Φ s) : SemiIsoQ Φ (r * s) := by
  obtain ⟨σ, hσ⟩ := hr
  obtain ⟨τ, hτ⟩ := hs
  exact ⟨τ.trans σ, fun v => by
    show Φ.Q (r (s v)) = σ (τ (Φ.Q v))
    rw [hσ, hτ]⟩

theorem semiIsoQ_inv (Φ : QuadForm F V) {r : Equiv.Perm V} (hr : SemiIsoQ Φ r) :
    SemiIsoQ Φ r⁻¹ := by
  obtain ⟨σ, hσ⟩ := hr
  refine ⟨σ.symm, fun v => ?_⟩
  have h := hσ (r⁻¹ v)
  rw [show r (r⁻¹ v) = v from r.apply_symm_apply v] at h
  rw [h, RingEquiv.symm_apply_apply]

end SemiIsoClosure

section Forms

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]

structure Split3 (Φ : ReflForm F V) (TS : Submodule F V → Prop) (W M W' : Submodule F V) :
    Prop where
  ts_W : TS W
  ts_W' : TS W'
  perp_WM : ∀ w ∈ W, ∀ m ∈ M, Φ.β w m = 0
  perp_MW' : ∀ m ∈ M, ∀ w ∈ W', Φ.β m w = 0
  sup_eq : W ⊔ M ⊔ W' = ⊤
  disj_W : Disjoint W (M ⊔ W')
  disj_M : Disjoint M W'

@[expose] def EA0 (Φ : ReflForm F V) (Sing : V → Prop) (ρ : H →* Module.End F V) : Prop :=
  ∀ x y, Sing x → Sing y → Φ.β x y = 0 →
    ∃ h : H, ∀ v, ρ h v = v + Φ.β x v • y - Φ.β y v • x

@[expose] def EA1 (Φ : ReflForm F V) (Sing : V → Prop) (ρ : H →* Module.End F V) : Prop :=
  ∀ x y, Sing x → Φ.β x y = 0 →
    ∃ (c : F) (h : H), ∀ v, ρ h v = v + Φ.β x v • (y + c • x) - Φ.β y v • x

@[expose] def EA2 (Φ : ReflForm F V) (Sing : V → Prop) (ρ : H →* Module.End F V) : Prop :=
  ∀ (x : V) (c : F), Sing x → Φ.σ c = c →
    ∃ h : H, ∀ v, ρ h v = v + (c * Φ.β x v) • x

structure RaiseCtx (Φ : ReflForm F V) (Sing : V → Prop) (TS : Submodule F V → Prop)
    (ρ : H →* Module.End F V) (p : ℕ) (Rh : Subgroup (Equiv.Perm V)) (X : ℕ → Submodule F V)
    (m : ℕ) (M W' : Submodule F V) : Prop where
  hσ : ∀ c, Φ.σ (Φ.σ c) = c
  hsymm : ∀ u v, Φ.β v u = Φ.σ (Φ.β u v)
  hSing : ∀ v, Sing v → Φ.β v v = 0
  hTS : ∀ U, TS U → Φ.IsTotallyIsotropic U
  hTSsing : ∀ U, TS U → ∀ v ∈ U, Sing v
  hρ : IsIsometric Φ ρ
  hinj : Function.Injective ρ
  hE0 : EA0 Φ Sing ρ
  hE1 : EA1 Φ Sing ρ
  hs : Rh ≤ semilinGroup F V
  hiso : ∀ r ∈ Rh, SemiIso Φ r
  hR : IsPGroup p Rh
  hN : ∀ r ∈ Rh, NormH ρ r
  hX0 : X 0 = ⊥
  hXmono : Monotone X
  hXts : ∀ k, TS (X k)
  hXinv : ∀ r ∈ Rh, ∀ k, ∀ v ∈ X k, r v ∈ X k
  hsplit : Split3 Φ TS (X m) M W'
  hMinv : ∀ r ∈ Rh, ∀ v ∈ M, r v ∈ M
  hW'inv : ∀ r ∈ Rh, ∀ v ∈ W', r v ∈ W'

@[expose] noncomputable def Urad (Φ : ReflForm F V) (ρ : H →* Module.End F V)
    (W' : Submodule F V) : Subgroup H :=
  flagKernel ρ (isoCompletion Φ (fun k => if k = 0 then ⊥ else W') 1)

@[expose] def LevProp (Φ : ReflForm F V) (ρ : H →* Module.End F V) (W : Submodule F V)
    (g : V →ₗ[F] V) (u : H) : Prop :=
  (∀ w ∈ W, ρ u w = w + g w) ∧ ∀ y ∈ Φ.perp W, ρ u y - y ∈ W

end Forms

theorem statedProj_kernel_central {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (H : Subgroup (GL ι K)) : (StatedScalars ι K).subgroupOf H ≤ Subgroup.center H := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  have hx' : (x : GL ι K) ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx
  rw [Subgroup.mem_center_iff]
  exact fun g => Subtype.ext (Subgroup.mem_center_iff.mp hx' g)

theorem statedProj_kernel_coprime {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    (r : ℕ) [Fact r.Prime] [CharP K r] (H : Subgroup (GL ι K)) :
    Nat.Coprime (Nat.card ((StatedScalars ι K).subgroupOf H)) r := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hxr : x ^ r = 1 := hx ▸ pow_orderOf_eq_one x
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp x.2
  have hcr : Matrix.GeneralLinearGroup.scalar ι c ^ r = 1 := by
    rw [hc]
    simpa using congrArg (fun y : (StatedScalars ι K).subgroupOf H => ((y : H) : GL ι K)) hxr
  have hx1 : x = 1 := Subtype.ext (Subtype.ext (hc ▸ scalar_eq_one_of_pow_eq_one c hcr))
  rw [hx1, orderOf_one] at hx
  exact (Fact.out : r.Prime).one_lt.ne hx

section SemilinMap

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] def semilinMap (A : GL ι F) (σ : F ≃+* F) : Equiv.Perm (ι → F) where
  toFun v := Matrix.mulVec (A : Matrix ι ι F) (fun i => σ (v i))
  invFun v := fun i => σ.symm (Matrix.mulVec ((A⁻¹ : GL ι F) : Matrix ι ι F) v i)
  left_inv v := by
    funext i
    have h : Matrix.mulVec ((A⁻¹ : GL ι F) : Matrix ι ι F)
        (Matrix.mulVec (A : Matrix ι ι F) (fun j => σ (v j))) = fun j => σ (v j) := by
      rw [Matrix.mulVec_mulVec]
      simp
    simp [h]
  right_inv v := by
    funext i
    have h : Matrix.mulVec (A : Matrix ι ι F) (fun j => σ (σ.symm
        (Matrix.mulVec ((A⁻¹ : GL ι F) : Matrix ι ι F) v j))) = v := by
      simp only [RingEquiv.apply_symm_apply]
      rw [Matrix.mulVec_mulVec]
      simp
    exact congrFun h i

theorem semilinMap_mem (A : GL ι F) (σ : F ≃+* F) : semilinMap A σ ∈ semilinGroup F (ι → F) := by
  refine ⟨fun u v => ?_, σ, fun c v => ?_⟩
  · show Matrix.mulVec (A : Matrix ι ι F) (fun i => σ ((u + v) i)) =
      Matrix.mulVec (A : Matrix ι ι F) (fun i => σ (u i)) +
        Matrix.mulVec (A : Matrix ι ι F) (fun i => σ (v i))
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp
  · show Matrix.mulVec (A : Matrix ι ι F) (fun i => σ ((c • v) i)) =
      σ c • Matrix.mulVec (A : Matrix ι ι F) (fun i => σ (v i))
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp

end SemilinMap

end CFSG.LieType.ChevTwo.OppCl
