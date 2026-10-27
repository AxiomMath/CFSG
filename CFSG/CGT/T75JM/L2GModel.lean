module

public import CFSG.CGT.T75JM.L2GBasic

public section

namespace CFSG.CGT.T75JM

structure T1Model (H : Type*) [Group H] (n m : ℕ) where
  T0 : Subgroup H
  B0 : Subgroup H
  b0 : H
  d : Fin n → H
  d0 : Fin m → H
  theta : Fin m → Fin n → H
  b0_mem : b0 ∈ B0
  d_mem : ∀ i, d i ∈ Subgroup.normalizer (B0 : Set H)
  d0_mem : ∀ k, d0 k ∈ Subgroup.normalizer (B0 : Set H)
  theta_mem : ∀ k i, theta k i ∈ Subgroup.normalizer (B0 : Set H)
  inv_class : ∀ x : H, x * x = 1 → x ∉ T0 → ∃ n : H, n * b0 * n⁻¹ = x
  klein_class : ∀ B' : Subgroup H, b0 ∈ B' → (∀ x ∈ B', x * x = 1) → Nat.card B' = 4 →
    B' ⊓ T0 = ⊥ → Nat.card ↥(T0 ⊓ Subgroup.normalizer (B' : Set H)) = 4 →
    (∀ a ∈ T0 ⊓ Subgroup.normalizer (B' : Set H), ∀ x ∈ B', a * x = x * a) →
    (∀ b ∈ B', b ≠ 1 → ∀ y : H, y * b = b * y → y ∈ Subgroup.normalizer (B' : Set H)) →
    ∃ ι : H ≃* H, T0.map ι.toMonoidHom = T0 ∧ B0.map ι.toMonoidHom = B'
  swap : ∀ f : H → H,
    (∀ x ∈ Subgroup.normalizer (B0 : Set H), f x ∈ Subgroup.normalizer (B0 : Set H)) →
    (∀ x ∈ Subgroup.normalizer (B0 : Set H), ∀ y ∈ Subgroup.normalizer (B0 : Set H),
      f (x * y) = f x * f y) →
    (∀ x ∈ Subgroup.normalizer (B0 : Set H), ∀ y ∈ Subgroup.normalizer (B0 : Set H),
      f x = f y → x = y) →
    (∀ a ∈ Subgroup.normalizer (B0 : Set H), a ∈ T0 → f a ∈ B0) → (∀ b ∈ B0, f b ∈ T0) →
    ∃ e ∈ Subgroup.normalizer (B0 : Set H), ∃ k : Fin m, ∀ i, e * f (d i) * e⁻¹ = theta k i
  center : ∀ z : H, z ∈ Subgroup.normalizer (B0 : Set H) → (∀ i, z * d i = d i * z) → z = 1
  theta_sq : ∀ k, ∃ w : Fin n → List (Fin n × Bool), ∀ i,
    FreeGroup.lift d (FreeGroup.mk (w i)) = theta k i ∧
      FreeGroup.lift (theta k) (FreeGroup.mk (w i)) = d0 k * d i * (d0 k)⁻¹

structure OntoEmb (H : Type*) [Group H] {G : Type*} [Group G] (N : Subgroup G) where
  Φ : H →* G
  inj : Function.Injective Φ
  mem : ∀ x, Φ x ∈ N
  surj : ∀ g ∈ N, ∃ x, Φ x = g

namespace OntoEmb

variable {H : Type*} [Group H] {G : Type*} [Group G] {N : Subgroup G}

@[expose] def comp (E : OntoEmb H N) (ι : H ≃* H) : OntoEmb H N where
  Φ := E.Φ.comp ι.toMonoidHom
  inj := E.inj.comp ι.injective
  mem x := E.mem (ι x)
  surj g hg := by
    obtain ⟨x, hx⟩ := E.surj g hg
    exact ⟨ι.symm x, by simpa using hx⟩

@[simp] theorem comp_Φ_apply (E : OntoEmb H N) (ι : H ≃* H) (x : H) :
    (E.comp ι).Φ x = E.Φ (ι x) :=
  rfl

@[expose] def ofEquiv (ψ : H ≃* ↥N) : OntoEmb H N where
  Φ := N.subtype.comp ψ.toMonoidHom
  inj := Subtype.coe_injective.comp ψ.injective
  mem x := (ψ x).2
  surj g hg := ⟨ψ.symm ⟨g, hg⟩, by simp⟩

@[simp] theorem ofEquiv_Φ_apply (ψ : H ≃* ↥N) (x : H) : (ofEquiv ψ).Φ x = (ψ x : G) :=
  rfl

@[expose] noncomputable def toEquiv (E : OntoEmb H N) : H ≃* ↥N :=
  MulEquiv.ofBijective (E.Φ.codRestrict N E.mem)
    ⟨fun x y hxy => E.inj (congrArg Subtype.val hxy), fun ⟨g, hg⟩ => by
      obtain ⟨x, hx⟩ := E.surj g hg
      exact ⟨x, Subtype.ext hx⟩⟩

@[simp] theorem toEquiv_apply_coe (E : OntoEmb H N) (x : H) :
    ((E.toEquiv x : ↥N) : G) = E.Φ x :=
  rfl

end OntoEmb

end CFSG.CGT.T75JM
