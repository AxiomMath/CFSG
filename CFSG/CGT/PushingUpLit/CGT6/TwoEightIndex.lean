module

public import CFSG.CGT.PushingUpLit.CGT6.TwoEightLayer
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSemilinear

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Index

variable {F L : Type} [Field F] [AddCommGroup L] [Module F L] [CharP F 2] (D : Data F L)

open Classical in
@[expose] noncomputable def alphaOf (a : Equiv.Perm (Wd F L)) (x : L) : L :=
  if h : ∃ x', a * sigPerm D x * a⁻¹ = sigPerm D x' then h.choose else x

theorem alphaOf_spec {a : Equiv.Perm (Wd F L)} {x : L}
    (h : ∃ x', a * sigPerm D x * a⁻¹ = sigPerm D x') :
    a * sigPerm D x * a⁻¹ = sigPerm D (alphaOf D a x) := by
  classical
  unfold alphaOf
  split
  · exact ‹∃ x', a * sigPerm D x * a⁻¹ = sigPerm D x'›.choose_spec
  · exact absurd h ‹_›

theorem alphaOf_eq {a : Equiv.Perm (Wd F L)} {x x' : L} (h : a * sigPerm D x * a⁻¹ = sigPerm D x') :
    alphaOf D a x = x' :=
  sigPerm_injective D ((alphaOf_spec D ⟨x', h⟩).symm.trans h)

theorem alphaOf_one (x : L) : alphaOf D 1 x = x :=
  alphaOf_eq D (by simp)

theorem alphaOf_mul {a b : Equiv.Perm (Wd F L)}
    (ha : ∀ x, ∃ x', a * sigPerm D x * a⁻¹ = sigPerm D x')
    (hb : ∀ x, ∃ x', b * sigPerm D x * b⁻¹ = sigPerm D x') (x : L) :
    alphaOf D (a * b) x = alphaOf D a (alphaOf D b x) := by
  apply alphaOf_eq
  have h1 := alphaOf_spec D (hb x)
  have h2 := alphaOf_spec D (ha (alphaOf D b x))
  calc a * b * sigPerm D x * (a * b)⁻¹ = a * (b * sigPerm D x * b⁻¹) * a⁻¹ := by group
    _ = sigPerm D (alphaOf D a (alphaOf D b x)) := by rw [h1, h2]

theorem alphaOf_alphaOf {a : Equiv.Perm (Wd F L)} (hsq : a * a = 1)
    (ha : ∀ x, ∃ x', a * sigPerm D x * a⁻¹ = sigPerm D x') (x : L) :
    alphaOf D a (alphaOf D a x) = x := by
  have h := alphaOf_mul D ha ha x
  rw [hsq, alphaOf_one] at h
  exact h.symm

theorem normAdd_alphaOf {a : Equiv.Perm (Wd F L)} (hadd : IsAddPerm a) (hsq : a * a = 1)
    (ha : ∀ x, ∃ x', a * sigPerm D x * a⁻¹ = sigPerm D x') : NormAdd D a (alphaOf D a) := by
  have hinv : ∀ x, alphaOf D a (alphaOf D a x) = x := alphaOf_alphaOf D hsq ha
  refine ⟨hadd, fun x w => ?_, fun y => ⟨alphaOf D a y, hinv y⟩, fun x y hxy => ?_⟩
  · have h := alphaOf_spec D (ha x)
    have := congrArg (fun g : Equiv.Perm (Wd F L) => g (a w)) h
    have h3 : a⁻¹ (a w) = w := by simp
    simp only [Equiv.Perm.mul_apply, h3] at this
    exact this
  · have := congrArg (alphaOf D a) hxy
    rwa [hinv, hinv] at this

theorem alphaOf_zero {a : Equiv.Perm (Wd F L)} (hadd : IsAddPerm a) (hsq : a * a = 1)
    (ha : ∀ x, ∃ x', a * sigPerm D x * a⁻¹ = sigPerm D x') : alphaOf D a 0 = 0 :=
  (normAdd_alphaOf D hadd hsq ha).alpha_zero

theorem card_le_two_mul_inf_of_semilinear [Finite F] [Finite L] {K : Type} [Field K] [Finite K]
    [CharP K 2] [Module K L] {Ā : Subgroup (Equiv.Perm (Wd F L))}
    (hadd : ∀ a ∈ Ā, IsAddPerm a) (hsq : ∀ a ∈ Ā, a * a = 1)
    (hnormS : ∀ a ∈ Ā, ∀ x, ∃ x', a * sigPerm D x * a⁻¹ = sigPerm D x') {x₁ : L} (hx₁ : x₁ ≠ 0)
    (hsemi : ∀ a ∈ Ā, ∃ κ : K ≃+* K, ∀ (c : K) (x : L),
      alphaOf D a (c • x) = κ c • alphaOf D a x)
    (hker : ∀ a ∈ Ā, (∀ (c : K) (x : L), alphaOf D a (c • x) = c • alphaOf D a x) →
      a ∈ Subgroup.centralizer (S0 D : Set (Equiv.Perm (Wd F L)))) :
    Nat.card Ā ≤ 2 * Nat.card ↥(Ā ⊓ Subgroup.centralizer (S0 D : Set (Equiv.Perm (Wd F L)))) := by
  classical
  have hne : ∀ a ∈ Ā, alphaOf D a x₁ ≠ 0 := fun a ha h0 => by
    have h1 := alphaOf_zero D (hadd a ha) (hsq a ha) (hnormS a ha)
    have h2 := alphaOf_alphaOf D (hsq a ha) (hnormS a ha) x₁
    rw [h0, h1] at h2
    exact hx₁ h2.symm
  let κ : ↥Ā → (K ≃+* K) := fun a => (hsemi a.1 a.2).choose
  have hκ : ∀ (a : ↥Ā) (c : K) (x : L), alphaOf D a.1 (c • x) = κ a c • alphaOf D a.1 x :=
    fun a => (hsemi a.1 a.2).choose_spec
  have hκmul : ∀ a b : ↥Ā, κ (a * b) = κ a * κ b := by
    intro a b
    ext c
    have h1 : alphaOf D (a.1 * b.1) (c • x₁) = κ (a * b) c • alphaOf D (a.1 * b.1) x₁ :=
      hκ (a * b) c x₁
    have h2 : alphaOf D (a.1 * b.1) (c • x₁) = κ a (κ b c) • alphaOf D (a.1 * b.1) x₁ := by
      rw [alphaOf_mul D (hnormS a.1 a.2) (hnormS b.1 b.2), hκ b, hκ a,
        ← alphaOf_mul D (hnormS a.1 a.2) (hnormS b.1 b.2)]
    have h3 := h1.symm.trans h2
    have hne' : alphaOf D (a.1 * b.1) x₁ ≠ 0 := hne _ (a * b).2
    exact (smul_left_injective K hne' h3 : _)
  let φ : ↥Ā →* (K ≃+* K) := MonoidHom.mk' κ hκmul
  refine card_le_two_mul_inf_of_hom φ (fun a => Subtype.ext (hsq a.1 a.2)) ?_ ?_
  · intro x y hx hy hx1 hy1
    exact CFSG.QuasithinUnique.Setup.Offender.aut_involution_unique x y hx hy hx1 hy1
  · intro a ha1
    have hlin : ∀ (c : K) (x : L), alphaOf D a.1 (c • x) = c • alphaOf D a.1 x := by
      intro c x
      rw [hκ a c x]
      have : κ a = 1 := ha1
      rw [this]
      rfl
    exact hker a.1 a.2 hlin

end Index

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
