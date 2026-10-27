module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Second
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterFusion
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

@[expose] def TwoSubgroupsAbelian (X : Type*) [Group X] : Prop :=
  ∀ P : Subgroup X, IsPGroup 2 P → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x

@[expose] def ElemBound (b : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ E : Subgroup X, (∀ x ∈ E, x * x = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ b

@[expose] def LamLike (b : ℕ) (X : Type*) [Group X] : Prop :=
  Group.IsSolvable X ∧ TwoSubgroupsAbelian X ∧ ElemBound b X

theorem TwoSubgroupsAbelian.of_injective {X Y : Type*} [Group X] [Group Y]
    (h : TwoSubgroupsAbelian Y) {f : X →* Y} (hf : Function.Injective f) :
    TwoSubgroupsAbelian X := by
  intro P hP x hx y hy
  have := h (P.map f) (hP.map f) (f x) ⟨x, hx, rfl⟩ (f y) ⟨y, hy, rfl⟩
  exact hf (by simpa [map_mul] using this)

theorem ElemBound.of_injective {b : ℕ} {X Y : Type*} [Group X] [Group Y] (h : ElemBound b Y)
    {f : X →* Y} (hf : Function.Injective f) : ElemBound b X := by
  intro E h2 hc
  have hcard : Nat.card (E.map f) = Nat.card E := Subgroup.card_map_of_injective hf
  rw [← hcard]
  refine h _ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, h2 x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]

theorem LamLike.of_injective {b : ℕ} {X Y : Type*} [Group X] [Group Y] (h : LamLike b Y)
    {f : X →* Y} (hf : Function.Injective f) : LamLike b X := by
  obtain ⟨hs, ha, hb⟩ := h
  exact ⟨Group.isSolvable_of_isSolvable_injective hf, ha.of_injective hf, hb.of_injective hf⟩

theorem inl_injective' (A B : Type*) [Group A] [Group B] : Function.Injective (MonoidHom.inl A B) :=
  fun _ _ h => (Prod.mk.inj h).1

@[expose] def NoFixedEmbeds (K : Type) [Group K] (Λ : Type*) [Group Λ] : Prop :=
  ∀ α : MulAut K, α ≠ 1 → α * α = 1 →
    (¬ ∃ f : ↥(fixSubgroup α) × Multiplicative (ZMod 2) →* Λ, Function.Injective f) ∧
      ((∃ k : K, α = MulAut.conj k) → ¬ ∃ f : ↥(fixSubgroup α) →* Λ, Function.Injective f)

@[expose] def InvolutionFixesNotLam (K : Type) [Group K] (b : ℕ) : Prop :=
  ∀ α : MulAut K, α ≠ 1 → α * α = 1 →
    ¬ LamLike b (↥(fixSubgroup α) × Multiplicative (ZMod 2)) ∧
      ((∃ k : K, α = MulAut.conj k) → ¬ LamLike b ↥(fixSubgroup α))

theorem NoFixedEmbeds.of_lamLike {K : Type} [Group K] {b : ℕ} {Λ : Type*} [Group Λ]
    (hK : InvolutionFixesNotLam K b) (hΛ : LamLike b Λ) : NoFixedEmbeds K Λ :=
  fun α h1 h2 =>
    ⟨fun ⟨_, hf⟩ => (hK α h1 h2).1 (hΛ.of_injective hf),
      fun hin ⟨_, hf⟩ => (hK α h1 h2).2 hin (hΛ.of_injective hf)⟩

theorem not_elemBound_fixSubgroup {K : Type} [Group K] {n b : ℕ} (hK : InvolutionFixesElem K n)
    (hbn : b < n) {α : MulAut K} (h1 : α ≠ 1) (h2 : α * α = 1) :
    ¬ ElemBound b ↥(fixSubgroup α) := by
  intro hb
  obtain ⟨E, hEfix, hE2, hEc, hEn⟩ := hK α h1 h2
  have hle : E ≤ fixSubgroup α := fun x hx => hEfix x hx
  have hcard : Nat.card (E.subgroupOf (fixSubgroup α)) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h := hb (E.subgroupOf (fixSubgroup α))
    (fun x hx => Subtype.ext (hE2 x hx)) (fun x hx y hy => Subtype.ext (hEc x hx y hy))
  omega

theorem not_elemBound_fixProd {K : Type} [Group K] {n b : ℕ} (hK : InvolutionFixesElem K n)
    (hbn : b < n) {α : MulAut K} (h1 : α ≠ 1) (h2 : α * α = 1) :
    ¬ ElemBound b (↥(fixSubgroup α) × Multiplicative (ZMod 2)) := fun hb =>
  not_elemBound_fixSubgroup hK hbn h1 h2 (hb.of_injective (f := MonoidHom.inl _ _)
    (inl_injective' _ _))

theorem NoFixedEmbeds.of_nonsolvable {K : Type} [Group K] {Λ : Type*} [Group Λ]
    (hK : ∀ α : MulAut K, α ≠ 1 → α * α = 1 → ¬ Group.IsSolvable ↥(fixSubgroup α))
    (hΛ : Group.IsSolvable Λ) : NoFixedEmbeds K Λ :=
  fun α h1 h2 =>
    ⟨fun ⟨f, hf⟩ => hK α h1 h2 (Group.isSolvable_of_isSolvable_injective
        (f := f.comp (MonoidHom.inl _ _)) (hf.comp (inl_injective' _ _))),
      fun _ ⟨_, hf⟩ => hK α h1 h2 (Group.isSolvable_of_isSolvable_injective hf)⟩

end CFSG.EvenSporadicStandard.Induction
