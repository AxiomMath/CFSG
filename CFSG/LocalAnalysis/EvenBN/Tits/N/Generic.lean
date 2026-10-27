module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open

section Generic

variable {Γ : Type*} [Group Γ]

@[expose] def centralizerMod (K W Y : Subgroup Γ) : Subgroup Γ where
  carrier := {g | g ∈ K ∧ g ∈ normalizer (W : Set Γ) ∧ ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ W}
  mul_mem' := by
    rintro g h ⟨hgK, hgN, hg⟩ ⟨hhK, hhN, hh⟩
    refine ⟨mul_mem hgK hhK, mul_mem hgN hhN, fun y hy => ?_⟩
    have e : g * h * y * (g * h)⁻¹ * y⁻¹ =
        g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹) := by group
    rw [e]
    refine mul_mem ?_ (hg y hy)
    exact (mem_normalizer_iff.1 hgN _).1 (hh y hy)
  one_mem' := ⟨one_mem _, one_mem _, fun y _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hgK, hgN, hg⟩
    refine ⟨inv_mem hgK, inv_mem hgN, fun y hy => ?_⟩
    have e : g⁻¹ * y * g⁻¹⁻¹ * y⁻¹ = g⁻¹ * (g * y * g⁻¹ * y⁻¹)⁻¹ * g := by group
    rw [e]
    exact (mem_normalizer_iff''.1 hgN _).1 (inv_mem (hg y hy))

@[expose] def conjActHom (S : Subgroup Γ) : ↥(normalizer (S : Set Γ)) →* MulAut ↥S where
  toFun h :=
    { toFun := fun v => ⟨(h : Γ) * v * (h : Γ)⁻¹, (mem_normalizer_iff.1 h.2 v).1 v.2⟩
      invFun := fun v => ⟨(h : Γ)⁻¹ * v * (h : Γ), (mem_normalizer_iff''.1 h.2 v).1 v.2⟩
      left_inv := fun v => Subtype.ext (by simp [mul_assoc])
      right_inv := fun v => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext v; simp
  map_mul' := fun a b => by ext v; simp [mul_assoc]

open Classical in
@[expose] noncomputable def actFun (S : Subgroup Γ) (g : Γ) : MulAut ↥S :=
  if h : g ∈ normalizer (S : Set Γ) then conjActHom S ⟨g, h⟩ else 1

@[expose] noncomputable def imgIn (S K : Subgroup Γ) : Subgroup (MulAut ↥S) :=
  (K.subgroupOf (normalizer (S : Set Γ))).map (conjActHom S)

@[expose] noncomputable def preIn (S : Subgroup Γ) (K : Subgroup (MulAut ↥S)) : Subgroup Γ :=
  (K.comap (conjActHom S)).map (normalizer (S : Set Γ)).subtype

@[expose] def maxElemAbelian2 (R : Subgroup Γ) : Set (Subgroup Γ) :=
  {E | E ≤ R ∧ IsElemAbelian 2 E ∧ ∀ D : Subgroup Γ, D ≤ R → IsElemAbelian 2 D →
    Nat.card D ≤ Nat.card E}

@[expose] def IsTransv (g : Γ) (Y : Subgroup Γ) (c : Γ) (axis : Subgroup Γ) : Prop :=
  axis ≤ Y ∧ c ∈ axis ∧ (∃ y ∈ Y, y ∉ axis) ∧
    ∀ y ∈ Y, (g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y * c) ∧ (g * y * g⁻¹ = y ↔ y ∈ axis)

@[expose] def IsElemAbQuot (K W : Subgroup Γ) (n : ℕ) : Prop :=
  W ≤ K ∧ (W.subgroupOf K).Normal ∧ (∀ k ∈ K, k * k ∈ W) ∧
    (∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ W) ∧ W.relIndex K = 2 ^ n

open Classical in
@[expose] noncomputable def elemOf (K : Subgroup Γ) (g : Γ) : ↥K := if h : g ∈ K then ⟨g, h⟩ else 1

end Generic

section GenericRk

variable {S : Type*} [Group S]

@[expose] def commImg (j : MulAut S) : Subgroup S := Subgroup.closure {x | ∃ w : S, x = w * (j w)⁻¹}

end GenericRk

end CFSG.LocalAnalysis.EvenBN.Tits.N
