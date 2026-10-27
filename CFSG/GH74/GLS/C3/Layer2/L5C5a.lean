module

public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

universe u

structure Ext2Data (H : Type u) [Group H] where
  α : H ≃* H
  u : H
  sq : ∀ h, α (α h) = u * h * u⁻¹
  fix : α u = u

@[ext] structure Ext2 {H : Type u} [Group H] (D : Ext2Data H) : Type u where
  fst : H
  snd : Bool

namespace Ext2

variable {H : Type u} [Group H] {D : Ext2Data H}

@[expose] def equivProd : Ext2 D ≃ H × Bool where
  toFun a := (a.fst, a.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [DecidableEq H] : DecidableEq (Ext2 D) := fun a b =>
  decidable_of_iff (a.fst = b.fst ∧ a.snd = b.snd)
    ⟨fun h => Ext2.ext h.1 h.2, fun h => by rw [h]; exact ⟨rfl, rfl⟩⟩

instance [Finite H] : Finite (Ext2 D) := Finite.of_equiv _ equivProd.symm

instance : Mul (Ext2 D) where
  mul a b := match a, b with
    | ⟨x, false⟩, ⟨y, false⟩ => ⟨x * y, false⟩
    | ⟨x, false⟩, ⟨y, true⟩ => ⟨x * y, true⟩
    | ⟨x, true⟩, ⟨y, false⟩ => ⟨x * D.α y, true⟩
    | ⟨x, true⟩, ⟨y, true⟩ => ⟨x * D.α y * D.u, false⟩

instance : One (Ext2 D) := ⟨⟨1, false⟩⟩

instance : Inv (Ext2 D) where
  inv a := match a with
    | ⟨x, false⟩ => ⟨x⁻¹, false⟩
    | ⟨x, true⟩ => ⟨D.u⁻¹ * D.α x⁻¹, true⟩

theorem mul_ff (x y : H) : (⟨x, false⟩ : Ext2 D) * ⟨y, false⟩ = ⟨x * y, false⟩ := rfl

theorem mul_ft (x y : H) : (⟨x, false⟩ : Ext2 D) * ⟨y, true⟩ = ⟨x * y, true⟩ := rfl

theorem mul_tf (x y : H) : (⟨x, true⟩ : Ext2 D) * ⟨y, false⟩ = ⟨x * D.α y, true⟩ := rfl

theorem mul_tt (x y : H) : (⟨x, true⟩ : Ext2 D) * ⟨y, true⟩ = ⟨x * D.α y * D.u, false⟩ := rfl

theorem one_def : (1 : Ext2 D) = ⟨1, false⟩ := rfl

theorem inv_f (x : H) : (⟨x, false⟩ : Ext2 D)⁻¹ = ⟨x⁻¹, false⟩ := rfl

theorem inv_t (x : H) : (⟨x, true⟩ : Ext2 D)⁻¹ = ⟨D.u⁻¹ * D.α x⁻¹, true⟩ := rfl

theorem mul_assoc' (a b c : Ext2 D) : a * b * c = a * (b * c) := by
  obtain ⟨x, e⟩ := a
  obtain ⟨y, f⟩ := b
  obtain ⟨z, g⟩ := c
  cases e <;> cases f <;> cases g <;>
    simp only [mul_ff, mul_ft, mul_tf, mul_tt] <;> refine Ext2.ext ?_ rfl <;>
    simp only [map_mul, D.sq, D.fix] <;> group

theorem one_mul' (a : Ext2 D) : 1 * a = a := by
  obtain ⟨x, e⟩ := a
  cases e <;> simp [one_def, mul_ff, mul_ft]

theorem inv_mul_cancel' (a : Ext2 D) : a⁻¹ * a = 1 := by
  obtain ⟨x, e⟩ := a
  cases e
  · simp [inv_f, mul_ff, one_def]
  · rw [inv_t, mul_tt, one_def]
    refine Ext2.ext ?_ rfl
    simp [map_inv]

instance instGroup : Group (Ext2 D) :=
  Group.ofLeftAxioms mul_assoc' one_mul' inv_mul_cancel'

@[expose] def inc : H →* Ext2 D :=
  MonoidHom.mk' (fun h => (⟨h, false⟩ : Ext2 D)) (fun _ _ => rfl)

@[simp] theorem inc_fst (h : H) : (inc (D := D) h).fst = h := rfl

@[simp] theorem inc_snd (h : H) : (inc (D := D) h).snd = false := rfl

theorem inc_injective : Function.Injective (inc (D := D)) := fun _ _ h => congrArg Ext2.fst h

theorem mem_range_inc {a : Ext2 D} : a ∈ (inc (D := D)).range ↔ a.snd = false := by
  constructor
  · rintro ⟨h, rfl⟩
    rfl
  · intro h
    exact ⟨a.fst, Ext2.ext rfl h.symm⟩

end Ext2

theorem Ext2.recognize {S : Type*} [Group S] {H : Type u} [Group H] (D : Ext2Data H)
    (κ : H →* S) (hκ : Function.Injective κ) (hidx : κ.range.index = 2) (b : S)
    (hb : b ∉ κ.range) (hα : ∀ h, κ (D.α h) = b * κ h * b⁻¹) (hu : κ D.u = b * b) :
    ∃ ψ : S ≃* Ext2 D, ∀ g, ψ (κ g) = Ext2.inc g := by
  let Φ : Ext2 D →* S := MonoidHom.mk'
    (fun a => κ a.fst * (if a.snd then b else 1)) (by
      rintro ⟨x, e⟩ ⟨y, f⟩
      cases e <;> cases f <;>
        simp only [Ext2.mul_ff, Ext2.mul_ft, Ext2.mul_tf, Ext2.mul_tt, map_mul, hα, hu,
          ite_true, ite_false, Bool.false_eq_true, mul_one] <;> group)
  have hΦ : ∀ a, Φ a = κ a.fst * (if a.snd then b else 1) := fun a => rfl
  have hbi : b⁻¹ ∉ κ.range := fun h => hb (by simpa using inv_mem h)
  have hmem : ∀ s : S, s ∈ κ.range ∨ s * b⁻¹ ∈ κ.range := by
    intro s
    by_cases hs : s ∈ κ.range
    · exact Or.inl hs
    · refine Or.inr ?_
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      simp [hs, hbi]
  have hinj : Function.Injective Φ := by
    rintro ⟨x, e⟩ ⟨y, f⟩ h
    simp only [hΦ] at h
    cases e <;> cases f
    · simp only [Bool.false_eq_true, ite_false, mul_one] at h
      exact Ext2.ext (hκ h) rfl
    · simp only [Bool.false_eq_true, ite_false, mul_one, ite_true] at h
      exfalso
      apply hb
      have : b = κ (y⁻¹ * x) := by rw [map_mul, map_inv, h]; group
      rw [this]
      exact ⟨_, rfl⟩
    · simp only [Bool.false_eq_true, ite_false, mul_one, ite_true] at h
      exfalso
      apply hb
      have : b = κ (x⁻¹ * y) := by rw [map_mul, map_inv, ← h]; group
      rw [this]
      exact ⟨_, rfl⟩
    · simp only [ite_true] at h
      exact Ext2.ext (hκ (mul_right_cancel h)) rfl
  have hsurj : Function.Surjective Φ := by
    intro s
    rcases hmem s with ⟨x, rfl⟩ | ⟨x, hx⟩
    · exact ⟨⟨x, false⟩, by simp [hΦ]⟩
    · exact ⟨⟨x, true⟩, by simp [hΦ, hx]⟩
  let e : Ext2 D ≃* S := MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  refine ⟨e.symm, fun g => ?_⟩
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  show κ g = Φ (Ext2.inc g)
  rw [hΦ]
  simp [Ext2.inc]

end CFSG.GH74.GLS.C3.Layer2.L5
