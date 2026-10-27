module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Equiv

theorem mem_of_commute_of_abelian_transitive {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htrans : ∀ i j : Fin n, ∃ a ∈ A, a i = j)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ b ∈ A, σ * b = b * σ) : σ ∈ A := by
  rcases isEmpty_or_nonempty (Fin n) with hE | ⟨⟨i0⟩⟩
  · have h1 : σ = 1 := Equiv.ext fun x => isEmptyElim x
    rw [h1]
    exact A.one_mem
  obtain ⟨a, ha, hai⟩ := htrans i0 (σ i0)
  have hτ : ∀ b ∈ A, (a⁻¹ * σ) * b = b * (a⁻¹ * σ) := by
    intro b hb
    have hab : a⁻¹ * b = b * a⁻¹ := hcomm _ (A.inv_mem ha) _ hb
    calc (a⁻¹ * σ) * b = a⁻¹ * (σ * b) := by group
      _ = a⁻¹ * (b * σ) := by rw [hσ b hb]
      _ = (a⁻¹ * b) * σ := by group
      _ = (b * a⁻¹) * σ := by rw [hab]
      _ = b * (a⁻¹ * σ) := by group
  have hfix : (a⁻¹ * σ) i0 = i0 := by
    rw [Equiv.Perm.mul_apply, ← hai]
    simp
  have hid : a⁻¹ * σ = 1 := by
    refine Equiv.ext fun x => ?_
    obtain ⟨b, hb, hbx⟩ := htrans i0 x
    have hk : (a⁻¹ * σ) (b i0) = b ((a⁻¹ * σ) i0) :=
      congrArg (fun p : Equiv.Perm (Fin n) => p i0) (hτ b hb)
    rw [← hbx, hk, hfix, Equiv.Perm.one_apply]
  have hσa : σ = a := (inv_mul_eq_one.mp hid).symm
  rw [hσa]
  exact ha

variable {n : ℕ}

theorem conj_mem_of_normal {G A : Subgroup (Equiv.Perm (Fin n))} (hA : A ≤ G)
    (hAn : (A.subgroupOf G).Normal) (g : G) {a : Equiv.Perm (Fin n)} (ha : a ∈ A) :
    (g : Equiv.Perm (Fin n)) * a * (g : Equiv.Perm (Fin n))⁻¹ ∈ A := by
  have h := hAn.conj_mem (⟨a, hA ha⟩ : G) (Subgroup.mem_subgroupOf.mpr ha) g
  have h' := Subgroup.mem_subgroupOf.mp h
  simpa using h'

theorem conj_inv_mem_of_normal {G A : Subgroup (Equiv.Perm (Fin n))} (hA : A ≤ G)
    (hAn : (A.subgroupOf G).Normal) (g : G) {a : Equiv.Perm (Fin n)} (ha : a ∈ A) :
    (g : Equiv.Perm (Fin n))⁻¹ * a * (g : Equiv.Perm (Fin n)) ∈ A := by
  have h := conj_mem_of_normal hA hAn g⁻¹ ha
  simpa using h

@[expose] def conjAut {G A : Subgroup (Equiv.Perm (Fin n))} (hA : A ≤ G) (hAn : (A.subgroupOf G).Normal)
    (g : G) : MulAut A where
  toFun a := ⟨(g : Equiv.Perm (Fin n)) * a * (g : Equiv.Perm (Fin n))⁻¹,
    conj_mem_of_normal hA hAn g a.2⟩
  invFun a := ⟨(g : Equiv.Perm (Fin n))⁻¹ * a * (g : Equiv.Perm (Fin n)),
    conj_inv_mem_of_normal hA hAn g a.2⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[expose] def conjHom {G A : Subgroup (Equiv.Perm (Fin n))} (hA : A ≤ G)
    (hAn : (A.subgroupOf G).Normal) :
    G →* MulAut A where
  toFun g := conjAut hA hAn g
  map_one' := MulEquiv.ext fun a => Subtype.ext (by simp [conjAut])
  map_mul' g h := MulEquiv.ext fun a => Subtype.ext (by simp [conjAut, mul_assoc])

theorem card_le_of_abelian_transitive_normal
    (G A : Subgroup (Equiv.Perm (Fin n)))
    (hA : A ≤ G) (hAn : (A.subgroupOf G).Normal)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htrans : ∀ i j : Fin n, ∃ a ∈ A, a i = j) :
    Nat.card G ≤ Nat.card A * Nat.card (MulAut A) := by
  have : Finite (MulAut A) :=
    Finite.of_injective (fun f : MulAut A => f.toEquiv)
      (fun f g h => MulEquiv.ext fun x => congrArg (fun e : A ≃ A => e x) h)
  set φ := conjHom hA hAn with hφ
  have hkerA : ∀ g : G, g ∈ φ.ker → (g : Equiv.Perm (Fin n)) ∈ A := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    apply mem_of_commute_of_abelian_transitive A hcomm htrans
    intro b hb
    have := congrArg (fun f : MulAut A => ((f ⟨b, hb⟩ : A) : Equiv.Perm (Fin n))) hg
    simp [hφ, conjHom, conjAut, mul_assoc] at this
    calc (g : Equiv.Perm (Fin n)) * b
        = ((g : Equiv.Perm (Fin n)) * (b * (g : Equiv.Perm (Fin n))⁻¹)) * (g : Equiv.Perm (Fin n)) := by
          group
      _ = b * (g : Equiv.Perm (Fin n)) := by rw [this]
  have hinj : Function.Injective
      (fun x : φ.ker => (⟨((x.1 : G) : Equiv.Perm (Fin n)), hkerA x.1 x.2⟩ : A)) := by
    intro x y h
    have h2 : ((x.1 : G) : Equiv.Perm (Fin n)) = ((y.1 : G) : Equiv.Perm (Fin n)) :=
      congrArg (fun z : A => (z : Equiv.Perm (Fin n))) h
    exact Subtype.ext (Subtype.ext h2)
  have hkerle : Nat.card φ.ker ≤ Nat.card A := Nat.card_le_card_of_injective _ hinj
  have hrange : Nat.card φ.range ≤ Nat.card (MulAut A) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have hidx : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
  calc Nat.card G = Nat.card φ.ker * φ.ker.index := (Subgroup.card_mul_index _).symm
    _ ≤ Nat.card A * Nat.card (MulAut A) := by
      rw [hidx]
      exact Nat.mul_le_mul hkerle hrange

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
