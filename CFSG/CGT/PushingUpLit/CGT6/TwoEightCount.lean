module

public import Mathlib.FieldTheory.Finiteness
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightData
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Count

variable {F L : Type} [Field F] [AddCommGroup L] [Module F L] (D : Data F L)

@[expose] def Lam [CharP F 2] (K : Subgroup (Equiv.Perm (Wd F L))) : AddSubgroup L where
  carrier := {x | sigPerm D x ∈ K}
  zero_mem' := by
    show sigPerm D 0 ∈ K
    rw [sigPerm_zero]
    exact K.one_mem
  add_mem' := fun {x y} hx hy => by
    show sigPerm D (x + y) ∈ K
    rw [← sigPerm_mul]
    exact K.mul_mem hx hy
  neg_mem' := fun {x} hx => by
    show sigPerm D (-x) ∈ K
    rw [neg_eq_of_add_eq_zero_right (add_self_L F x)]
    exact hx

variable [CharP F 2]

theorem card_eq_card_Lam {K : Subgroup (Equiv.Perm (Wd F L))} (hK : K ≤ S0 D) :
    Nat.card K = Nat.card (Lam D K) := by
  refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
    (fun x : Lam D K => (⟨sigPerm D x, x.2⟩ : K)) ⟨?_, ?_⟩))
  · intro x y hxy
    exact Subtype.ext (sigPerm_injective D (congrArg Subtype.val hxy))
  · rintro ⟨g, hg⟩
    obtain ⟨x, rfl⟩ := hK hg
    exact ⟨⟨x, hg⟩, rfl⟩

theorem exists_ne_zero_of_ne_bot {K : Subgroup (Equiv.Perm (Wd F L))} (hK : K ≤ S0 D)
    (hne : K ≠ ⊥) : ∃ x ∈ Lam D K, x ≠ 0 := by
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨x, rfl⟩ := hK hg
  refine ⟨x, hg, fun h0 => hg1 ?_⟩
  apply Subtype.ext
  show sigPerm D x = 1
  rw [h0, sigPerm_zero]

@[expose] def Perp (Λ : AddSubgroup L) : Submodule F L where
  carrier := {y | ∀ x ∈ Λ, D.B x y = 0}
  zero_mem' := fun x _ => map_zero _
  add_mem' := fun {y y'} hy hy' x hx => by rw [map_add, hy x hx, hy' x hx, add_zero]
  smul_mem' := fun c y hy x hx => by rw [B_smul_right, hy x hx, mul_zero]

omit [CharP F 2] in
theorem mem_Perp {Λ : AddSubgroup L} {y : L} : y ∈ Perp D Λ ↔ ∀ x ∈ Λ, D.B x y = 0 := Iff.rfl

variable [Finite F] [Module.Finite F L] [Finite L]

omit [Finite F] [CharP F 2] in
theorem card_Lam_mul_card_Perp_le (Λ : AddSubgroup L) :
    Nat.card Λ * Nat.card (Perp D Λ) ≤ Nat.card L := by
  set U : Submodule F L := Submodule.span F (Λ : Set L) with hU
  have hperp : Perp D Λ = D.B.orthogonal U := by
    ext y
    rw [mem_Perp, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact h x hx
      | zero => exact LinearMap.map_zero₂ _ _
      | add x x' _ _ hx hx' => rw [LinearMap.map_add₂, hx, hx', add_zero]
      | smul c x _ hx => rw [LinearMap.map_smul₂, hx, smul_zero]
    · intro h x hx
      exact h x (Submodule.subset_span hx)
  have hfin : Module.finrank F U + Module.finrank F (D.B.orthogonal U) = Module.finrank F L := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal D.nondeg U
    have h2 : Module.finrank F U ≤ Module.finrank F L := Submodule.finrank_le U
    omega
  have hcard : Nat.card U * Nat.card (D.B.orthogonal U) = Nat.card L := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := U),
      Module.natCard_eq_pow_finrank (K := F) (V := D.B.orthogonal U),
      Module.natCard_eq_pow_finrank (K := F) (V := L), ← pow_add, hfin]
  have hle : Nat.card Λ ≤ Nat.card U := by
    refine Nat.card_le_card_of_injective (fun x : Λ => (⟨x.1, Submodule.subset_span x.2⟩ : U)) ?_
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : U => (z : L)) hxy
  rw [hperp]
  calc Nat.card Λ * Nat.card (D.B.orthogonal U) ≤ Nat.card U * Nat.card (D.B.orthogonal U) :=
        Nat.mul_le_mul_right _ hle
    _ = Nat.card L := hcard

omit [Finite F] [Module.Finite F L] [Finite L] in
theorem fix_mem_perp {K : Subgroup (Equiv.Perm (Wd F L))} (hK : K ≤ S0 D) (hne : K ≠ ⊥)
    {w : Wd F L} (hw : w ∈ Fix K) : w.2.2 = 0 ∧ w.2.1 ∈ Perp D (Lam D K) := by
  obtain ⟨x₁, hx₁, hx₁0⟩ := exists_ne_zero_of_ne_bot D hK hne
  have h1 : ∀ x ∈ Lam D K, sigFun D x w = w := fun x hx => hw _ hx
  have hs : w.2.2 = 0 := by
    have e := congrArg (fun u : Wd F L => u.2.1) (h1 x₁ hx₁)
    simp only [sigFun, add_eq_left] at e
    rcases smul_eq_zero.mp e with h0 | h0
    · exact h0
    · exact absurd h0 hx₁0
  refine ⟨hs, fun x hx => ?_⟩
  have e := congrArg (fun u : Wd F L => u.1) (h1 x hx)
  simp only [sigFun] at e
  rw [hs, mul_zero, add_zero] at e
  simpa using e

theorem card_mul_card_fix_le {K : Subgroup (Equiv.Perm (Wd F L))} (hK : K ≤ S0 D) (hne : K ≠ ⊥) :
    Nat.card K * Nat.card (Fix K) ≤ Nat.card F * Nat.card L := by
  have hinj : Function.Injective (fun w : Fix K =>
      ((w.1.1, (⟨w.1.2.1, (fix_mem_perp D hK hne w.2).2⟩ : Perp D (Lam D K))) :
        F × Perp D (Lam D K))) := by
    intro w w' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun z : F × Perp D (Lam D K) => (z.2 : L)) h
    refine Subtype.ext (Prod.ext h1 (Prod.ext h2 ?_))
    rw [(fix_mem_perp D hK hne w.2).1, (fix_mem_perp D hK hne w'.2).1]
  have h1 : Nat.card (Fix K) ≤ Nat.card F * Nat.card (Perp D (Lam D K)) := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective _ hinj
  rw [card_eq_card_Lam D hK]
  calc Nat.card (Lam D K) * Nat.card (Fix K)
      ≤ Nat.card (Lam D K) * (Nat.card F * Nat.card (Perp D (Lam D K))) :=
        Nat.mul_le_mul_left _ h1
    _ = Nat.card F * (Nat.card (Lam D K) * Nat.card (Perp D (Lam D K))) := by ring
    _ ≤ Nat.card F * Nat.card L := Nat.mul_le_mul_left _ (card_Lam_mul_card_Perp_le D _)

end Count

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
