module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.EvenSL

open Module

section Fix

variable {F : Type} [Field F] [Finite F] {X : Type} [AddCommGroup X] [Module F X]
  [Module.Finite F X] {T : Type} [Group T]

theorem even_natCard_of_charP_two [CharP F 2] : 2 ∣ Nat.card F := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self 2 n.ne_zero

theorem exists_fixed_ne_zero [CharP F 2] (hT : IsPGroup 2 T) (ρ : T →* Module.End F X)
    (hX : Nontrivial X) : ∃ x : X, x ≠ 0 ∧ ∀ t, ρ t x = x := by
  classical
  have : Finite X := Module.finite_of_finite F
  let _ : MulAction T X := MulAction.compHom X ρ
  have hsm : ∀ (t : T) (x : X), t • x = ρ t x := fun t x => rfl
  have hmod := hT.card_modEq_card_fixedPoints X
  have hpos : 0 < finrank F X := Module.finrank_pos
  have hXeven : 2 ∣ Nat.card X := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    exact (even_natCard_of_charP_two (F := F)).trans
      (dvd_pow_self _ hpos.ne')
  have hfix : Nat.card (MulAction.fixedPoints T X) % 2 = 0 := by
    have h := hmod
    unfold Nat.ModEq at h
    have := Nat.mod_eq_zero_of_dvd hXeven
    omega
  by_contra hcon
  push Not at hcon
  have hone : Nat.card (MulAction.fixedPoints T X) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨0, ?_⟩⟩⟩
    · by_contra hne
      have ha : (a : X) = 0 := by
        by_contra h
        obtain ⟨t, ht⟩ := hcon _ h
        exact ht (by rw [← hsm]; exact MulAction.mem_fixedPoints.1 a.2 t)
      have hb : (b : X) = 0 := by
        by_contra h
        obtain ⟨t, ht⟩ := hcon _ h
        exact ht (by rw [← hsm]; exact MulAction.mem_fixedPoints.1 b.2 t)
      exact hne (ha.trans hb.symm)
    · rw [MulAction.mem_fixedPoints]
      intro t
      rw [hsm, map_zero]
  rw [hone] at hfix
  omega

end Fix

section Quot

variable {F : Type} [Field F] {X : Type} [AddCommGroup X] [Module F X] {T : Type} [Group T]

@[expose] def qAct (ρ : T →* Module.End F X) (L : Submodule F X) (hL : ∀ t, L ≤ L.comap (ρ t)) :
    T →* Module.End F (X ⧸ L) where
  toFun t := L.mapQ L (ρ t) (hL t)
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_mul' s t := by
    apply Submodule.linearMap_qext
    ext x
    simp

theorem qAct_mk (ρ : T →* Module.End F X) (L : Submodule F X) (hL : ∀ t, L ≤ L.comap (ρ t))
    (t : T) (x : X) :
    qAct ρ L hL t (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ t x) := rfl

@[expose] def subAct (ρ : T →* Module.End F X) (W : Submodule F X) (hW : ∀ t, ∀ w ∈ W, ρ t w ∈ W) :
    T →* Module.End F W where
  toFun t := (ρ t).restrict (hW t)
  map_one' := by
    ext
    simp
  map_mul' s t := by
    ext
    simp

end Quot

section Comm

variable {F : Type} [Field F] [Finite F] [CharP F 2] {X : Type} [AddCommGroup X] [Module F X]
  [Module.Finite F X] {T : Type} [Group T]

theorem eq_one_of_finrank_eq_one (hT : IsPGroup 2 T) (ρ : T →* Module.End F X)
    (hX : finrank F X = 1) (t : T) : ρ t = 1 := by
  have : Nontrivial X := Module.nontrivial_of_finrank_eq_succ hX
  obtain ⟨x, hx, hfix⟩ := exists_fixed_ne_zero hT ρ ‹_›
  have hall := (finrank_eq_one_iff_of_nonzero' x hx).1 hX
  ext y
  obtain ⟨c, rfl⟩ := hall y
  simp [hfix t]

theorem comm_of_finrank_le_two (hT : IsPGroup 2 T) (ρ : T →* Module.End F X)
    (hX : finrank F X ≤ 2) (s t : T) : ρ s * ρ t = ρ t * ρ s := by
  rcases Nat.lt_or_ge (finrank F X) 2 with h | h
  · rcases Nat.lt_or_ge (finrank F X) 1 with h0 | h1
    · have : Subsingleton X := Module.finrank_zero_iff (R := F) |>.1 (by omega)
      exact Subsingleton.elim _ _
    · rw [eq_one_of_finrank_eq_one hT ρ (by omega) s, eq_one_of_finrank_eq_one hT ρ (by omega) t]
  · have h2 : finrank F X = 2 := by omega
    have : Nontrivial X := Module.nontrivial_of_finrank_pos (R := F) (by omega)
    obtain ⟨x, hx, hfix⟩ := exists_fixed_ne_zero hT ρ ‹_›
    set L : Submodule F X := Submodule.span F {x} with hLdef
    have hL : ∀ t, L ≤ L.comap (ρ t) := by
      intro t
      rw [hLdef, Submodule.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      show ρ t y ∈ L
      rw [hfix t]
      exact Submodule.subset_span rfl
    have hLrank : finrank F L = 1 := finrank_span_singleton hx
    have hQrank : finrank F (X ⧸ L) = 1 := by
      have := L.finrank_quotient_add_finrank
      omega
    have hq : ∀ t, qAct ρ L hL t = 1 := fun t => eq_one_of_finrank_eq_one hT _ hQrank t
    have hmem : ∀ t y, ρ t y - y ∈ L := by
      intro t y
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
      have := congrArg (fun f => f (Submodule.Quotient.mk y)) (hq t)
      simpa [qAct_mk] using this
    have hkey : ∀ t y, ∃ a : F, ρ t y = y + a • x := by
      intro t y
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hmem t y)
      exact ⟨a, by rw [ha]; abel⟩
    ext y
    obtain ⟨a, ha⟩ := hkey t y
    obtain ⟨b, hb⟩ := hkey s y
    simp only [Module.End.mul_apply]
    rw [ha, hb, map_add, map_add, map_smul, map_smul, hfix s, hfix t, ha, hb]
    module

end Comm

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.EvenSL
