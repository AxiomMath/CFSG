module

public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module CategoryTheory Representation

namespace CFSG.FeitThompson

variable {G k V W X : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup X] [Module k X]

noncomputable def intertwiningMapCongrRight (ρ : Representation k G V)
    {σ : Representation k G W} {τ : Representation k G X} (e : σ.Equiv τ) :
    ρ.IntertwiningMap σ ≃ₗ[k] ρ.IntertwiningMap τ where
  toFun f := e.toIntertwiningMap.comp f
  map_add' f g := by ext v; simp
  map_smul' a f := by ext v; simp
  invFun f := e.symm.toIntertwiningMap.comp f
  left_inv f := by ext v; simp
  right_inv f := by ext v; simp

@[simp]
theorem intertwiningMapCongrRight_apply_apply {ρ : Representation k G V}
    {σ : Representation k G W} {τ : Representation k G X} (e : σ.Equiv τ)
    (f : ρ.IntertwiningMap σ) (v : V) :
    intertwiningMapCongrRight ρ e f v = e (f v) := (rfl)

theorem nonempty_equiv_of_intertwiningMap_ne_zero {ρ : Representation k G V}
    {σ : Representation k G W} [ρ.IsIrreducible] [σ.IsIrreducible] {f : ρ.IntertwiningMap σ}
    (hf : f ≠ 0) : Nonempty (ρ.Equiv σ) :=
  ⟨f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩

theorem intertwiningMap_eq_zero_of_isEmpty_equiv {ρ : Representation k G V}
    {σ : Representation k G W} [ρ.IsIrreducible] [σ.IsIrreducible] [IsEmpty (ρ.Equiv σ)]
    (f : ρ.IntertwiningMap σ) : f = 0 :=
  Subsingleton.elim _ _

open scoped Classical in
theorem finrank_intertwiningMap_of_isIrreducible [IsAlgClosed k]
    (ρ : Representation k G V) (σ : Representation k G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] [FiniteDimensional k V] [FiniteDimensional k W] :
    finrank k (ρ.IntertwiningMap σ) = if Nonempty (ρ.Equiv σ) then 1 else 0 := by
  by_cases h : Nonempty (ρ.Equiv σ)
  · obtain ⟨e⟩ := h
    rw [if_pos ⟨e⟩, ← (intertwiningMapCongrRight ρ e).finrank_eq,
      IsIrreducible.finrank_intertwiningMap_self]
  · rw [if_neg h]
    have : IsEmpty (ρ.Equiv σ) := not_nonempty_iff.mp h
    exact finrank_zero_of_subsingleton

theorem existsUnique_smul_of_isIrreducible [IsAlgClosed k] {ρ : Representation k G V}
    [ρ.IsIrreducible] [FiniteDimensional k V] (f : ρ.IntertwiningMap ρ) :
    ∃! a : k, ∀ v : V, f v = a • v := by
  obtain ⟨inj, surj⟩ :=
    IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)
  obtain ⟨a, ha⟩ := surj f
  refine ⟨a, fun v => by rw [← ha]; simp [Algebra.algebraMap_eq_smul_one], fun b hb => ?_⟩
  refine inj ?_
  rw [ha]
  ext v
  simp [Algebra.algebraMap_eq_smul_one, hb v]

theorem character_mem_irrChar {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {G : Type*} [Group G] (ρ : Representation k G V)
    (h : ρ.IsIrreducible) : ρ.character ∈ irrChar k G := by
  refine mem_irrChar.2 ⟨FDRep.of ρ, ?_, ?_⟩
  · rw [FDRep.of_ρ' ρ]; exact h
  · ext g; simp [FDRep.character, Representation.character, FDRep.of_ρ']

theorem mem_irrChar_conj {G : Type*} [Group G] {χ : G → k} (hχ : χ ∈ irrChar k G) (g h : G) :
    χ (h * g * h⁻¹) = χ g := irrChar_conj hχ g h

theorem exists_finrank_of_mem_irrChar {G : Type*} [Group G] {χ : G → k}
    (hχ : χ ∈ irrChar k G) : ∃ V : FDRep k G, χ 1 = finrank k V.V := by
  obtain ⟨V, -, rfl⟩ := mem_irrChar.1 hχ
  exact ⟨V, V.char_one⟩

end CFSG.FeitThompson
