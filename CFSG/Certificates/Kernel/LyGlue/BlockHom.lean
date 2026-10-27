module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.KC.BlockHom

open Equiv Subgroup

variable {α β : Type*} [Finite α]

@[expose] def compat (O : Set α) (f : α → β) : Subgroup (Perm α × Perm β) where
  carrier := {p | ∀ a ∈ O, p.1 a ∈ O ∧ f (p.1 a) = p.2 (f a)}
  one_mem' := by
    intro a ha
    exact ⟨ha, rfl⟩
  mul_mem' := by
    intro p q hp hq a ha
    obtain ⟨m2, e2⟩ := hq a ha
    obtain ⟨m1, e1⟩ := hp _ m2
    refine ⟨m1, ?_⟩
    change f (p.1 (q.1 a)) = p.2 (q.2 (f a))
    rw [e1, e2]
  inv_mem' := by
    intro p hp a ha
    have hmaps : Set.MapsTo p.1 O O := fun b hb => (hp b hb).1
    have hbij : Set.BijOn p.1 O O :=
      ((Set.toFinite O).injOn_iff_bijOn_of_mapsTo hmaps).1 (p.1.injective.injOn)
    obtain ⟨b, hb, rfl⟩ := hbij.surjOn ha
    obtain ⟨-, e⟩ := hp b hb
    refine ⟨?_, ?_⟩
    · change p.1⁻¹ (p.1 b) ∈ O
      rw [Perm.inv_eq_iff_eq.2 rfl]
      exact hb
    · change f (p.1⁻¹ (p.1 b)) = p.2⁻¹ (f (p.1 b))
      rw [Perm.inv_eq_iff_eq.2 rfl, e, Perm.inv_eq_iff_eq.2 rfl]

theorem exists_hom {m : ℕ} (gs : ℕ → Perm α) (hs : ℕ → Perm β) (O : Set α) (f : α → β)
    (hc : ∀ k < m, ∀ a ∈ O, gs k a ∈ O ∧ f (gs k a) = hs k (f a))
    (hsurj : ∀ b, ∃ a ∈ O, f a = b) :
    ∃ φ : ↥(closure (gs '' {k | k < m})) →* ↥(closure (hs '' {k | k < m})),
      Function.Surjective φ ∧
      (∀ k (hk : k < m), (φ ⟨gs k, subset_closure ⟨k, hk, rfl⟩⟩ : Perm β) = hs k) ∧
      ∀ (g : ↥(closure (gs '' {k | k < m}))), ∀ a ∈ O,
        (g : Perm α) a ∈ O ∧ f ((g : Perm α) a) = (φ g : Perm β) (f a) := by
  classical
  set S : Set (Perm α × Perm β) := (fun k => (gs k, hs k)) '' {k | k < m} with hS
  set L : Subgroup (Perm α × Perm β) := closure S with hLdef
  have hL : L ≤ compat O f := by
    refine (closure_le _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    exact hc k hk
  have hfst : L.map (MonoidHom.fst (Perm α) (Perm β)) = closure (gs '' {k | k < m}) := by
    rw [hLdef, MonoidHom.map_closure, hS, Set.image_image]
    rfl
  have hsnd : L.map (MonoidHom.snd (Perm α) (Perm β)) = closure (hs '' {k | k < m}) := by
    rw [hLdef, MonoidHom.map_closure, hS, Set.image_image]
    rfl
  let π1 : ↥L →* Perm α := (MonoidHom.fst (Perm α) (Perm β)).domRestrict L
  have hinj : Function.Injective π1 := by
    intro x y hxy
    have h1 : (x * y⁻¹ : ↥L).1.1 = 1 := by
      change x.1.1 * (y.1.1)⁻¹ = 1
      have : x.1.1 = y.1.1 := hxy
      rw [this, mul_inv_cancel]
    have h2 : (x * y⁻¹ : ↥L).1.2 = 1 := by
      ext b
      obtain ⟨a, ha, rfl⟩ := hsurj b
      have := (hL (x * y⁻¹).2 a ha).2
      rw [h1] at this
      rw [← this]
      rfl
    have h3 : x * y⁻¹ = 1 := Subtype.ext (Prod.ext h1 h2)
    exact mul_inv_eq_one.1 h3
  have hrange : π1.range = closure (gs '' {k | k < m}) := by
    rw [← hfst, MonoidHom.restrict_range]
  let e : ↥L ≃* ↥(closure (gs '' {k | k < m})) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have he : ∀ x : ↥L, ((e x : ↥(closure (gs '' {k | k < m}))) : Perm α) = x.1.1 := fun _ => rfl
  have hmem2 : ∀ x : ↥L, x.1.2 ∈ closure (hs '' {k | k < m}) := by
    intro x
    rw [← hsnd]
    exact ⟨x.1, x.2, rfl⟩
  let ψ : ↥L →* ↥(closure (hs '' {k | k < m})) :=
    ((MonoidHom.snd (Perm α) (Perm β)).domRestrict L).codRestrict _ hmem2
  refine ⟨ψ.comp e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro y
    have hy : (y : Perm β) ∈ L.map (MonoidHom.snd (Perm α) (Perm β)) := by
      rw [hsnd]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨e ⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    change ((e.symm (e ⟨x, hx⟩)) : Perm α × Perm β).2 = y
    rw [e.symm_apply_apply]
    exact hxy
  · intro k hk
    have hx : (gs k, hs k) ∈ L := subset_closure ⟨k, hk, rfl⟩
    have : e.symm ⟨gs k, subset_closure ⟨k, hk, rfl⟩⟩ = ⟨(gs k, hs k), hx⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rfl
    change ((e.symm ⟨gs k, subset_closure ⟨k, hk, rfl⟩⟩ : ↥L) : Perm α × Perm β).2 = hs k
    rw [this]
  · intro g a ha
    have key := hL (e.symm g).2 a ha
    have hg : ((e.symm g : ↥L) : Perm α × Perm β).1 = g := by
      have := he (e.symm g)
      rw [e.apply_symm_apply] at this
      exact this.symm
    rw [← hg]
    exact ⟨key.1, key.2⟩

end CFSG.KC.BlockHom

end
