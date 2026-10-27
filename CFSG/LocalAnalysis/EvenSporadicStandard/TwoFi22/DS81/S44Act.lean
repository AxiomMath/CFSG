module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

open Subgroup

variable {G : Type} [Group G] {E : Subgroup G}

theorem conj_mem_of_mem_normalizer {n : G} (hn : n ∈ normalizer (E : Set G)) {e : G}
    (he : e ∈ E) : n * e * n⁻¹ ∈ E :=
  (mem_normalizer_iff.1 hn e).1 he

theorem inv_conj_mem_of_mem_normalizer {n : G} (hn : n ∈ normalizer (E : Set G)) {e : G}
    (he : e ∈ E) : n⁻¹ * e * n ∈ E := by
  have := conj_mem_of_mem_normalizer (inv_mem hn) he
  simpa using this

@[expose] def conjE {E : Subgroup G} (n : G) (hn : n ∈ normalizer (E : Set G)) : MulAut E where
  toFun e := ⟨n * e * n⁻¹, conj_mem_of_mem_normalizer hn e.2⟩
  invFun e := ⟨n⁻¹ * e * n, inv_conj_mem_of_mem_normalizer hn e.2⟩
  left_inv e := Subtype.ext (by simp [mul_assoc])
  right_inv e := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[expose] def actN (E : Subgroup G) : ↥(normalizer (E : Set G)) →* MulAut E where
  toFun n := conjE n.1 n.2
  map_one' := MulEquiv.ext fun e => Subtype.ext (by simp [conjE])
  map_mul' a b := MulEquiv.ext fun e => Subtype.ext (by simp [conjE, mul_assoc])


theorem actN_apply (n : ↥(normalizer (E : Set G))) (e : E) :
    ((actN E n e : E) : G) = n * e * (n : G)⁻¹ := rfl

theorem mem_ker_actN {n : ↥(normalizer (E : Set G))} :
    n ∈ (actN E).ker ↔ ∀ e ∈ E, (n : G) * e * (n : G)⁻¹ = e := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h e he
    have := congrArg Subtype.val (MulEquiv.congr_fun h ⟨e, he⟩)
    simpa [actN_apply] using this
  · intro h
    refine MulEquiv.ext fun e => Subtype.ext ?_
    simpa [actN_apply] using h e e.2

theorem mem_ker_actN_iff_mem_centralizer {n : ↥(normalizer (E : Set G))} :
    n ∈ (actN E).ker ↔ (n : G) ∈ centralizer (E : Set G) := by
  rw [mem_ker_actN, mem_centralizer_iff]
  constructor
  · intro h g hg
    have := h g hg
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro h e he
    have := h e he
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm

theorem card_map_mul_card_ker {A B : Type} [Group A] [Group B] (f : A →* B) (S : Subgroup A)
    (hS : f.ker ≤ S) : Nat.card (S.map f) * Nat.card f.ker = Nat.card S := by
  set g : S →* B := f.domRestrict S with hg
  have h1 : g.range = S.map f := MonoidHom.domRestrict_range S f
  have h2 : g.ker = f.ker.subgroupOf S := MonoidHom.ker_domRestrict S f
  have h3 : Nat.card g.ker = Nat.card f.ker := by
    rw [h2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  have h4 := Subgroup.card_mul_index g.ker
  rw [Subgroup.index_ker, h1, h3] at h4
  rw [mul_comm]
  exact h4

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44
