module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Orb
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open scoped Pointwise
open MulAction

section Stab

variable {n : ℕ} {M : Subgroup (Equiv.Perm (Fin n))}

theorem stab_mem_iff {B : Finset (Fin n)} {g : ↥M} :
    g ∈ stabilizer ↥M B ↔ ∀ x : Fin n, g • x ∈ B ↔ x ∈ B := by
  rw [mem_stabilizer_iff]
  constructor
  · intro h x
    have := Finset.smul_mem_smul_finset_iff (a := g) (s := B) (b := x)
    rwa [h] at this
  · intro h
    ext y
    rw [← Finset.inv_smul_mem_iff]
    have := h (g⁻¹ • y)
    rw [smul_inv_smul] at this
    exact this.symm

theorem stab_of_fix {B : Finset (Fin n)} {g : ↥M} (h : ∀ x ∈ B, g • x = x) :
    g ∈ stabilizer ↥M B := by
  rw [stab_mem_iff]
  intro x
  constructor
  · intro hgx
    have h1 := h _ hgx
    have h2 : g • (g • x) = g • x := h1
    have h3 : g • x = x := MulAction.injective g h1
    rw [← h3]
    exact hgx
  · intro hx
    rw [h x hx]
    exact hx

@[expose] def blockRestr (B : Finset (Fin n)) :
    ↥(stabilizer ↥M B) →* Equiv.Perm {x // x ∈ B} where
  toFun k := Equiv.Perm.subtypePerm ((k : ↥M) : Equiv.Perm (Fin n))
    (fun x => stab_mem_iff.1 k.2 x)
  map_one' := by
    ext ⟨x, hx⟩
    rfl
  map_mul' a b := by
    ext ⟨x, hx⟩
    rfl

theorem blockRestr_eq_one_iff (B : Finset (Fin n)) (k : ↥(stabilizer ↥M B)) :
    blockRestr B k = 1 ↔ ∀ x ∈ B, (k : ↥M) • x = x := by
  constructor
  · intro h x hx
    have := congrArg (fun p : Equiv.Perm {x // x ∈ B} => (p ⟨x, hx⟩ : Fin n)) h
    have h' : ((k : ↥M) : Equiv.Perm (Fin n)) x = x := by simpa [blockRestr] using this
    exact h'
  · intro h
    apply Equiv.ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    exact h x hx

theorem exists_block_hom (B : Finset (Fin n)) {m : ℕ} (hB : B.card = m) :
    ∃ φ : ↥(stabilizer ↥M B) →* Equiv.Perm (Fin m),
      ∀ k, φ k = 1 ↔ ∀ x ∈ B, (k : ↥M) • x = x := by
  refine ⟨(Equiv.permCongrHom (Finset.equivFinOfCardEq hB)).toMonoidHom.comp (blockRestr B),
    fun k => ?_⟩
  rw [← blockRestr_eq_one_iff]
  exact map_eq_one_iff (Equiv.permCongrHom (Finset.equivFinOfCardEq hB))
    (Equiv.permCongrHom (Finset.equivFinOfCardEq hB)).injective

end Stab

section Orbit

variable {X : Type*} [Group X] {Ω : Type*} [MulAction X Ω]

theorem le_card_orbit [Finite Ω] [DecidableEq Ω] (Q : Subgroup X) {ks : List X}
    (hks : ∀ g ∈ ks, g ∈ Q) {x₀ : Ω} {O : List Ω} {par lab : List ℕ}
    (hR : Reach ks x₀ O par lab) (hnd : O.Nodup) :
    O.length ≤ Nat.card (MulAction.orbit ↥Q x₀) := by
  have hsub : ((O.toFinset : Finset Ω) : Set Ω) ⊆ MulAction.orbit ↥Q x₀ := by
    intro y hy
    obtain ⟨g, hg, hgy⟩ := hR.exists y (List.mem_toFinset.1 hy)
    have hgQ : g ∈ Q := by
      have : Subgroup.closure {g | g ∈ ks} ≤ Q := by
        rw [Subgroup.closure_le]
        exact fun g hg => hks g hg
      exact this hg
    exact ⟨⟨g, hgQ⟩, hgy⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd] at h1
  rw [Nat.card_coe_set_eq]
  exact h1

end Orbit

end CFSG.QuasithinUnique.Vol2Native.L239
