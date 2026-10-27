module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Orb
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open scoped Pointwise

section BFS

variable {Γ : Type*} [Group Γ] {Ω : Type*} [MulAction Γ Ω] {E : Type*} [BEq E] [Hashable E]

structure BfsState (Ω E : Type*) [BEq E] [Hashable E] where
  O : Array Ω
  par : Array ℕ
  lab : Array ℕ
  seen : Std.HashSet E

@[expose] def bfsLoop (nrm : Ω → Ω) (enc : Ω → E) (gens : List Γ) :
    ℕ → ℕ → BfsState Ω E → BfsState Ω E
  | 0, _, st => st
  | f + 1, i, st =>
    if h : i < st.O.size then
      let x := st.O[i]
      bfsLoop nrm enc gens f (i + 1)
        ((List.range gens.length).foldl (fun (st : BfsState Ω E) j =>
          if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
          else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
            st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩) st)
    else st

@[expose] def bfsOrbit (nrm : Ω → Ω) (enc : Ω → E) (gens : List Γ) (x₀ : Ω) (fuel : ℕ) :
    List Ω × List ℕ × List ℕ :=
  let st := bfsLoop nrm enc gens fuel 0 ⟨#[x₀], #[0], #[0], (∅ : Std.HashSet E).insert (enc x₀)⟩
  (st.O.toList, st.par.toList, st.lab.toList)

end BFS

section Bound

variable {Γ : Type*} [Group Γ] {Ω : Type*} [MulAction Γ Ω]

theorem card_stab_mul_le [Finite Γ] {gens : List Γ} {x₀ : Ω} {O : List Ω} {par lab : List ℕ}
    (hR : Reach gens x₀ O par lab) (hnd : O.Nodup) :
    Nat.card (MulAction.stabilizer Γ x₀) * O.length ≤ Nat.card Γ := by
  classical
  have hsub : ∀ y ∈ O, y ∈ MulAction.orbit Γ x₀ := by
    intro y hy
    obtain ⟨g, -, hg⟩ := hR.exists y hy
    exact ⟨g, hg⟩
  have hfin : (MulAction.orbit Γ x₀).Finite := Set.finite_range _
  have : Finite (MulAction.orbit Γ x₀) := hfin.to_subtype
  have h1 : O.length ≤ Nat.card (MulAction.orbit Γ x₀) := by
    have h2 : (↑O.toFinset : Set Ω) ⊆ MulAction.orbit Γ x₀ := fun y hy =>
      hsub y (List.mem_toFinset.1 hy)
    have h3 := Set.ncard_le_ncard h2 (Set.toFinite _)
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, ← Nat.card_coe_set_eq] at h3
    exact h3
  calc Nat.card (MulAction.stabilizer Γ x₀) * O.length
      ≤ Nat.card (MulAction.stabilizer Γ x₀) * Nat.card (MulAction.orbit Γ x₀) :=
        Nat.mul_le_mul_left _ h1
    _ = Nat.card (MulAction.orbit Γ x₀) * Nat.card (MulAction.stabilizer Γ x₀) := mul_comm _ _
    _ = Nat.card Γ := card_orbit_mul_card_stabilizer x₀

theorem card_centralizer_mul_le {X : Type*} [Group X] [Finite X] {gens : List (ConjAct X)}
    {z : X} {O : List X} {par lab : List ℕ} (hR : Reach gens z O par lab) (hnd : O.Nodup) :
    Nat.card {x : X // x * z * x⁻¹ = z} * O.length ≤ Nat.card X := by
  have : Finite (ConjAct X) := inferInstanceAs (Finite X)
  have h := card_stab_mul_le hR hnd
  have e1 : Nat.card {x : X // x * z * x⁻¹ = z} =
      Nat.card (MulAction.stabilizer (ConjAct X) z) := by
    refine Nat.card_congr ?_
    exact (ConjAct.toConjAct.toEquiv.subtypeEquiv fun x => by
      simp [MulAction.mem_stabilizer_iff, ConjAct.smul_def])
  have e2 : Nat.card (ConjAct X) = Nat.card X := Nat.card_congr ConjAct.ofConjAct.toEquiv
  rw [e1]
  rw [e2] at h
  exact h

end Bound

section Partition

variable {X : Type*} [Group X] {n : ℕ} [MulAction X (Fin n)]

theorem smul_partition_eq (A : Subgroup X) (τ : Finset (Finset (Fin n)))
    (orbF : Fin n → Finset (Fin n)) (horb : ∀ i j, j ∈ orbF i ↔ ∃ a ∈ A, a • i = j)
    (hτ : ∀ i, orbF i ∈ τ) (hτ' : ∀ B ∈ τ, ∃ i, orbF i = B) {x : X}
    (hx : x ∈ Subgroup.normalizer (A : Set X)) : x • τ = τ := by
  classical
  have hxn := Subgroup.mem_normalizer_iff.1 hx
  have key : ∀ i, x • orbF i = orbF (x • i) := by
    intro i
    ext j
    rw [← Finset.inv_smul_mem_iff, horb, horb]
    constructor
    · rintro ⟨a, ha, hai⟩
      refine ⟨x * a * x⁻¹, (hxn a).1 ha, ?_⟩
      calc (x * a * x⁻¹) • x • i = x • a • i := by simp [mul_smul]
        _ = j := by rw [hai]; simp
    · rintro ⟨a, ha, hai⟩
      refine ⟨x⁻¹ * a * x, ?_, ?_⟩
      · rw [hxn]
        simpa [mul_assoc] using ha
      · calc (x⁻¹ * a * x) • i = x⁻¹ • a • x • i := by simp [mul_smul]
          _ = x⁻¹ • j := by rw [hai]
  have hsub : x • τ ⊆ τ := by
    intro B hB
    obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_smul_finset.1 hB
    obtain ⟨i, rfl⟩ := hτ' B₀ hB₀
    rw [key]
    exact hτ _
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])

end Partition

end CFSG.QuasithinUnique.Vol2Native.L239
