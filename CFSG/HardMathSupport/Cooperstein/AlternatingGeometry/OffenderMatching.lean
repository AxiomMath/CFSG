module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderShape
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IndexTwoBlockUniqueness
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

open Equiv Equiv.Perm MulAction

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {E : Subgroup (Perm Ω)}

theorem exists_other_of_card_two (hall : ∀ i : Ω, Nat.card (orbit E i) = 2) (x : Ω) :
    ∃ y, y ∈ orbit E x ∧ y ≠ x ∧ ∀ z ∈ orbit E x, z = x ∨ z = y := by
  have h := (Nat.card_eq_two_iff' (⟨x, mem_orbit_self x⟩ : orbit E x)).1 (hall x)
  obtain ⟨y, hy, huniq⟩ := h
  refine ⟨y.1, y.2, fun h => hy (Subtype.ext h), fun z hz => ?_⟩
  by_cases hzx : z = x
  · exact Or.inl hzx
  · right
    have := huniq ⟨z, hz⟩ (fun h => hzx (congrArg Subtype.val h))
    exact congrArg Subtype.val this

theorem exists_matching_of_orbits_two (hall : ∀ i : Ω, Nat.card (orbit E i) = 2)
    (hord : Nat.card (orbitStab E) ≤ 2 * Nat.card E) :
    ∃ σ : Perm Ω, (∀ x, σ x ≠ x) ∧ (∀ x, σ (σ x) = x) ∧ (∀ g ∈ E, ∀ x, g x = x ∨ g x = σ x) ∧
      ∃ c : Ω → Bool, (∀ x, c (σ x) = c x) ∧ (∀ x, c x = true ↔ swap x (σ x) ∉ E) ∧
        dblGroup σ c ≤ E := by
  classical
  choose σ0 hσorb hσne hσall using exists_other_of_card_two hall
  have hsymm : ∀ x, x ∈ orbit E (σ0 x) := by
    intro x
    have h1 : orbit E (σ0 x) = orbit E x := orbit_eq_iff.2 (hσorb x)
    rw [h1]; exact mem_orbit_self x
  have hinv : Function.Involutive σ0 := by
    intro x
    rcases hσall (σ0 x) x (hsymm x) with h | h
    · exact absurd h.symm (hσne x)
    · exact h.symm
  let σ : Perm Ω := hinv.toPerm
  have hσ : ∀ x, σ x = σ0 x := fun x => rfl
  have hswapmem : ∀ x, swap x (σ x) ∈ orbitStab E := by
    intro x z
    by_cases hz : z = x
    · rw [hz, swap_apply_left]; exact hσorb x
    · by_cases hz' : z = σ x
      · rw [hz', swap_apply_right]; exact hsymm x
      · rw [swap_apply_of_ne_of_ne hz hz']; exact mem_orbit_self z
  have hswap_comm : ∀ x, swap (σ x) (σ (σ x)) = swap x (σ x) := by
    intro x
    rw [show σ (σ x) = x from hinv x]; exact swap_comm _ _
  have hswap_sq : ∀ x, swap x (σ x) * swap x (σ x) = 1 := by
    intro x
    exact swap_mul_self _ _
  have key : ∀ x y, (swap x (σ x) ∈ E ↔ swap y (σ y) ∈ E) →
      swap x (σ x) * swap y (σ y) ∈ E := by
    intro x y hxy
    by_cases hx : swap x (σ x) ∈ E
    · exact E.mul_mem hx (hxy.1 hx)
    · have hy : swap y (σ y) ∉ E := fun h => hx (hxy.2 h)
      set J := orbitStab E with hJ
      have hle : E ≤ J := le_orbitStab
      have hidx : (E.subgroupOf J).index = 2 := by
        have hcard := Subgroup.card_mul_index (E.subgroupOf J)
        have hcE : Nat.card (E.subgroupOf J) = Nat.card E :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
        rw [hcE] at hcard
        have hpos : 0 < Nat.card E := Nat.card_pos
        have hne : (E.subgroupOf J).index ≠ 1 := by
          intro h1
          rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
          exact hx (h1 (hswapmem x))
        have hJpos : 0 < Nat.card J := Nat.card_pos
        have hne0 : (E.subgroupOf J).index ≠ 0 := by
          intro h0; rw [h0, mul_zero] at hcard; omega
        have hle2 : (E.subgroupOf J).index ≤ 2 := by
          by_contra hgt
          push Not at hgt
          have : Nat.card E * 3 ≤ Nat.card E * (E.subgroupOf J).index :=
            Nat.mul_le_mul_left _ hgt
          omega
        omega
      obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hidx
      let tx : J := ⟨swap x (σ x), hswapmem x⟩
      let ty : J := ⟨swap y (σ y), hswapmem y⟩
      have htx : tx ∉ E.subgroupOf J := hx
      have hty : ty ∉ E.subgroupOf J := hy
      have h1 : tx * a ∈ E.subgroupOf J := by
        have := ha tx
        rcases this with ⟨h, _⟩ | ⟨hb, _⟩
        · exact h
        · exact absurd hb htx
      have h2 : ty * a ∈ E.subgroupOf J := by
        have := ha ty
        rcases this with ⟨h, _⟩ | ⟨hb, _⟩
        · exact h
        · exact absurd hb hty
      have h3 : tx * ty ∈ E.subgroupOf J := by
        have := (E.subgroupOf J).mul_mem h1 ((E.subgroupOf J).inv_mem h2)
        have hty' : ty⁻¹ = ty := by
          apply Subtype.ext
          show (swap y (σ y))⁻¹ = swap y (σ y)
          exact inv_eq_of_mul_eq_one_right (hswap_sq y)
        have e : tx * a * (ty * a)⁻¹ = tx * ty := by
          rw [mul_inv_rev, mul_assoc, mul_inv_cancel_left, hty']
        rwa [e] at this
      exact h3
  refine ⟨σ, fun x => hσne x, hinv, ?_, fun x => if swap x (σ x) ∈ E then false else true, ?_, ?_, ?_⟩
  · intro g hg x
    rcases hσall x (g x) ⟨⟨g, hg⟩, rfl⟩ with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro x
    simp only [hswap_comm]
  · intro x
    by_cases h : swap x (σ x) ∈ E <;> simp [h]
  · unfold dblGroup
    rw [Subgroup.closure_le]
    rintro g ⟨x, y, -, -, hc, rfl⟩
    apply key
    by_cases hx : swap x (σ x) ∈ E <;> by_cases hy : swap y (σ y) ∈ E <;> simp_all
  
end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

end
