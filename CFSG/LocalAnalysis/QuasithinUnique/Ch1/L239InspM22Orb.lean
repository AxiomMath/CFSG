module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Data.List.GetD

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

section Orbit

variable {Γ : Type*} [Group Γ] {Ω : Type*} [MulAction Γ Ω]

@[expose] def Reach (gens : List Γ) (x₀ : Ω) (O : List Ω) (par lab : List ℕ) : Prop :=
  0 < O.length ∧ O.getD 0 x₀ = x₀ ∧ ∀ k < O.length, 0 < k → par.getD k 0 < k ∧
    O.getD k x₀ = gens.getD (lab.getD k 0) 1 • O.getD (par.getD k 0) x₀

@[expose] def ClosedUnder (gens : List Γ) (O : List Ω) : Prop :=
  ∀ x ∈ O, ∀ g ∈ gens, g • x ∈ O

@[expose] def AllMem {α : Type*} (L : List α) (p : α → Prop) : Prop := ∀ x ∈ L, p x

instance {α : Type*} (L : List α) (p : α → Prop) [DecidablePred p] : Decidable (AllMem L p) := by
  unfold AllMem
  exact List.decidableBAll p L

instance [DecidableEq Ω] (gens : List Γ) (x₀ : Ω) (O : List Ω) (par lab : List ℕ) :
    Decidable (Reach gens x₀ O par lab) := by
  unfold Reach
  infer_instance

instance [DecidableEq Ω] (gens : List Γ) (O : List Ω) : Decidable (ClosedUnder gens O) := by
  unfold ClosedUnder
  infer_instance

theorem Reach.exists {gens : List Γ} {x₀ : Ω} {O : List Ω} {par lab : List ℕ}
    (h : Reach gens x₀ O par lab) : ∀ y ∈ O, ∃ g ∈ Subgroup.closure {g | g ∈ gens}, g • x₀ = y := by
  obtain ⟨hpos, h0, hstep⟩ := h
  have key : ∀ k, k < O.length → ∃ g ∈ Subgroup.closure {g | g ∈ gens}, g • x₀ = O.getD k x₀ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst hk0
        exact ⟨1, Subgroup.one_mem _, by rw [h0, one_smul]⟩
      · obtain ⟨hp, he⟩ := hstep k hk (Nat.pos_of_ne_zero hk0)
        obtain ⟨g', hg', hg'x⟩ := ih (par.getD k 0) hp (hp.trans hk)
        have hgen : gens.getD (lab.getD k 0) 1 ∈ Subgroup.closure {g | g ∈ gens} := by
          by_cases hl : lab.getD k 0 < gens.length
          · rw [List.getD_eq_getElem gens 1 hl]
            exact Subgroup.subset_closure (List.getElem_mem hl)
          · rw [List.getD_eq_default _ _ (by omega)]
            exact Subgroup.one_mem _
        refine ⟨gens.getD (lab.getD k 0) 1 * g', Subgroup.mul_mem _ hgen hg', ?_⟩
        rw [mul_smul, hg'x, he]
  intro y hy
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  obtain ⟨g, hg, hgx⟩ := key k hk
  exact ⟨g, hg, by rw [hgx, List.getD_eq_getElem O x₀ hk]⟩

theorem ClosedUnder.closure {gens : List Γ} {O : List Ω} (h : ClosedUnder gens O) :
    ∀ g ∈ Subgroup.closure {g | g ∈ gens}, ∀ x ∈ O, g • x ∈ O := by
  classical
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact fun x hx => h x hx g hg
  | one => intro x hx; simpa using hx
  | mul a b _ _ ha hb =>
    intro x hx
    rw [mul_smul]
    exact ha _ (hb x hx)
  | inv a _ ha =>
    intro x hx
    have himg : (O.toFinset).image (fun y => a • y) ⊆ O.toFinset := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      exact List.mem_toFinset.2 (ha y (List.mem_toFinset.1 hy))
    have hinj : Function.Injective (fun y : Ω => a • y) := MulAction.injective a
    have hcard : (O.toFinset.image fun y => a • y).card = O.toFinset.card :=
      Finset.card_image_of_injective _ hinj
    have heq := Finset.eq_of_subset_of_card_le himg (le_of_eq hcard.symm)
    have hx' : x ∈ O.toFinset.image fun y => a • y := by
      rw [heq]
      exact List.mem_toFinset.2 hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hx'
    have : a⁻¹ • x = y := by rw [← hyx, inv_smul_smul]
    rw [this]
    exact List.mem_toFinset.1 hy

theorem orbit_eq_of_reach_closed {gens : List Γ} {x₀ : Ω} {O : List Ω} {par lab : List ℕ}
    (hgens : Subgroup.closure {g | g ∈ gens} = ⊤) (hR : Reach gens x₀ O par lab)
    (hC : ClosedUnder gens O) (y : Ω) : y ∈ MulAction.orbit Γ x₀ ↔ y ∈ O := by
  have hx₀ : x₀ ∈ O := by
    have := List.getElem_mem (l := O) hR.1
    rwa [← List.getD_eq_getElem O x₀ hR.1, hR.2.1] at this
  constructor
  · rintro ⟨g, rfl⟩
    exact hC.closure g (hgens ▸ Subgroup.mem_top g) x₀ hx₀
  · intro hy
    obtain ⟨g, -, hg⟩ := hR.exists y hy
    exact ⟨g, hg⟩

theorem Reach.sameOrbit {gens : List Γ} {x₀ : Ω} {O : List Ω} {par lab : List ℕ}
    (h : Reach gens x₀ O par lab) (Q : Subgroup Γ) (hQ : ∀ g ∈ gens, g ∈ Q) :
    ∀ B ∈ O, ∀ B' ∈ O, ∃ q ∈ Q, q • B = B' := by
  have hcl : Subgroup.closure {g | g ∈ gens} ≤ Q := by
    rw [Subgroup.closure_le]
    exact fun g hg => hQ g hg
  intro B hB B' hB'
  obtain ⟨g, hg, rfl⟩ := h.exists B hB
  obtain ⟨g', hg', rfl⟩ := h.exists B' hB'
  refine ⟨g' * g⁻¹, Q.mul_mem (hcl hg') (Q.inv_mem (hcl hg)), ?_⟩
  rw [mul_smul, inv_smul_smul]

theorem card_orbit_mul_card_stabilizer (x : Ω) :
    Nat.card (MulAction.orbit Γ x) * Nat.card (MulAction.stabilizer Γ x) = Nat.card Γ := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer Γ x),
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer Γ x)]

end Orbit

end CFSG.QuasithinUnique.Vol2Native.L239
