module

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Group
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Certificates.DceTw

variable {G : Type*} [Group G] {N : Subgroup G}

@[expose] def RelT (N : Subgroup G) (a b : G) : Prop := a * b⁻¹ ∈ N

theorem RelT.refl (a : G) : RelT N a a := by
  unfold RelT
  rw [mul_inv_cancel]
  exact N.one_mem

theorem RelT.of_eq {a b : G} (h : a = b) : RelT N a b := h ▸ RelT.refl a

theorem RelT.symm {a b : G} (h : RelT N a b) : RelT N b a := by
  unfold RelT at *
  have e : b * a⁻¹ = (a * b⁻¹)⁻¹ := by group
  rw [e]
  exact N.inv_mem h

theorem RelT.trans {a b c : G} (h : RelT N a b) (h' : RelT N b c) : RelT N a c := by
  unfold RelT at *
  have e : a * c⁻¹ = a * b⁻¹ * (b * c⁻¹) := by group
  rw [e]
  exact N.mul_mem h h'

theorem RelT.mul_right {a b : G} (h : RelT N a b) (g : G) : RelT N (a * g) (b * g) := by
  unfold RelT at *
  have e : a * g * (b * g)⁻¹ = a * b⁻¹ := by group
  rw [e]
  exact h

theorem RelT.left_mem {a b n : G} (hn : n ∈ N) (h : RelT N a b) : RelT N (n * a) b := by
  unfold RelT at *
  rw [mul_assoc]
  exact N.mul_mem hn h

theorem relT_of_eq_iff {a b c d : G} (h : a * b⁻¹ = c * d⁻¹) : RelT N a b ↔ RelT N c d := by
  unfold RelT
  rw [h]

theorem relT_of_eq_inv_iff {a b c d : G} (h : a * b⁻¹ = (c * d⁻¹)⁻¹) :
    RelT N a b ↔ RelT N c d := by
  unfold RelT
  rw [h, inv_mem_iff]

variable (a b r p g σ τ u ω : G)

theorem eps_fwd : RelT N (a * p * 1) (b * (r * p)) ↔ RelT N (a * 1) (b * r) :=
  relT_of_eq_iff (by group)

theorem eps_bwd : RelT N (b * p * 1) (a * (r⁻¹ * p)) ↔ RelT N (a * 1) (b * r) :=
  relT_of_eq_inv_iff (by group)

theorem u_fwd (hp : σ = g * p) (hτ : u⁻¹ * σ * u = τ) :
    RelT N (a * p * u) (b * (r * g⁻¹ * τ)) ↔ RelT N (a * (g⁻¹ * u * g)) (b * r) := by
  have hp' : p = g⁻¹ * σ := by rw [hp]; group
  subst hp' hτ
  exact relT_of_eq_iff (by group)

theorem U_fwd (hp : σ = g * p) (hτ : u⁻¹ * σ * u = τ) (hω : u * u = ω) :
    RelT N (a * p * u⁻¹) (b * (r * g⁻¹ * τ * ω⁻¹)) ↔ RelT N (a * (g⁻¹ * u * g)) (b * r) := by
  have hp' : p = g⁻¹ * σ := by rw [hp]; group
  subst hp' hτ hω
  exact relT_of_eq_iff (by group)

theorem U_bwd (hp : τ = g * r⁻¹ * p) (hτ : u⁻¹ * σ * u = τ) :
    RelT N (b * p * u⁻¹) (a * (g⁻¹ * σ)) ↔ RelT N (a * (g⁻¹ * u * g)) (b * r) := by
  have hp' : p = r * g⁻¹ * τ := by rw [hp]; group
  subst hp'
  subst hτ
  exact relT_of_eq_inv_iff (by group)

theorem u_bwd (hp : τ = g * r⁻¹ * p) (hτ : u⁻¹ * σ * u = τ) (hω : u * u = ω) :
    RelT N (b * p * u) (a * (g⁻¹ * σ * ω)) ↔ RelT N (a * (g⁻¹ * u * g)) (b * r) := by
  have hp' : p = r * g⁻¹ * τ := by rw [hp]; group
  subst hp'
  subst hτ hω
  exact relT_of_eq_inv_iff (by group)

omit a b r p g σ τ u ω

theorem chain_own (c ℓ : ℕ → G) {n qo : ℕ} (hqo : qo < n)
    (hs : ∀ q < n, q ≠ qo → RelT N (c q * ℓ q) (c (q + 1)))
    (hv : ((List.range n).map ℓ).prod = 1) (hcl : c n = c 0) :
    RelT N (c qo * ℓ qo) (c (qo + 1)) := by
  let P : ℕ → G := fun k => ((List.range k).map ℓ).prod
  have hP : ∀ k, P (k + 1) = P k * ℓ k := fun k => by
    simp only [P, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton]
  have c1 : ∀ q ≤ qo, RelT N (c 0 * P q) (c q) := by
    intro q
    induction q with
    | zero =>
      intro _
      simp only [P, List.range_zero, List.map_nil, List.prod_nil, mul_one]
      exact RelT.refl _
    | succ q ih =>
      intro hq
      have := (ih (by omega)).mul_right (ℓ q)
      rw [hP, ← mul_assoc]
      exact this.trans (hs q (by omega) (by omega))
  have c2 : ∀ d, qo + 1 + d ≤ n →
      RelT N (c (qo + 1) * (P (qo + 1))⁻¹ * P (qo + 1 + d)) (c (qo + 1 + d)) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.add_zero, inv_mul_cancel_right]
      exact RelT.refl _
    | succ d ih =>
      intro hd
      have := (ih (by omega)).mul_right (ℓ (qo + 1 + d))
      rw [show qo + 1 + (d + 1) = qo + 1 + d + 1 by omega, hP (qo + 1 + d), ← mul_assoc]
      exact this.trans (hs _ (by omega) (by omega))
  have f1 := (c1 qo le_rfl).mul_right (ℓ qo)
  have f2 := c2 (n - (qo + 1)) (by omega)
  rw [show qo + 1 + (n - (qo + 1)) = n by omega] at f2
  have hPn : P n = 1 := hv
  rw [hPn, mul_one, hcl] at f2
  have f3 := f2.mul_right (P (qo + 1))
  rw [inv_mul_cancel_right, hP qo, ← mul_assoc] at f3
  exact f1.symm.trans f3.symm

theorem exists_tree (nf : ℕ) (T : ℕ → Prop) (p c : ℕ → ℕ) (g : ℕ → G)
    (hpc : ∀ i < nf, T i → p i < c i)
    (hinj : ∀ i < nf, ∀ i' < nf, T i → T i' → c i = c i' → i = i') :
    ∃ wv : ℕ → G, wv 0 = 1 ∧ ∀ i < nf, T i → wv (c i) = wv (p i) * g i := by
  classical
  have key : ∀ B, ∃ wv : ℕ → G, wv 0 = 1 ∧
      ∀ i < nf, T i → c i < B → wv (c i) = wv (p i) * g i := by
    intro B
    induction B with
    | zero => exact ⟨fun _ => 1, rfl, fun i _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ B ih =>
      obtain ⟨wv, hw0, hw⟩ := ih
      refine ⟨fun D => if D = B then
          (if hB : ∃ i, i < nf ∧ T i ∧ c i = B then wv (p hB.choose) * g hB.choose else wv B)
        else wv D, ?_, ?_⟩
      · dsimp only
        by_cases h0 : (0 : ℕ) = B
        · have hn : ¬∃ i, i < nf ∧ T i ∧ c i = B := fun ⟨i, hi, hT, hc⟩ => by
            have := hpc i hi hT
            omega
          rw [ite_eq_left h0, dite_eq_right hn, ← h0, hw0]
        · rw [ite_eq_right h0, hw0]
      · intro i hi hTi hci
        dsimp only
        have hpB : p i ≠ B := by
          have := hpc i hi hTi
          omega
        rw [ite_eq_right hpB]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hci with hlt | heq
        · rw [ite_eq_right (by omega : c i ≠ B)]
          exact hw i hi hTi hlt
        · have hB : ∃ i, i < nf ∧ T i ∧ c i = B := ⟨i, hi, hTi, heq⟩
          rw [ite_eq_left heq, dite_eq_left hB]
          have hs := hB.choose_spec
          rw [hinj _ hs.1 _ hi hs.2.1 hTi (hs.2.2.trans heq.symm)]
  obtain ⟨wv, hw0, hw⟩ := key ((Finset.range nf).sup c + 1)
  exact ⟨wv, hw0, fun i hi hTi =>
    hw i hi hTi (Nat.lt_succ_of_le (Finset.le_sup (f := c) (Finset.mem_range.2 hi)))⟩

end CFSG.Certificates.DceTw

end
