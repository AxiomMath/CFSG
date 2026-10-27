module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuX17Gen

public section

namespace CFSG.ComponentClassification.GMS78

variable {Γ : Type} [Group Γ]

@[expose] def InCV (V : Subgroup Γ) (x w : Γ) : Prop := w ∈ V ∧ w * x = x * w

@[expose] noncomputable def nCV (V : Subgroup Γ) (x : Γ) : ℕ := Nat.card {w // InCV V x w}

@[expose] noncomputable def nRV (V : Subgroup Γ) (x t : Γ) : ℕ :=
  Nat.card {w // InCV V x w ∧ w * w = t}

@[expose] noncomputable def nZV (V : Subgroup Γ) (x t : Γ) : ℕ :=
  Nat.card {w // InCV V x w ∧ ∀ q, InCV V x q → w * q = q * w ∨ w * q = t * (q * w)}

theorem card_conj (g : Γ) (P : Γ → Prop) :
    Nat.card {w // P w} = Nat.card {w // P (g * w * g⁻¹)} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g⁻¹).toEquiv fun w => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
  rw [show g * (g⁻¹ * w * g) * g⁻¹ = w by group]

theorem conj_comm_iff (g a b : Γ) :
    g⁻¹ * a * g * b = b * (g⁻¹ * a * g) ↔ a * (g * b * g⁻¹) = g * b * g⁻¹ * a := by
  constructor
  · intro h
    calc a * (g * b * g⁻¹) = g * (g⁻¹ * a * g * b) * g⁻¹ := by group
      _ = g * (b * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
      _ = g * b * g⁻¹ * a := by group
  · intro h
    calc g⁻¹ * a * g * b = g⁻¹ * (a * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹ * a) * g := by rw [h]
      _ = b * (g⁻¹ * a * g) := by group

theorem swap_mem {V : Subgroup Γ} {z g : Γ} (hV : ∀ w, w ∈ V ↔ w * z = z * w)
    (hx : g * z * g⁻¹ ∈ V) : g⁻¹ * z * g ∈ V := by
  rw [hV] at hx ⊢
  calc g⁻¹ * z * g * z = g⁻¹ * (z * (g * z * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * z * g⁻¹ * z) * g := by rw [hx]
    _ = z * (g⁻¹ * z * g) := by group

theorem inCV_swap {V : Subgroup Γ} {z g : Γ} (hV : ∀ w, w ∈ V ↔ w * z = z * w) (w : Γ) :
    InCV V (g * z * g⁻¹) w ↔ InCV V (g⁻¹ * z * g) (g⁻¹ * w * g) := by
  unfold InCV
  rw [hV, hV, conj_comm_iff]
  have h2 : g⁻¹ * w * g * (g⁻¹ * z * g) = g⁻¹ * z * g * (g⁻¹ * w * g) ↔ w * z = z * w := by
    rw [show g⁻¹ * w * g * (g⁻¹ * z * g) = g⁻¹ * (w * z) * g by group,
      show g⁻¹ * z * g * (g⁻¹ * w * g) = g⁻¹ * (z * w) * g by group]
    constructor
    · intro h
      simpa using h
    · intro h
      rw [h]
  rw [h2]
  exact and_comm

theorem inCV_swap' {V : Subgroup Γ} {z g : Γ} (hV : ∀ w, w ∈ V ↔ w * z = z * w) (w : Γ) :
    InCV V (g * z * g⁻¹) (g * w * g⁻¹) ↔ InCV V (g⁻¹ * z * g) w := by
  rw [inCV_swap hV, show g⁻¹ * (g * w * g⁻¹) * g = w by group]

theorem nCV_swap {V : Subgroup Γ} {z g : Γ} (hV : ∀ w, w ∈ V ↔ w * z = z * w) :
    nCV V (g * z * g⁻¹) = nCV V (g⁻¹ * z * g) := by
  unfold nCV
  rw [card_conj g]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun w => inCV_swap' hV w)

theorem nRV_swap {V : Subgroup Γ} {z g : Γ} (hV : ∀ w, w ∈ V ↔ w * z = z * w) (t : Γ) :
    nRV V (g * z * g⁻¹) t = nRV V (g⁻¹ * z * g) (g⁻¹ * t * g) := by
  unfold nRV
  rw [card_conj g]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  rw [inCV_swap' hV, show g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ by group]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← h2]; group⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]; group⟩

theorem nZV_swap {V : Subgroup Γ} {z g : Γ} (hV : ∀ w, w ∈ V ↔ w * z = z * w) (t : Γ) :
    nZV V (g * z * g⁻¹) t = nZV V (g⁻¹ * z * g) (g⁻¹ * t * g) := by
  unfold nZV
  rw [card_conj g]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  rw [inCV_swap' hV]
  refine and_congr Iff.rfl ⟨fun h q hq => ?_, fun h q hq => ?_⟩
  · have h1 := h (g * q * g⁻¹) ((inCV_swap' hV q).mpr hq)
    rcases h1 with h1 | h1
    · left
      have : g * (w * q) * g⁻¹ = g * (q * w) * g⁻¹ := by
        rw [show g * (w * q) * g⁻¹ = g * w * g⁻¹ * (g * q * g⁻¹) by group, h1]; group
      simpa using this
    · right
      have : g * (w * q) * g⁻¹ = g * (g⁻¹ * t * g * (q * w)) * g⁻¹ := by
        rw [show g * (w * q) * g⁻¹ = g * w * g⁻¹ * (g * q * g⁻¹) by group, h1]; group
      simpa using this
  · have hq' := (inCV_swap hV q).mp hq
    rcases h _ hq' with h1 | h1
    · left
      calc g * w * g⁻¹ * q = g * (w * (g⁻¹ * q * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * q * g * w) * g⁻¹ := by rw [h1]
        _ = q * (g * w * g⁻¹) := by group
    · right
      calc g * w * g⁻¹ * q = g * (w * (g⁻¹ * q * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * t * g * (g⁻¹ * q * g * w)) * g⁻¹ := by rw [h1]
        _ = t * (q * (g * w * g⁻¹)) := by group

omit [Group Γ] in
theorem card_eq_countP_range (φ : ℕ → Γ) (n : ℕ) (V : Set Γ) (hφV : ∀ p < n, φ p ∈ V)
    (hVφ : ∀ w ∈ V, ∃ p < n, φ p = w) (hinj : ∀ p < n, ∀ q < n, φ p = φ q → p = q)
    (P : Γ → Prop) (Q : ℕ → Bool) (hPQ : ∀ p < n, P (φ p) ↔ Q p = true) :
    Nat.card {w : Γ // w ∈ V ∧ P w} = (List.range n).countP Q := by
  classical
  set s : Finset ℕ := (Finset.range n).filter (fun p => Q p = true) with hs
  have hmem : ∀ p, p ∈ s ↔ p < n ∧ Q p = true := fun p => by simp [hs]
  have h1 : Nat.card {w : Γ // w ∈ V ∧ P w} = Nat.card s := by
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun p : s => (⟨φ p, ?_⟩ : {w : Γ // w ∈ V ∧ P w}))
      ⟨?_, ?_⟩)
    · obtain ⟨hp, hq⟩ := (hmem p).mp p.2
      exact ⟨hφV p hp, (hPQ p hp).mpr hq⟩
    · intro p q h
      have := congrArg Subtype.val h
      exact Subtype.ext (hinj p ((hmem p).mp p.2).1 q ((hmem q).mp q.2).1 this)
    · rintro ⟨w, hwV, hwP⟩
      obtain ⟨p, hp, rfl⟩ := hVφ w hwV
      exact ⟨⟨p, (hmem p).mpr ⟨hp, (hPQ p hp).mp hwP⟩⟩, rfl⟩
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_coe, hs, List.countP_eq_length_filter]
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, ← Multiset.coe_range,
    Multiset.filter_coe, Multiset.coe_card]
  simp

end CFSG.ComponentClassification.GMS78
