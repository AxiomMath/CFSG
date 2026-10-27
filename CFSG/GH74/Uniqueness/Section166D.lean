module

public import CFSG.GH74.Uniqueness.Section166C

public section

namespace CFSG.GH74.Uniqueness.Cor166

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem exists_mem_ne_ne {W : Subgroup X} (hW4 : Nat.card W = 4) (a : X) :
    ∃ w ∈ W, w ≠ 1 ∧ w ≠ a := by
  by_contra hcon
  push Not at hcon
  have hsub : (W : Set X) ⊆ {1, a} := fun w hw => by
    by_cases h1 : w = 1
    · exact Or.inl h1
    · exact Or.inr (hcon w hw h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, a} : Set X).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : X) ({a} : Set X)
    rwa [Set.ncard_singleton] at this
  have h3 : Nat.card W = (W : Set X).ncard := Nat.card_coe_set_eq (W : Set X)
  omega

theorem cor166d_pair
    (S : ZDSetup X Z M) (c : Conf16 Z M) (h163 : Lemma163Stmt Z M)
    (h164 : Lemma164Stmt Z M) (h165 : Prop165Stmt Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) {a w₀ : X} (ha2 : orderOf a = 2) (hw₀2 : w₀ * w₀ = 1)
    (hw₀1 : w₀ ≠ 1) (hw₀a : w₀ ≠ a) (hcomm : w₀ * a = a * w₀) :
    a ∈ Z ∨ w₀ ∈ Z ∨ w₀ * a ∈ Z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨haZ, hw₀Z, hw₀aZ⟩ := hcon
  have hZ := S.invariant
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha2, sq] at this
  have hZconj : ∀ (g y : X), g⁻¹ * y * g ∈ Z → y ∈ Z := fun g y h => by
    have := hZ.2 _ h g⁻¹
    simpa [mul_assoc] using this
  have hau : IsConj c.u a := by
    rcases cor166c_invol S c h163 h164 h165 hB ha2 with h | h
    · exact absurd (hZ.isConj_mem c.hz h.symm) haZ
    · exact h
  obtain ⟨g, hg⟩ := isConj_iff.mp hau
  have hua : c.u = g⁻¹ * a * g := by rw [← hg]; group
  set w := g⁻¹ * w₀ * g with hwdef
  have hwB : w ∈ c.B := by
    rw [Subgroup.mem_centralizer_singleton_iff, hua, hwdef]
    symm
    calc g⁻¹ * a * g * (g⁻¹ * w₀ * g) = g⁻¹ * (a * w₀) * g := by group
      _ = g⁻¹ * (w₀ * a) * g := by rw [hcomm]
      _ = g⁻¹ * w₀ * g * (g⁻¹ * a * g) := by group
  have hw2 : w * w = 1 := by
    rw [hwdef]
    calc g⁻¹ * w₀ * g * (g⁻¹ * w₀ * g) = g⁻¹ * (w₀ * w₀) * g := by group
      _ = 1 := by rw [hw₀2]; group
  have hwu : w * c.u = g⁻¹ * (w₀ * a) * g := by rw [hwdef, hua]; group
  have hwZ : w ∉ Z := fun h => hw₀Z (hZconj g w₀ h)
  have hwuZ : w * c.u ∉ Z := fun h => hw₀aZ (hZconj g _ (hwu ▸ h))
  have hw1 : w ≠ 1 := fun h => hw₀1 (by
    have : w₀ = g * w * g⁻¹ := by rw [hwdef]; group
    rw [this, h]; group)
  have hwu1 : w * c.u ≠ 1 := fun h => hw₀a (by
    have h' : g⁻¹ * (w₀ * a) * g = 1 := hwu ▸ h
    have : w₀ * a = 1 := by
      calc w₀ * a = g * (g⁻¹ * (w₀ * a) * g) * g⁻¹ := by group
        _ = 1 := by rw [h']; group
    calc w₀ = w₀ * a * a⁻¹ := by group
      _ = a := by rw [this, one_mul, inv_eq_of_mul_eq_one_right haa])
  obtain ⟨b, hbB, hbT⟩ := exists_conj_mem_of_isSylowOf (h163 c).2.2.1 hwB hw2
  have hbu : b * c.u * b⁻¹ = c.u := by
    rw [comm_u_of_mem_B c hbB]
    group
  have hZb : ∀ y : X, b * y * b⁻¹ ∈ Z → y ∈ Z := fun y h => by
    have := hZ.2 _ h b
    simpa [mul_assoc] using this
  have hw'2 : b * w * b⁻¹ * (b * w * b⁻¹) = 1 := by
    calc b * w * b⁻¹ * (b * w * b⁻¹) = b * (w * w) * b⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  rcases mem_or_mul_mem_Q S c h164 h165 hB hbT hw'2 with hQ | hQ
  · have hne : b * w * b⁻¹ ≠ 1 := fun h => hw1 (by
      calc w = b⁻¹ * (b * w * b⁻¹) * b := by group
        _ = 1 := by rw [h]; group)
    have hord : orderOf (b * w * b⁻¹) = 2 := orderOf_eq_prime (by rw [sq]; exact hw'2) hne
    exact hwZ (hZb w (hB.invol _ (Q_le_B0 c hQ) hord))
  · have heq : b * w * b⁻¹ * c.u = b * (w * c.u) * b⁻¹ := by
      calc b * w * b⁻¹ * c.u = b * w * b⁻¹ * (b * c.u * b⁻¹) := by rw [hbu]
        _ = b * (w * c.u) * b⁻¹ := by group
    rw [heq] at hQ
    have hne : b * (w * c.u) * b⁻¹ ≠ 1 := fun h => hwu1 (by
      calc w * c.u = b⁻¹ * (b * (w * c.u) * b⁻¹) * b := by group
        _ = 1 := by rw [h]; group)
    have hsq : b * (w * c.u) * b⁻¹ * (b * (w * c.u) * b⁻¹) = 1 := by
      have hwuB : w * c.u = c.u * w := comm_u_of_mem_B c hwB
      calc b * (w * c.u) * b⁻¹ * (b * (w * c.u) * b⁻¹) = b * (w * (c.u * w) * c.u) * b⁻¹ := by
            group
        _ = b * (w * (w * c.u) * c.u) * b⁻¹ := by rw [← hwuB]
        _ = b * ((w * w) * (c.u * c.u)) * b⁻¹ := by group
        _ = 1 := by rw [hw2, u_mul_self c]; group
    have hord : orderOf (b * (w * c.u) * b⁻¹) = 2 := orderOf_eq_prime (by rw [sq]; exact hsq) hne
    exact hwuZ (hZb _ (hB.invol _ (Q_le_B0 c hQ) hord))

theorem cor166d
    (S : ZDSetup X Z M) (c : Conf16 Z M) (h163 : Lemma163Stmt Z M)
    (h164 : Lemma164Stmt Z M) (h165 : Prop165Stmt Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) (W : Subgroup X) (hW4 : Nat.card W = 4)
    (hW2 : ∀ w ∈ W, w * w = 1) : ∃ w ∈ W, w ∈ Z := by
  obtain ⟨a, haW, ha1, -⟩ := exists_mem_ne_ne hW4 1
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hW2 a haW) ha1
  obtain ⟨w₀, hw₀W, hw₀1, hw₀a⟩ := exists_mem_ne_ne hW4 a
  have hcomm : w₀ * a = a * w₀ := by
    have h1 := hW2 _ (W.mul_mem hw₀W haW)
    have hw₀i : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right (hW2 w₀ hw₀W)
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hW2 a haW)
    calc w₀ * a = (w₀ * a)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = a⁻¹ * w₀⁻¹ := mul_inv_rev _ _
      _ = a * w₀ := by rw [hai, hw₀i]
  rcases cor166d_pair S c h163 h164 h165 hB ha2 (hW2 w₀ hw₀W) hw₀1 hw₀a hcomm with h | h | h
  · exact ⟨a, haW, h⟩
  · exact ⟨w₀, hw₀W, h⟩
  · exact ⟨_, W.mul_mem hw₀W haW, h⟩

end CFSG.GH74.Uniqueness.Cor166
