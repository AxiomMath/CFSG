module

public import CFSG.ClassicalInvolution.RouteD.Entries

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

@[expose] def LeafPairM {ι : Type} (M : Matrix ι ι ℤ) (ℓ b : ι) : Prop :=
  ℓ ≠ b ∧ (∀ x, x ≠ ℓ → x ≠ b → M ℓ x = 0 ∧ M x ℓ = 0) ∧ M ℓ b = -1 ∧ M b ℓ = -1

@[expose] def LeafPair (t : DynkinType) (ℓ b : Fin t.rank) : Prop :=
  LeafPairM (stdCartan t) ℓ b

@[expose] def IsLongM {ι : Type} (M : Matrix ι ι ℤ) (ℓ : ι) : Prop :=
  ∃ d : ι → ℤ, (∀ i, 0 < d i) ∧ (∀ i j, d i * M i j = d j * M j i) ∧ ∀ y, d y ≤ d ℓ

@[expose] def IsLongStd (t : DynkinType) (ℓ : Fin t.rank) : Prop := IsLongM (stdCartan t) ℓ

@[expose] def LeafCase : (t : DynkinType) → Fin t.rank → Fin t.rank → Prop
  | .A n, ℓ, b => (ℓ.val = 0 ∧ b.val = 1) ∨ (ℓ.val + 1 = n ∧ b.val + 2 = n)
  | .B n, ℓ, b => 3 ≤ n ∧ ℓ.val = 0 ∧ b.val = 1
  | .C _, _, _ => False
  | .D n, ℓ, b => (ℓ.val = 0 ∧ b.val = 1) ∨ ((ℓ.val + 2 = n ∨ ℓ.val + 1 = n) ∧ b.val + 3 = n)
  | .E6, ℓ, b => (ℓ.val = 0 ∧ b.val = 2) ∨ (ℓ.val = 1 ∧ b.val = 3) ∨ (ℓ.val = 5 ∧ b.val = 4)
  | .E7, ℓ, b => (ℓ.val = 0 ∧ b.val = 2) ∨ (ℓ.val = 1 ∧ b.val = 3) ∨ (ℓ.val = 6 ∧ b.val = 5)
  | .E8, ℓ, b => (ℓ.val = 0 ∧ b.val = 2) ∨ (ℓ.val = 1 ∧ b.val = 3) ∨ (ℓ.val = 7 ∧ b.val = 6)
  | .F4, ℓ, b => ℓ.val = 0 ∧ b.val = 1
  | .G2, _, _ => False

theorem stdCartan_A_eq (n : ℕ) : stdCartan (.A n) = (CartanMatrix.A n).transpose :=
  congrArg Matrix.transpose (DynkinType.cartanMatrix_A n)

theorem stdCartan_B_eq (n : ℕ) : stdCartan (.B n) = (CartanMatrix.B n).transpose :=
  congrArg Matrix.transpose (DynkinType.cartanMatrix_B n)

theorem stdCartan_C_eq (n : ℕ) : stdCartan (.C n) = (CartanMatrix.C n).transpose :=
  congrArg Matrix.transpose (DynkinType.cartanMatrix_C n)

theorem stdCartan_D_eq (n : ℕ) : stdCartan (.D n) = (CartanMatrix.D n).transpose :=
  congrArg Matrix.transpose (DynkinType.cartanMatrix_D n)

theorem stdCartan_E6_eq : stdCartan .E6 = (CartanMatrix.E 6).transpose :=
  congrArg Matrix.transpose DynkinType.cartanMatrix_E6

theorem stdCartan_E7_eq : stdCartan .E7 = (CartanMatrix.E 7).transpose :=
  congrArg Matrix.transpose DynkinType.cartanMatrix_E7

theorem stdCartan_E8_eq : stdCartan .E8 = (CartanMatrix.E 8).transpose :=
  congrArg Matrix.transpose DynkinType.cartanMatrix_E8

theorem stdCartan_F4_eq : stdCartan .F4 = CartanMatrix.F₄.transpose :=
  congrArg Matrix.transpose DynkinType.cartanMatrix_F4

theorem stdCartan_G2_eq : stdCartan .G2 = CartanMatrix.G₂ :=
  (congrArg Matrix.transpose DynkinType.cartanMatrix_G2).trans (Matrix.transpose_transpose _)

theorem LeafPairM.transpose {ι : Type} {M : Matrix ι ι ℤ} {ℓ b : ι} (h : LeafPairM M ℓ b) :
    LeafPairM M.transpose ℓ b :=
  ⟨h.1, fun x hx hb => ⟨(h.2.1 x hx hb).2, (h.2.1 x hx hb).1⟩, h.2.2.2, h.2.2.1⟩

section Families

variable {n : ℕ}

theorem leafCase_A {ℓ b : Fin n} (h : LeafPairM (CartanMatrix.A n) ℓ b) :
    (ℓ.val = 0 ∧ b.val = 1) ∨ (ℓ.val + 1 = n ∧ b.val + 2 = n) := by
  obtain ⟨hne, hall, hb1, -⟩ := h
  have hne' : ℓ.val ≠ b.val := fun h => hne (Fin.ext h)
  rw [A_eq_neg_one_iff] at hb1
  have key : ∀ x : Fin n, x.val ≠ ℓ.val → x.val ≠ b.val →
      (ℓ.val + 1 = x.val ∨ x.val + 1 = ℓ.val) → False := by
    intro x h1 h2 hx
    have := (hall x (fun e => h1 (by rw [e])) (fun e => h2 (by rw [e]))).1
    rw [A_eq_zero_iff] at this
    exact this.2 hx
  rcases hb1 with h1 | h1
  · left
    have h0 : ℓ.val = 0 := by
      by_contra h0
      exact key ⟨ℓ.val - 1, by omega⟩ (by simp; omega) (by simp; omega) (by simp; omega)
    exact ⟨h0, by omega⟩
  · right
    have h0 : ℓ.val + 1 = n := by
      by_contra h0
      exact key ⟨ℓ.val + 1, by omega⟩ (by simp) (by simp; omega) (by simp)
    exact ⟨h0, by omega⟩

theorem leafCase_B {ℓ b : Fin n} (h : LeafPairM (CartanMatrix.B n) ℓ b) :
    3 ≤ n ∧ ℓ.val = 0 ∧ b.val = 1 := by
  obtain ⟨hne, hall, hb1, hb2⟩ := h
  have hne' : ℓ.val ≠ b.val := fun h => hne (Fin.ext h)
  rw [B_eq_neg_one_iff] at hb1 hb2
  have key : ∀ x : Fin n, x.val ≠ ℓ.val → x.val ≠ b.val →
      (ℓ.val + 1 = x.val ∨ x.val + 1 = ℓ.val) → False := by
    intro x h1 h2 hx
    have := (hall x (fun e => h1 (by rw [e])) (fun e => h2 (by rw [e]))).1
    rw [B_eq_zero_iff] at this
    omega
  have hℓ := ℓ.isLt
  have hb := b.isLt
  by_cases hcase : ℓ.val + 1 = b.val
  · have h0 : ℓ.val = 0 := by
      by_contra h0
      exact key ⟨ℓ.val - 1, by omega⟩ (by simp; omega) (by simp; omega) (by simp; omega)
    refine ⟨?_, h0, by omega⟩
    omega
  · exfalso
    have h1 : b.val + 1 = ℓ.val := by omega
    have h2 : ℓ.val + 1 < n := by omega
    exact key ⟨ℓ.val + 1, h2⟩ (by simp) (by simp; omega) (by simp)

theorem leafCase_D {ℓ b : Fin n} (h : LeafPairM (CartanMatrix.D n) ℓ b) :
    (ℓ.val = 0 ∧ b.val = 1) ∨ ((ℓ.val + 2 = n ∨ ℓ.val + 1 = n) ∧ b.val + 3 = n) := by
  obtain ⟨hne, hall, hb1, -⟩ := h
  have hne' : ℓ.val ≠ b.val := fun h => hne (Fin.ext h)
  rw [D_eq_neg_one_iff] at hb1
  have key : ∀ x : Fin n, x.val ≠ ℓ.val → x.val ≠ b.val → DAdj n ℓ x → False := by
    intro x h1 h2 hx
    have := (hall x (fun e => h1 (by rw [e])) (fun e => h2 (by rw [e]))).1
    rw [D_eq_zero_iff] at this
    exact this.2 hx
  have hℓ := ℓ.isLt
  have hb := b.isLt
  unfold DAdj at hb1
  rcases hb1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have h0 : ℓ.val = 0 := by
      by_contra h0
      refine key ⟨ℓ.val - 1, by omega⟩ (by simp; omega) (by simp; omega) ?_
      unfold DAdj
      simp only
      omega
    exact ⟨h0, by omega⟩
  · exfalso
    refine key ⟨ℓ.val + 1, by omega⟩ (by simp) (by simp; omega) ?_
    unfold DAdj
    simp only [true_and]
    omega
  · exfalso
    by_cases hb' : b.val + 2 = n
    · refine key ⟨n - 1, by omega⟩ (by simp; omega) (by simp; omega) ?_
      unfold DAdj
      simp only
      omega
    · refine key ⟨n - 2, by omega⟩ (by simp; omega) (by simp; omega) ?_
      unfold DAdj
      simp only
      omega
  · right
    exact ⟨by omega, by omega⟩

theorem symmetrizer_C {d : Fin n → ℤ}
    (hd : ∀ i j, d i * (CartanMatrix.C n).transpose i j = d j * (CartanMatrix.C n).transpose j i)
    (hn : 2 ≤ n) :
    (∀ k : ℕ, ∀ hk : k + 2 ≤ n, d ⟨k, by omega⟩ = d ⟨0, by omega⟩) ∧
      d ⟨n - 1, by omega⟩ = 2 * d ⟨n - 2, by omega⟩ := by
  refine ⟨?_, ?_⟩
  · intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have e1 := hd ⟨k, by omega⟩ ⟨k + 1, by omega⟩
      simp only [Matrix.transpose_apply] at e1
      have c1 : CartanMatrix.C n ⟨k + 1, by omega⟩ ⟨k, by omega⟩ = -1 := by
        rw [C_eq_neg_one_iff]; simp; omega
      have c2 : CartanMatrix.C n ⟨k, by omega⟩ ⟨k + 1, by omega⟩ = -1 := by
        rw [C_eq_neg_one_iff]; simp
      rw [c1, c2] at e1
      have := ih (by omega)
      omega
  · have e2 := hd ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩
    simp only [Matrix.transpose_apply] at e2
    have c3 : CartanMatrix.C n ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩ = -2 := by
      rw [C_eq_neg_two_iff]; simp; omega
    have c4 : CartanMatrix.C n ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ = -1 := by
      rw [C_eq_neg_one_iff]; simp; omega
    rw [c3, c4] at e2
    omega

theorem isLongM_C_last {ℓ : Fin n} (hn : 2 ≤ n) (hl : IsLongM (CartanMatrix.C n).transpose ℓ) :
    ℓ.val + 1 = n := by
  obtain ⟨d, hdpos, hd, hmax⟩ := hl
  obtain ⟨hc, hl2⟩ := symmetrizer_C hd hn
  by_contra hne
  have h1 := hc ℓ.val (by have := ℓ.isLt; omega)
  have h2 := hc (n - 2) (by omega)
  have h3 := hmax ⟨n - 1, by omega⟩
  have h4 := hdpos ⟨0, by omega⟩
  simp only [Fin.eta] at h1
  omega

theorem not_isLongM_C {ℓ b : Fin n} (h : LeafPairM (CartanMatrix.C n) ℓ b)
    (hl : IsLongM (CartanMatrix.C n).transpose ℓ) : False := by
  obtain ⟨hne, hall, hb1, hb2⟩ := h
  have hne' : ℓ.val ≠ b.val := fun h => hne (Fin.ext h)
  rw [C_eq_neg_one_iff] at hb1 hb2
  have key : ∀ x : Fin n, x.val ≠ ℓ.val → x.val ≠ b.val →
      (ℓ.val + 1 = x.val ∨ x.val + 1 = ℓ.val) → False := by
    intro x h1 h2 hx
    have := (hall x (fun e => h1 (by rw [e])) (fun e => h2 (by rw [e]))).1
    rw [C_eq_zero_iff] at this
    omega
  have hℓ := ℓ.isLt
  have hb := b.isLt
  have h0 : ℓ.val = 0 := by
    by_cases hcase : ℓ.val + 1 = b.val
    · by_contra h0
      exact key ⟨ℓ.val - 1, by omega⟩ (by simp; omega) (by simp; omega) (by simp; omega)
    · exfalso
      exact key ⟨ℓ.val + 1, by omega⟩ (by simp) (by simp; omega) (by simp)
  have := isLongM_C_last (by omega) hl
  omega

end Families

theorem LeafPairM.of_transpose {ι : Type} {M : Matrix ι ι ℤ} {ℓ b : ι}
    (h : LeafPairM M.transpose ℓ b) : LeafPairM M ℓ b := by
  simpa using h.transpose

private def ent {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Fin n → Fin n → ℤ := fun i j => M i j

private theorem leafPairs_E {n : ℕ} (k : Fin n → Fin n → Prop)
    [∀ i j, Decidable (k i j)] (hk : ∀ ℓ b : Fin n, (ℓ ≠ b ∧ (∀ x : Fin n, x ≠ ℓ → x ≠ b →
      ent (CartanMatrix.E n) ℓ x = 0 ∧ ent (CartanMatrix.E n) x ℓ = 0) ∧
      ent (CartanMatrix.E n) ℓ b = -1 ∧ ent (CartanMatrix.E n) b ℓ = -1) → k ℓ b) {ℓ b : Fin n}
    (h : LeafPairM (CartanMatrix.E n) ℓ b) : k ℓ b := hk ℓ b h

theorem leafCase_E6 {ℓ b : Fin 6} (h : LeafPairM (CartanMatrix.E 6) ℓ b) :
    (ℓ.val = 0 ∧ b.val = 2) ∨ (ℓ.val = 1 ∧ b.val = 3) ∨ (ℓ.val = 5 ∧ b.val = 4) := by
  refine leafPairs_E (fun ℓ b : Fin 6 =>
    (ℓ.val = 0 ∧ b.val = 2) ∨ (ℓ.val = 1 ∧ b.val = 3) ∨ (ℓ.val = 5 ∧ b.val = 4)) ?_ h
  decide

theorem leafCase_E7 {ℓ b : Fin 7} (h : LeafPairM (CartanMatrix.E 7) ℓ b) :
    (ℓ.val = 0 ∧ b.val = 2) ∨ (ℓ.val = 1 ∧ b.val = 3) ∨ (ℓ.val = 6 ∧ b.val = 5) := by
  refine leafPairs_E (fun ℓ b : Fin 7 =>
    (ℓ.val = 0 ∧ b.val = 2) ∨ (ℓ.val = 1 ∧ b.val = 3) ∨ (ℓ.val = 6 ∧ b.val = 5)) ?_ h
  decide

theorem leafCase_E8 {ℓ b : Fin 8} (h : LeafPairM (CartanMatrix.E 8) ℓ b) :
    (ℓ.val = 0 ∧ b.val = 2) ∨ (ℓ.val = 1 ∧ b.val = 3) ∨ (ℓ.val = 7 ∧ b.val = 6) := by
  refine leafPairs_E (fun ℓ b : Fin 8 =>
    (ℓ.val = 0 ∧ b.val = 2) ∨ (ℓ.val = 1 ∧ b.val = 3) ∨ (ℓ.val = 7 ∧ b.val = 6)) ?_ h
  decide

theorem leafCase_F4 {ℓ b : Fin 4} (h : LeafPairM CartanMatrix.F₄ ℓ b)
    (hl : IsLongM CartanMatrix.F₄.transpose ℓ) : ℓ.val = 0 ∧ b.val = 1 := by
  obtain ⟨d, hdpos, hd, hmax⟩ := hl
  have hpairs : ∀ ℓ b : Fin 4, (ℓ ≠ b ∧ (∀ x : Fin 4, x ≠ ℓ → x ≠ b →
      ent CartanMatrix.F₄ ℓ x = 0 ∧ ent CartanMatrix.F₄ x ℓ = 0) ∧
      ent CartanMatrix.F₄ ℓ b = -1 ∧ ent CartanMatrix.F₄ b ℓ = -1) →
      (ℓ.val = 0 ∧ b.val = 1) ∨ (ℓ.val = 3 ∧ b.val = 2) := by
    decide
  rcases hpairs ℓ b h with h1 | h1
  · exact h1
  · exfalso
    have e01 := hd 0 1
    have e12 := hd 1 2
    have e23 := hd 2 3
    have c1 : CartanMatrix.F₄ 1 0 = -1 := by decide
    have c2 : CartanMatrix.F₄ 0 1 = -1 := by decide
    have c3 : CartanMatrix.F₄ 2 1 = -1 := by decide
    have c4 : CartanMatrix.F₄ 1 2 = -2 := by decide
    have c5 : CartanMatrix.F₄ 3 2 = -1 := by decide
    have c6 : CartanMatrix.F₄ 2 3 = -1 := by decide
    simp only [Matrix.transpose_apply, c1, c2, c3, c4, c5, c6] at e01 e12 e23
    have hℓ : ℓ = 3 := Fin.ext h1.1
    subst hℓ
    have := hmax 0
    have := hdpos 3
    omega

theorem leafCase_G2 {ℓ b : Fin 2} (h : LeafPairM CartanMatrix.G₂ ℓ b) : False := by
  have hpairs : ∀ ℓ b : Fin 2, (ℓ ≠ b ∧ (∀ x : Fin 2, x ≠ ℓ → x ≠ b →
      ent CartanMatrix.G₂ ℓ x = 0 ∧ ent CartanMatrix.G₂ x ℓ = 0) ∧
      ent CartanMatrix.G₂ ℓ b = -1 ∧ ent CartanMatrix.G₂ b ℓ = -1) → False := by
    decide
  exact hpairs ℓ b h

theorem leafCase_of_leafPair {t : DynkinType} {ℓ b : Fin t.rank} (h : LeafPair t ℓ b)
    (hl : IsLongStd t ℓ) : LeafCase t ℓ b := by
  cases t with
  | A n =>
    have h' : LeafPairM (CartanMatrix.A n).transpose ℓ b := by
      rw [← stdCartan_A_eq]; exact h
    exact leafCase_A h'.of_transpose
  | B n =>
    have h' : LeafPairM (CartanMatrix.B n).transpose ℓ b := by
      rw [← stdCartan_B_eq]; exact h
    exact leafCase_B h'.of_transpose
  | C n =>
    exfalso
    have h' : LeafPairM (CartanMatrix.C n).transpose ℓ b := by
      rw [← stdCartan_C_eq]; exact h
    have hl' : IsLongM (CartanMatrix.C n).transpose ℓ := by
      rw [← stdCartan_C_eq]; exact hl
    exact not_isLongM_C h'.of_transpose hl'
  | D n =>
    have h' : LeafPairM (CartanMatrix.D n).transpose ℓ b := by
      rw [← stdCartan_D_eq]; exact h
    exact leafCase_D h'.of_transpose
  | E6 =>
    have h' : LeafPairM (CartanMatrix.E 6).transpose ℓ b := by
      rw [← stdCartan_E6_eq]; exact h
    exact leafCase_E6 h'.of_transpose
  | E7 =>
    have h' : LeafPairM (CartanMatrix.E 7).transpose ℓ b := by
      rw [← stdCartan_E7_eq]; exact h
    exact leafCase_E7 h'.of_transpose
  | E8 =>
    have h' : LeafPairM (CartanMatrix.E 8).transpose ℓ b := by
      rw [← stdCartan_E8_eq]; exact h
    exact leafCase_E8 h'.of_transpose
  | F4 =>
    have h' : LeafPairM CartanMatrix.F₄.transpose ℓ b := by
      rw [← stdCartan_F4_eq]; exact h
    have hl' : IsLongM CartanMatrix.F₄.transpose ℓ := by
      rw [← stdCartan_F4_eq]; exact hl
    exact leafCase_F4 h'.of_transpose hl'
  | G2 =>
    exfalso
    have h' : LeafPairM CartanMatrix.G₂ ℓ b := by
      rw [← stdCartan_G2_eq]; exact h
    exact leafCase_G2 h'

end CFSG.ClassicalInvolution.RouteD
