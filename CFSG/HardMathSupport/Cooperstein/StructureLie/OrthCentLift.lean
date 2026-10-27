module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthCentMatrix

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.LieType.Universal.Spin

variable {n : ℕ} {F : Type} [Field F]

structure Shape (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (P : Set (Fin n ⊕ Fin n)) : Prop where
  delta : ∀ x y, ¬ (x ∈ P ∧ bar y ∈ P) → G x y = if x = y then 1 else 0
  diag : ∀ p ∈ P, G p (bar p) = 0
  symm : ∀ p ∈ P, ∀ q ∈ P, G p (bar q) = G q (bar p)

@[expose] noncomputable def cntBlock (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (P : Set (Fin n ⊕ Fin n)) :
    ℕ :=
  open Classical in
  (Finset.univ.filter fun pq : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) =>
    pq.1 ∈ P ∧ pq.2 ∈ P ∧ G pq.1 (bar pq.2) ≠ 0).card

variable {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} {P : Set (Fin n ⊕ Fin n)}

theorem mul_root_entry {p q : Fin n ⊕ Fin n} {c : F}
    (hp : ∀ x, G x p = if x = p then 1 else 0) (hq : ∀ x, G x q = if x = q then 1 else 0)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hX : ∀ z y, X z y = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) z y +
      (if z = p ∧ y = bar q then c else 0) - (if z = q ∧ y = bar p then c else 0)) (x y : Fin n ⊕ Fin n) :
    (G * X) x y = G x y + (if x = p ∧ y = bar q then c else 0) -
      (if x = q ∧ y = bar p then c else 0) := by
  simp only [Matrix.mul_apply, hX, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [hp x, hq x]
  by_cases hpq : p = q
  · subst hpq
    by_cases hx1 : x = p <;> by_cases hy1 : y = bar p <;> simp [hx1, hy1]
  · by_cases hx1 : x = p <;> by_cases hx2 : x = q <;> by_cases hy1 : y = bar q <;>
      by_cases hy2 : y = bar p <;> simp_all

theorem peel_shape [CharP F 2] (hd : ∀ p ∈ P, bar p ∉ P) (hS : Shape G P) {p q : Fin n ⊕ Fin n}
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) (hc : G p (bar q) ≠ 0)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hX : ∀ z y, X z y = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) z y +
      (if z = p ∧ y = bar q then -G p (bar q) else 0) -
        (if z = q ∧ y = bar p then -G p (bar q) else 0)) :
    Shape (G * X) P ∧ cntBlock (G * X) P < cntBlock G P := by
  classical
  have h2 : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
  have hcp : ∀ x, G x p = if x = p then 1 else 0 := fun x =>
    hS.delta x p (fun h => hd p hp h.2)
  have hcq : ∀ x, G x q = if x = q then 1 else 0 := fun x =>
    hS.delta x q (fun h => hd q hq h.2)
  have hE := mul_root_entry hcp hcq X hX
  have hsymm := hS.symm q hq p hp
  have hE' : ∀ u w, u ∈ P → w ∈ P → (G * X) u (bar w) = G u (bar w) +
      (if u = p ∧ w = q then -G p (bar q) else 0) - (if u = q ∧ w = p then -G p (bar q) else 0) := by
    intro u w hu hw
    rw [hE]
    simp only [bar_inj]
  have hshape : Shape (G * X) P := by
    refine ⟨fun x y hxy => ?_, fun u hu => ?_, fun u hu w hw => ?_⟩
    · rw [hE]
      have h1 : ¬ (x = p ∧ y = bar q) := fun h => hxy ⟨h.1 ▸ hp, by rw [h.2, bar_bar]; exact hq⟩
      have h3 : ¬ (x = q ∧ y = bar p) := fun h => hxy ⟨h.1 ▸ hq, by rw [h.2, bar_bar]; exact hp⟩
      rw [if_neg h1, if_neg h3, hS.delta x y hxy]
      ring
    · rw [hE' u u hu hu, hS.diag u hu]
      have h1 : ¬ (u = p ∧ u = q) := fun h => hpq (h.1.symm.trans h.2)
      have h3 : ¬ (u = q ∧ u = p) := fun h => hpq (h.2.symm.trans h.1)
      simp [h1, h3]
    · rw [hE' u w hu hw, hE' w u hw hu, hS.symm u hu w hw]
      simp only [and_comm (a := w = p) (b := u = q), and_comm (a := w = q) (b := u = p)]
      by_cases i1 : u = p ∧ w = q
      · have i2 : ¬ (u = q ∧ w = p) := fun h => hpq (i1.1.symm.trans h.1)
        rw [if_pos i1, if_neg i2]
        linear_combination (-G p (bar q)) * h2
      · by_cases i2 : u = q ∧ w = p
        · rw [if_neg i1, if_pos i2]
          linear_combination (G p (bar q)) * h2
        · rw [if_neg i1, if_neg i2]
  refine ⟨hshape, ?_⟩
  unfold cntBlock
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(p, q), ?_, ?_⟩
    · simp [hp, hq, hc]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not]
      intro _ _
      rw [hE' p q hp hq]
      simp [hpq]
  · intro ⟨u, w⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    obtain ⟨hu, hw, hne⟩ := h
    refine ⟨hu, hw, fun h0 => hne ?_⟩
    rw [hE' u w hu hw, h0]
    by_cases i1 : u = p ∧ w = q
    · obtain ⟨h1, h2'⟩ := i1
      rw [h1, h2'] at h0
      exact absurd h0 hc
    · by_cases i2 : u = q ∧ w = p
      · obtain ⟨h1, h2'⟩ := i2
        rw [h1, h2', hsymm] at h0
        exact absurd h0 hc
      · rw [if_neg i1, if_neg i2]
        ring

@[expose] def pSet (Aset : Set (Fin n)) (σ : Fin n → Bool) : Set (Fin n ⊕ Fin n) :=
  {p | ∃ a ∈ Aset, p = kap a (σ a)}

theorem pSet_disj (Aset : Set (Fin n)) (σ : Fin n → Bool) :
    ∀ p ∈ pSet Aset σ, bar p ∉ pSet Aset σ := by
  rintro p ⟨a, ha, rfl⟩ ⟨b, hb, h⟩
  rw [bar_kap] at h
  obtain ⟨rfl, h2⟩ := kap_inj h
  cases e : σ a <;> simp_all

end CFSG.HardMathSupport.Cooperstein.StructureLie
