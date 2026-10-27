module

public import CFSG.ClassicalInvolution.Phan.PhanQ13Bridge
public import CFSG.ClassicalInvolution.Phan.PhanD3Coord

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanD4
  CFSG.ClassicalInvolution.ModelFacts.MF15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs

section Support

variable {R : Type} [Field R]

@[expose] def InW0 (v : V8 R) : Prop :=
  ∀ i : Fin 4, 2 ≤ i.val → v (Sum.inl i) = 0 ∧ v (Sum.inr i) = 0

@[expose] def InW2 (v : V8 R) : Prop :=
  ∀ i : Fin 4, i.val < 2 → v (Sum.inl i) = 0 ∧ v (Sum.inr i) = 0

theorem B8_eq_zero_of_support {u v : V8 R} (hu : InW0 u) (hv : InW2 v) : B8 u v = 0 := by
  rw [B8_eq_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : 2 ≤ i.val
  · obtain ⟨h1, h2⟩ := hu i hi
    rw [h1, h2]
    ring
  · obtain ⟨h1, h2⟩ := hv i (by omega)
    rw [h1, h2]
    ring

theorem inW0_incl (X : Matrix (Fin 2) (Fin 2) R) : InW0 ((frame0 (F := R)).incl X) := by
  intro i hi
  fin_cases i <;> simp at hi ⊢ <;>
    simp [Frame.incl_apply, frame0, frameOfVectors, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂,
      vecXY]

end Support

section Ext

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem inW0_vecK {z : NPair ε} (hx : InW0 z.x) (hy : InW0 z.y) : InW0 (vecK D z) := by
  intro i hi
  obtain ⟨h1, h2⟩ := hx i hi
  obtain ⟨h3, h4⟩ := hy i hi
  simp [vecK, extV, h1, h2, h3, h4]

theorem inW2_conj {v : V8 K} (hv : InW2 v) : InW2 (conj D v) := by
  intro i hi
  obtain ⟨h1, h2⟩ := hv i hi
  simp [conj, h1, h2]

theorem her_eq_sum (u v : V8 K) :
    her D u v = ∑ i : Fin 4, (u (Sum.inl i) * D.τ (v (Sum.inr i)) +
      D.τ (v (Sum.inl i)) * u (Sum.inr i)) := by
  rw [her, B8_eq_sum]
  rfl

@[expose] def pvec1 : V8 K := Sum.elim ![0, 0, 1, D.θ] ![0, 0, D.θ ^ 2, -D.θ]

@[expose] def pvec2 : V8 K := Sum.elim ![0, 0, 1, -D.θ] ![0, 0, -D.θ ^ 2, -D.θ]

theorem inW2_pvec1 : InW2 (pvec1 D) := by
  intro i hi
  fin_cases i <;> simp [pvec1] at hi ⊢

theorem inW2_pvec2 : InW2 (pvec2 D) := by
  intro i hi
  fin_cases i <;> simp [pvec2] at hi ⊢

theorem Q8_pvec1 : Q8 (pvec1 D) = 0 := by
  rw [Q8_eq_sum]
  simp [pvec1, Fin.sum_univ_four]
  ring

theorem Q8_pvec2 : Q8 (pvec2 D) = 0 := by
  rw [Q8_eq_sum]
  simp [pvec2, Fin.sum_univ_four]
  ring

theorem tau_theta_sq : D.τ (D.θ ^ 2) = D.θ ^ 2 := by
  rw [map_pow, D.tau_theta, neg_sq]

theorem her_pvec1 : her D (pvec1 D) (pvec1 D) = 4 * D.θ ^ 2 := by
  rw [her_eq_sum]
  simp [pvec1, Fin.sum_univ_four, D.tau_theta, tau_theta_sq D]
  ring

theorem her_pvec2 : her D (pvec2 D) (pvec2 D) = -(4 * D.θ ^ 2) := by
  rw [her_eq_sum]
  simp [pvec2, Fin.sum_univ_four, D.tau_theta, tau_theta_sq D]
  ring

theorem B8_pvec12 : B8 (pvec1 D) (pvec2 D) = 0 := by
  rw [B8_eq_sum]
  simp [pvec1, pvec2, Fin.sum_univ_four]

theorem her_pvec12 : her D (pvec1 D) (pvec2 D) = 0 := by
  rw [her_eq_sum]
  simp [pvec1, pvec2, Fin.sum_univ_four, D.tau_theta, tau_theta_sq D]

theorem ffK_pvec1 (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) : ffK D (pvec1 D) := by
  refine ⟨Q8_pvec1 D, ?_⟩
  rw [her_pvec1]
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  exact mul_ne_zero h4 (pow_ne_zero 2 (theta_ne_zero D hε))

theorem ffK_pvec2 (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) : ffK D (pvec2 D) := by
  refine ⟨Q8_pvec2 D, ?_⟩
  rw [her_pvec2]
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  exact neg_ne_zero.2 (mul_ne_zero h4 (pow_ne_zero 2 (theta_ne_zero D hε)))

theorem colK_smul_left {κ : K} (hκ : κ ≠ 0) {u v : V8 K} :
    ColK D (κ • u) v ↔ ColK D u v := by
  have := colK_smul D hκ (one_ne_zero (α := K)) (u := u) (v := v)
  rwa [one_smul] at this

end Ext

section Pent

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε) [Fintype K]
  [DecidableEq K]

theorem exists_pent_point_K (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) {c d : NPair ε}
    (hc : InW0 c.x ∧ InW0 c.y) (hd : InW0 d.x ∧ InW0 d.y) (hcd : ColP ε c d) {a : V8 K}
    (ha : ffK D a) :
    ∃ f : V8 K, ffK D f ∧ ColK D f (vecK D c) ∧ ColK D f (vecK D d) ∧ ColK D f a := by
  have hic := inW0_vecK D hc.1 hc.2
  have hid := inW0_vecK D hd.1 hd.2
  have hic' : InW0 (conj D (vecK D c)) := by
    intro i hi
    obtain ⟨h1, h2'⟩ := hic i hi
    simp [conj, h1, h2']
  have hid' : InW0 (conj D (vecK D d)) := by
    intro i hi
    obtain ⟨h1, h2'⟩ := hid i hi
    simp [conj, h1, h2']
  have hHc : ∀ {p : V8 K}, InW2 p → her D (vecK D c) p = 0 := fun hp =>
    B8_eq_zero_of_support hic (inW2_conj D hp)
  have hHd : ∀ {p : V8 K}, InW2 p → her D (vecK D d) p = 0 := fun hp =>
    B8_eq_zero_of_support hid (inW2_conj D hp)
  exact pentK D h2 hε hq2 hq5 (ffK_vecK D h2 hε c) (ffK_vecK D h2 hε d)
    ((colK_vecK_iff D h2 hε).2 hcd) (ffK_pvec1 D h2 hε) (ffK_pvec2 D h2 hε) (B8_pvec12 D)
    (her_pvec12 D) (B8_eq_zero_of_support hic (inW2_pvec1 D))
    (B8_eq_zero_of_support hic (inW2_pvec2 D)) (B8_eq_zero_of_support hid (inW2_pvec1 D))
    (B8_eq_zero_of_support hid (inW2_pvec2 D)) (hHc (inW2_pvec1 D)) (hHc (inW2_pvec2 D))
    (hHd (inW2_pvec1 D)) (hHd (inW2_pvec2 D)) ha

include D in
theorem exists_pent_inW0 [Finite F] (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0)
    (hε : ε ≠ 0) (hq2 : 2 ≤ Nat.card F) (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2)
    {c d : NPair ε} (hc : InW0 c.x ∧ InW0 c.y) (hd : InW0 d.x ∧ InW0 d.y) (hcd : ColP ε c d)
    (a : NPair ε) : ∃ f : NPair ε, ColP ε f c ∧ ColP ε f d ∧ ColP ε a f := by
  obtain ⟨fK, hff, h1, h2', h3⟩ :=
    exists_pent_point_K D h2 hε hq2 hq5 hc hd hcd (ffK_vecK D h2 hε a)
  obtain ⟨κ, hκ, f, rfl⟩ := exists_npair_of_ffK D hodd h2 hε hff
  rw [colK_smul_left D hκ] at h1 h2' h3
  refine ⟨f, ?_, ?_, ?_⟩
  · exact (colK_vecK_iff D h2 hε).1 h1
  · exact (colK_vecK_iff D h2 hε).1 h2'
  · exact ((colK_vecK_iff D h2 hε).1 h3.symm)

end Pent

end CFSG.ClassicalInvolution.PhanQ
