module

public import CFSG.GH74.GLS.C3.Layer2.L4ModelE1

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

theorem wStdE1_mem_Fgrp : wStdE1 7 ∈ Fgrp 7 := by
  refine ⟨?_, ?_⟩
  · show (1 : Perm (Fin 4)) * x4 = x4 * 1
    simp
  · show sign (swap (4 : Fin 7) 5 * swap 5 6) = sign (1 : Perm (Fin 4))
    rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
    simp

theorem wStdE1_pow_three : wStdE1 7 ^ 3 = 1 := by decide

theorem wStdE1_ne_one : wStdE1 7 ≠ 1 := by decide

theorem orderOf_wStdE1 : orderOf (wStdE1 7) = 3 :=
  orderOf_eq_prime wStdE1_pow_three wStdE1_ne_one

namespace Tab

variable {n : ℕ} [NeZero n] (T : Tab n)

@[expose] def wActE3 : Vector ℕ 64 :=
  Vector.ofFn fun i =>
    if T.el.get i * wStdE1 n * (T.el.get i)⁻¹ = wStdE1 n then 0
    else if T.el.get i * wStdE1 n * (T.el.get i)⁻¹ = (wStdE1 n)⁻¹ then 1 else 2

@[expose] def wCommE3 : Vector Bool 64 :=
  Vector.ofFn fun i => decide (wStdE1 n * T.el.get i = T.el.get i * wStdE1 n)

@[expose] def wActOKE3 : Bool :=
  let wA := T.wActE3
  (List.finRange 64).all fun i => wA.get i != 2

@[expose] def aVecE3 (E0 : Vector Bool 64) : Vector Bool 64 :=
  Vector.ofFn fun i => (List.finRange 64).all fun j => imp (E0.get j) (T.mulT i j == T.mulT j i)

@[expose] def bVecE3 (A0 E0 X0 : Vector Bool 64) : Vector (Fin 64) 4 :=
  let L := (List.finRange 64).filter fun i => A0.get i && T.isInv i && X0.get i && !E0.get i
  Vector.ofFn fun k => L.getD k.1 T.one

@[expose] def conjE3 (i x : Fin 64) : Fin 64 := T.mulT (T.mulT i x) (T.inv.get i)

@[expose] def pairE3 (A0 : Vector Bool 64) (it iy : Fin 64) : Bool :=
  T.isInv it && T.isInv iy && !A0.get it && !A0.get iy && T.mulT it iy == T.mulT iy it

@[expose] def quadE3 (B : Vector (Fin 64) 4) (it iy : Fin 64) (p1 p2 q1 q2 : Fin 4) : Bool :=
  p1 != p2 && p1 != q1 && p1 != q2 && p2 != q1 && p2 != q2 && q1 != q2 &&
  T.conjE3 it (B.get p1) == B.get p2 && T.conjE3 it (B.get p2) == B.get p1 &&
  T.conjE3 it (B.get q1) == B.get q1 && T.conjE3 it (B.get q2) == B.get q2 &&
  T.conjE3 iy (B.get p1) == B.get p1 && T.conjE3 iy (B.get p2) == B.get p2 &&
  T.conjE3 iy (B.get q1) == B.get q2 && T.conjE3 iy (B.get q2) == B.get q1

theorem pairE3_intro (A0 : Vector Bool 64) {it iy : Fin 64} (h1 : T.isInv it = true)
    (h2 : T.isInv iy = true) (h3 : A0.get it = false) (h4 : A0.get iy = false)
    (h5 : T.mulT it iy = T.mulT iy it) : T.pairE3 A0 it iy = true := by
  simp [pairE3, h1, h2, h3, h4, h5]

theorem pairE3_elim (A0 : Vector Bool 64) {it iy : Fin 64} (h : T.pairE3 A0 it iy = true) :
    T.isInv it = true ∧ T.isInv iy = true ∧ A0.get it = false ∧ A0.get iy = false ∧
      T.mulT it iy = T.mulT iy it := by
  simpa only [pairE3, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, and_assoc] using h

theorem quadE3_intro (B : Vector (Fin 64) 4) {it iy : Fin 64} {p1 p2 q1 q2 : Fin 4}
    (d1 : p1 ≠ p2) (d2 : p1 ≠ q1) (d3 : p1 ≠ q2) (d4 : p2 ≠ q1) (d5 : p2 ≠ q2) (d6 : q1 ≠ q2)
    (c1 : T.conjE3 it (B.get p1) = B.get p2) (c2 : T.conjE3 it (B.get p2) = B.get p1)
    (c3 : T.conjE3 it (B.get q1) = B.get q1) (c4 : T.conjE3 it (B.get q2) = B.get q2)
    (c5 : T.conjE3 iy (B.get p1) = B.get p1) (c6 : T.conjE3 iy (B.get p2) = B.get p2)
    (c7 : T.conjE3 iy (B.get q1) = B.get q2) (c8 : T.conjE3 iy (B.get q2) = B.get q1) :
    T.quadE3 B it iy p1 p2 q1 q2 = true := by
  simp [quadE3, d1, d2, d3, d4, d5, d6, c1, c2, c3, c4, c5, c6, c7, c8]

theorem quadE3_elim (B : Vector (Fin 64) 4) {it iy : Fin 64} {p1 p2 q1 q2 : Fin 4}
    (h : T.quadE3 B it iy p1 p2 q1 q2 = true) :
    p1 ≠ p2 ∧ p1 ≠ q1 ∧ p1 ≠ q2 ∧ p2 ≠ q1 ∧ p2 ≠ q2 ∧ q1 ≠ q2 ∧
      T.conjE3 it (B.get p1) = B.get p2 ∧ T.conjE3 it (B.get p2) = B.get p1 ∧
      T.conjE3 it (B.get q1) = B.get q1 ∧ T.conjE3 it (B.get q2) = B.get q2 ∧
      T.conjE3 iy (B.get p1) = B.get p1 ∧ T.conjE3 iy (B.get p2) = B.get p2 ∧
      T.conjE3 iy (B.get q1) = B.get q2 ∧ T.conjE3 iy (B.get q2) = B.get q1 := by
  simpa only [quadE3, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, and_assoc] using h

@[expose] def e3P (wA : Vector ℕ 64) (wC : Vector Bool 64) (a : Tbl) (_u : Fin 64) : Bool :=
  let E0 := T.eVecE1 a
  let A0 := T.aVecE3 E0
  let X0 := T.reach a T.x0i
  let B := T.bVecE3 A0 E0 X0
  decide (
    (∀ i j : Fin 64, T.isInv i = true → T.isInv j = true → T.mulT i j = T.mulT j i → i ≠ j →
        T.isInv (T.mulT i j) = true) ∧
    T.isInv (T.vIE1 a) = true ∧
    (∀ j : Fin 64, E0.get j = true → wC.get j = true) ∧
    (∀ i : Fin 64, A0.get i = true → E0.get i = false → wA.get i = 1)) &&
  decide (
    (∀ k : Fin 4, A0.get (B.get k) = true ∧ T.isInv (B.get k) = true ∧ X0.get (B.get k) = true ∧
        E0.get (B.get k) = false) ∧
    (∀ k k' : Fin 4, B.get k = B.get k' → k = k') ∧
    (∀ i : Fin 64, A0.get i = true → T.isInv i = true → X0.get i = true → E0.get i = false →
        ∃ k : Fin 4, i = B.get k)) &&
  decide (∀ it iy : Fin 64, T.pairE3 A0 it iy = true →
    ∀ p1 p2 q1 q2 : Fin 4, T.quadE3 B it iy p1 p2 q1 q2 = true → wA.get it = 0) &&
  decide (∃ it iy : Fin 64, T.pairE3 A0 it iy = true ∧
    ∃ p1 p2 q1 q2 : Fin 4, T.quadE3 B it iy p1 p2 q1 q2 = true)

theorem wActE3_spec (i : Fin 64) :
    (T.wActE3.get i = 0 → T.el.get i * wStdE1 n * (T.el.get i)⁻¹ = wStdE1 n) ∧
    (T.wActE3.get i = 1 → T.el.get i * wStdE1 n * (T.el.get i)⁻¹ = (wStdE1 n)⁻¹) := by
  simp only [wActE3, vget_ofFn]
  split_ifs with h1 h2
  · exact ⟨fun _ => h1, fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd h (by decide), fun _ => h2⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

theorem wActOKE3_spec (h : T.wActOKE3 = true) (i : Fin 64) :
    T.el.get i * wStdE1 n * (T.el.get i)⁻¹ = wStdE1 n ∨
      T.el.get i * wStdE1 n * (T.el.get i)⁻¹ = (wStdE1 n)⁻¹ := by
  unfold wActOKE3 at h
  simp only [List.all_eq_true, List.mem_finRange, true_implies, wActE3, vget_ofFn] at h
  have hi := h i
  split_ifs at hi with h1 h2
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd hi (by decide)

theorem wCommE3_spec (j : Fin 64) (h : T.wCommE3.get j = true) :
    wStdE1 n * T.el.get j = T.el.get j * wStdE1 n := by
  simp only [wCommE3, vget_ofFn, decide_eq_true_eq] at h
  exact h

theorem conjE3_iT
    (hn : n = 6 ∨ n = 7) (hv : T.Valid) (i x : Fin 64) :
    T.iT hn hv (T.conjE3 i x) = T.iT hn hv i * T.iT hn hv x * (T.iT hn hv i)⁻¹ := by
  simp only [conjE3]
  rw [iT_mul, iT_mul, iT_inv]

end Tab

theorem fin4_exhaustE3 : ∀ x x' z z' : Fin 4, x ≠ x' → x ≠ z → x ≠ z' → x' ≠ z → x' ≠ z' →
    z ≠ z' → ∀ i : Fin 4, i = x ∨ i = x' ∨ i = z ∨ i = z' := by decide

theorem fix_of_swapE3 {a b c : Fin 4} (hab : a ≠ b) (h : swap a b c = c) : c ≠ a ∧ c ≠ b := by
  constructor
  · rintro rfl
    rw [swap_apply_left] at h
    exact hab h.symm
  · rintro rfl
    rw [swap_apply_right] at h
    exact hab h

theorem model_E3_aux
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) (hn7 : n = 7) (T : Tab n)
    (hv : T.Valid) (hcB : T.claimB = true)
    (hc : T.claimG (T.e3P T.wActE3 T.wCommE3) = true) (hact : T.wActOKE3 = true)
    (α : T0 n ≃* T0 n) (u : T0 n) (X V : Set (T0 n))
    (hx : α (x0T n) ≠ x0T n) (hu : α u = u) (hsq : ∀ x, α (α x) = u * x * u⁻¹)
    (hext : n = 7 →
      ∃ β : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)) ≃* ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)),
        ∀ (x : T0 n) (hx : (x : Amb n) ∈ Hgrp n ((α (x0T n) : T0 n) : Amb n)),
          ((β ⟨(x : Amb n), hx⟩ : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n))) : Amb n) =
            ((α x : T0 n) : Amb n))
    (hX : x0T n ∈ X) (hV : x0T n * α (x0T n) ∈ V) (hdisj : Disjoint X V)
    (hclX : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ X → t ∈ X)
    (hclV : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ V → t ∈ V)
    (hQ : ∀ q : T0 n, (q : Amb n).1 = 1 → q ≠ 1 → q ∉ V)
    (E : Subgroup (T0 n))
    (hE : ∀ t : T0 n, t ∈ E ↔ (t = 1 ∨ t = vHat n α ∨
        (orderOf t = 2 ∧ t ∈ X ∧ t * vHat n α = vHat n α * t ∧ t * vHat n α ∈ X)))
    (A : Subgroup (T0 n)) (hA : ∀ t : T0 n, t ∈ A ↔ ∀ e ∈ E, t * e = e * t)
    (b : Fin 4 → T0 n) (hbinj : Function.Injective b)
    (hb1 : ∀ i, b i ∈ A ∧ orderOf (b i) = 2 ∧ b i ∈ X ∧ b i ∉ E)
    (hb2 : ∀ t ∈ A, orderOf t = 2 → t ∈ X → t ∉ E → ∃ i, t = b i)
    (hcover : ∀ g ∈ Fgrp n, g * ((vHat n α : T0 n) : Amb n) = ((vHat n α : T0 n) : Amb n) * g →
        ∃ t : T0 n, ∃ j : ℕ, j < 3 ∧ g = (t : Amb n) * wStdE1 n ^ j) :
    ∃ w : Amb n, w ∈ Fgrp n ∧ orderOf w = 3 ∧ (∀ e ∈ liftT n E, w * e = e * w) ∧
      (∀ g ∈ Fgrp n ⊓ Subgroup.centralizer (liftT n E : Set (Amb n)),
        ∃ k : ℕ, ∃ t ∈ A, g = w ^ k * ((t : T0 n) : Amb n)) ∧
      (∀ g ∈ Fgrp n, g * ((vHat n α : T0 n) : Amb n) = ((vHat n α : T0 n) : Amb n) * g →
        ∃ k : ℤ, g * w * g⁻¹ = w ^ k) ∧
      (∀ t ∈ A, t ∉ E → ((t : T0 n) : Amb n) * w * ((t : T0 n) : Amb n)⁻¹ = w⁻¹) ∧
      (∀ (t y : T0 n) (π₁ π₂ : Equiv.Perm (Fin 4)), t ∉ A → y ∉ A → orderOf t = 2 →
        orderOf y = 2 → t * y = y * t → π₁.IsSwap → π₂.IsSwap → Disjoint π₁ π₂ →
        (∀ i, t * b i * t⁻¹ = b (π₁ i)) → (∀ i, y * b i * y⁻¹ = b (π₂ i)) →
        ((t : T0 n) : Amb n) * w = w * ((t : T0 n) : Amb n)) ∧
      (∃ t y : T0 n, t ∉ A ∧ y ∉ A ∧ orderOf t = 2 ∧ orderOf y = 2 ∧ t * y = y * t ∧
        ∃ π₁ π₂ : Equiv.Perm (Fin 4), π₁.IsSwap ∧ π₂.IsSwap ∧ Disjoint π₁ π₂ ∧
          (∀ i, t * b i * t⁻¹ = b (π₁ i)) ∧ (∀ i, y * b i * y⁻¹ = b (π₂ i))) := by
  subst hn7
  obtain ⟨_, -, hP, hXc, -⟩ := T.facts_of_claimG hn hv hcB _ hc α u X V hx hu hsq hext hX hV
    hdisj hclX hclV hQ
  have ha : ∀ i, T.iT hn hv ((T.tabOf hn hv α).get i) = α (T.iT hn hv i) :=
    T.iT_tabOf hn hv α
  have hclX' := Tab.edge_closed T hn hv α X hclX
  have hX0 := Tab.reach_sound T hn hv (T.tabOf hn hv α) X hclX' T.x0i
    (by rw [Tab.iT_x0]; exact hX)
  unfold Tab.e3P at hP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨⟨⟨hF1, hvinv, hwE, hwA⟩, ⟨hB1, hBinj, hBc⟩⟩, hF⟩, hG⟩ := hP
  set a : Tbl := T.tabOf hn hv α
  set E0 := T.eVecE1 a
  set A0 := T.aVecE3 E0
  set X0 := T.reach a T.x0i
  set B := T.bVecE3 A0 E0 X0
  have hEm : ∀ i, E0.get i = true ↔ T.iT hn hv i ∈ E := fun i =>
    (T.eVecE1_iff hn hv α X a ha hXc hX0 hF1 hvinv i).trans (hE _).symm
  have hAm : ∀ i, A0.get i = true ↔ T.iT hn hv i ∈ A := by
    intro i
    rw [hA]
    simp only [A0, Tab.aVecE3, vget_ofFn, List.all_eq_true, List.mem_finRange, true_implies,
      imp_eq_true, beq_iff_eq]
    constructor
    · intro h e he
      obtain ⟨j, rfl⟩ := T.iT_surjective hn hv e
      rw [← Tab.iT_mul, ← Tab.iT_mul, h j ((hEm j).2 he)]
    · intro h j hj
      have := h _ ((hEm j).1 hj)
      rw [← Tab.iT_mul, ← Tab.iT_mul] at this
      exact T.iT_injective hn hv this
  have hw3 := wStdE1_pow_three
  have hwinv : (wStdE1 7)⁻¹ = wStdE1 7 ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    exact hw3
  have hwE' : ∀ e ∈ liftT 7 E, wStdE1 7 * e = e * wStdE1 7 := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.1 he
    obtain ⟨j, rfl⟩ := T.iT_surjective hn hv e'
    exact T.wCommE3_spec j (hwE j ((hEm j).2 he'))
  have hInv : ∀ t ∈ A, t ∉ E →
      ((t : T0 7) : Amb 7) * wStdE1 7 * ((t : T0 7) : Amb 7)⁻¹ = (wStdE1 7)⁻¹ := by
    intro t htA htE
    obtain ⟨i, rfl⟩ := T.iT_surjective hn hv t
    have h1 := (hAm i).2 htA
    have h2 : E0.get i = false := by
      cases h : E0.get i
      · rfl
      · exact absurd ((hEm i).1 h) htE
    exact (T.wActE3_spec i).2 (hwA i h1 h2)
  have hvE : ((vHat 7 α : T0 7) : Amb 7) ∈ (liftT 7 E : Set (Amb 7)) :=
    ⟨vHat 7 α, (hE _).2 (Or.inr (Or.inl rfl)), rfl⟩
  have hτ0 : ∀ x : Fin 4, ∃ k : Fin 4, b x = T.iT hn hv (B.get k) := by
    intro x
    obtain ⟨hbA, hb2', hbX, hbE⟩ := hb1 x
    obtain ⟨i, hi⟩ := T.iT_surjective hn hv (b x)
    have hinv : T.isInv i = true := T.isInv_of_orderOf_iTE1 hn hv (by rw [hi]; exact hb2')
    have hA0 := (hAm i).2 (by rw [hi]; exact hbA)
    have hX0' := (hXc i hinv).2 (by rw [hi]; exact hbX)
    have hE0 : E0.get i = false := by
      cases h : E0.get i
      · rfl
      · exact absurd (by rw [← hi]; exact (hEm i).1 h) hbE
    obtain ⟨k, hk⟩ := hBc i hA0 hinv hX0' hE0
    exact ⟨k, by rw [← hi, hk]⟩
  choose τ hτ using hτ0
  refine ⟨wStdE1 7, wStdE1_mem_Fgrp, orderOf_wStdE1, hwE', ?_, ?_, hInv, ?_, ?_⟩
  ·
    intro g hg
    obtain ⟨hgF, hgc⟩ := Subgroup.mem_inf.1 hg
    have hgcm := Subgroup.mem_centralizer_iff.1 hgc
    obtain ⟨t, j, hj, hgt⟩ := hcover g hgF (hgcm _ hvE).symm
    have hwj : ∀ e ∈ liftT 7 E, wStdE1 7 ^ j * e = e * wStdE1 7 ^ j := fun e he =>
      ((Commute.pow_left (hwE' e he) j))
    have htA : t ∈ A := by
      rw [hA]
      intro e he
      have h1 : (e : Amb 7) * g = g * (e : Amb 7) := hgcm _ ⟨e, he, rfl⟩
      have h2 : wStdE1 7 ^ j * (e : Amb 7) = (e : Amb 7) * wStdE1 7 ^ j := hwj _ ⟨e, he, rfl⟩
      apply Subtype.ext
      show (t : Amb 7) * (e : Amb 7) = (e : Amb 7) * (t : Amb 7)
      rw [hgt] at h1
      have h3 : (e : Amb 7) * (t : Amb 7) * wStdE1 7 ^ j = (t : Amb 7) * (e : Amb 7) * wStdE1 7 ^ j := by
        calc (e : Amb 7) * (t : Amb 7) * wStdE1 7 ^ j = (e : Amb 7) * ((t : Amb 7) * wStdE1 7 ^ j) := by
              rw [mul_assoc]
          _ = ((t : Amb 7) * wStdE1 7 ^ j) * (e : Amb 7) := h1
          _ = (t : Amb 7) * (wStdE1 7 ^ j * (e : Amb 7)) := by rw [mul_assoc]
          _ = (t : Amb 7) * ((e : Amb 7) * wStdE1 7 ^ j) := by rw [h2]
          _ = (t : Amb 7) * (e : Amb 7) * wStdE1 7 ^ j := by rw [mul_assoc]
      exact (mul_right_cancel h3).symm
    by_cases htE : t ∈ E
    · refine ⟨j, t, htA, ?_⟩
      rw [hgt]
      have hc : Commute (wStdE1 7) (t : Amb 7) := hwE' (t : Amb 7) ⟨t, htE, rfl⟩
      exact (hc.symm.pow_right j).eq
    · refine ⟨2 * j, t, htA, ?_⟩
      rw [hgt]
      have h := hInv t htA htE
      rw [hwinv] at h
      have h' : (t : Amb 7) * wStdE1 7 ^ j * (t : Amb 7)⁻¹ = wStdE1 7 ^ (2 * j) := by
        rw [← conj_pow, h, ← pow_mul]
      calc (t : Amb 7) * wStdE1 7 ^ j = (t : Amb 7) * wStdE1 7 ^ j * (t : Amb 7)⁻¹ * (t : Amb 7) := by
            group
        _ = wStdE1 7 ^ (2 * j) * (t : Amb 7) := by rw [h']
  ·
    intro g hgF hgv
    obtain ⟨t, j, hj, hgt⟩ := hcover g hgF hgv
    have hg' : g * wStdE1 7 * g⁻¹ = (t : Amb 7) * wStdE1 7 * (t : Amb 7)⁻¹ := by
      rw [hgt]
      group
    rw [hg']
    have := T.wActOKE3_spec hact ((T.eT hn hv).symm t)
    have e1 : T.el.get ((T.eT hn hv).symm t) = (t : Amb 7) := by
      rw [← Tab.iT_coe T hn hv, T.iT_eT_symmE1 hn hv]
    rw [e1] at this
    rcases this with h | h
    · exact ⟨1, by rw [h, zpow_one]⟩
    · exact ⟨-1, by rw [h, zpow_neg_one]⟩
  ·
    intro t y π₁ π₂ htA hyA ht2 hy2 hty hπ₁ hπ₂ hdis hact1 hact2
    obtain ⟨x, x', hxx', rfl⟩ := hπ₁
    obtain ⟨z, z', hzz', rfl⟩ := hπ₂
    have d1 : x ≠ z ∧ x ≠ z' := by
      rcases hdis x with h | h
      · rw [swap_apply_left] at h
        exact absurd h.symm hxx'
      · exact fix_of_swapE3 hzz' h
    have d2 : x' ≠ z ∧ x' ≠ z' := by
      rcases hdis x' with h | h
      · rw [swap_apply_right] at h
        exact absurd h hxx'
      · exact fix_of_swapE3 hzz' h
    have hτinj : ∀ p q, p ≠ q → τ p ≠ τ q := by
      intro p q hpq h
      apply hpq
      apply hbinj
      rw [hτ p, hτ q, h]
    have hconj : ∀ (s : T0 7) (p q : Fin 4), s * b p * s⁻¹ = b q →
        T.conjE3 ((T.eT hn hv).symm s) (B.get (τ p)) = B.get (τ q) := by
      intro s p q h
      apply T.iT_injective hn hv
      rw [T.conjE3_iT hn hv, T.iT_eT_symmE1 hn hv, ← hτ p, ← hτ q]
      exact h
    have hit : T.isInv ((T.eT hn hv).symm t) = true := T.isInv_of_orderOf hn hv ht2
    have hiy : T.isInv ((T.eT hn hv).symm y) = true := T.isInv_of_orderOf hn hv hy2
    have hAit : A0.get ((T.eT hn hv).symm t) = false := by
      cases h : A0.get ((T.eT hn hv).symm t)
      · rfl
      · exact absurd (by rw [← T.iT_eT_symmE1 hn hv t]; exact (hAm _).1 h) htA
    have hAiy : A0.get ((T.eT hn hv).symm y) = false := by
      cases h : A0.get ((T.eT hn hv).symm y)
      · rfl
      · exact absurd (by rw [← T.iT_eT_symmE1 hn hv y]; exact (hAm _).1 h) hyA
    have hcomm : T.mulT ((T.eT hn hv).symm t) ((T.eT hn hv).symm y) =
        T.mulT ((T.eT hn hv).symm y) ((T.eT hn hv).symm t) := by
      apply T.iT_injective hn hv
      rw [Tab.iT_mul, Tab.iT_mul, T.iT_eT_symmE1 hn hv, T.iT_eT_symmE1 hn hv]
      exact hty
    have a1 := hact1 x
    have a2 := hact1 x'
    have a3 := hact1 z
    have a4 := hact1 z'
    have b1 := hact2 x
    have b2 := hact2 x'
    have b3 := hact2 z
    have b4 := hact2 z'
    rw [swap_apply_left] at a1
    rw [swap_apply_right] at a2
    rw [swap_apply_of_ne_of_ne d1.1.symm d2.1.symm] at a3
    rw [swap_apply_of_ne_of_ne d1.2.symm d2.2.symm] at a4
    rw [swap_apply_of_ne_of_ne d1.1 d1.2] at b1
    rw [swap_apply_of_ne_of_ne d2.1 d2.2] at b2
    rw [swap_apply_left] at b3
    rw [swap_apply_right] at b4
    have key := hF _ _ (T.pairE3_intro A0 hit hiy hAit hAiy hcomm) (τ x) (τ x') (τ z) (τ z')
      (T.quadE3_intro B (hτinj _ _ hxx') (hτinj _ _ d1.1) (hτinj _ _ d1.2) (hτinj _ _ d2.1)
        (hτinj _ _ d2.2) (hτinj _ _ hzz') (hconj _ _ _ a1) (hconj _ _ _ a2) (hconj _ _ _ a3)
        (hconj _ _ _ a4) (hconj _ _ _ b1) (hconj _ _ _ b2) (hconj _ _ _ b3) (hconj _ _ _ b4))
    have h0 := (T.wActE3_spec ((T.eT hn hv).symm t)).1 key
    have e1 : T.el.get ((T.eT hn hv).symm t) = (t : Amb 7) := by
      rw [← Tab.iT_coe T hn hv, T.iT_eT_symmE1 hn hv]
    rw [e1] at h0
    exact mul_inv_eq_iff_eq_mul.1 h0
  ·
    obtain ⟨it, iy, hpair, p1, p2, q1, q2, hquad⟩ := hG
    obtain ⟨hit, hiy, hAit, hAiy, hcomm⟩ := T.pairE3_elim A0 hpair
    obtain ⟨hp12, hp1q1, hp1q2, hp2q1, hp2q2, hq12, c1, c2, c3, c4, c5, c6, c7, c8⟩ :=
      T.quadE3_elim B hquad
    have hpull : ∀ p : Fin 4, ∃ x : Fin 4, T.iT hn hv (B.get p) = b x := by
      intro p
      obtain ⟨hA0, hinv, hX0', hE0⟩ := hB1 p
      refine hb2 _ ((hAm _).1 hA0) (T.orderOf_iT_of_isInv hn hv hinv) ((hXc _ hinv).1 hX0') ?_
      intro h
      have := (hEm _).2 h
      rw [hE0] at this
      exact Bool.false_ne_true this
    choose xx hxx using hpull
    have hxxinj : ∀ p q, p ≠ q → xx p ≠ xx q := by
      intro p q hpq h
      apply hpq
      apply hBinj
      apply T.iT_injective hn hv
      rw [hxx p, hxx q, h]
    have hact : ∀ (s : Fin 64) (p q : Fin 4), T.conjE3 s (B.get p) = B.get q →
        T.iT hn hv s * b (xx p) * (T.iT hn hv s)⁻¹ = b (xx q) := by
      intro s p q h
      rw [← hxx p, ← hxx q, ← T.conjE3_iT hn hv, h]
    have hxy : xx p1 ≠ xx p2 := hxxinj _ _ hp12
    have hxz : xx p1 ≠ xx q1 := hxxinj _ _ hp1q1
    have hxz' : xx p1 ≠ xx q2 := hxxinj _ _ hp1q2
    have hx'z : xx p2 ≠ xx q1 := hxxinj _ _ hp2q1
    have hx'z' : xx p2 ≠ xx q2 := hxxinj _ _ hp2q2
    have hzz' : xx q1 ≠ xx q2 := hxxinj _ _ hq12
    have hex := fin4_exhaustE3 _ _ _ _ hxy hxz hxz' hx'z hx'z' hzz'
    refine ⟨T.iT hn hv it, T.iT hn hv iy, ?_, ?_, ?_, ?_, ?_, swap (xx p1) (xx p2),
      swap (xx q1) (xx q2), ⟨xx p1, xx p2, hxy, rfl⟩, ⟨xx q1, xx q2, hzz', rfl⟩, ?_, ?_, ?_⟩
    · intro h
      have := (hAm it).2 h
      rw [hAit] at this
      exact Bool.false_ne_true this
    · intro h
      have := (hAm iy).2 h
      rw [hAiy] at this
      exact Bool.false_ne_true this
    · exact T.orderOf_iT_of_isInv hn hv hit
    · exact T.orderOf_iT_of_isInv hn hv hiy
    · rw [← Tab.iT_mul, ← Tab.iT_mul, hcomm]
    ·
      intro i
      rcases hex i with rfl | rfl | rfl | rfl
      · right
        exact swap_apply_of_ne_of_ne hxz hxz'
      · right
        exact swap_apply_of_ne_of_ne hx'z hx'z'
      · left
        exact swap_apply_of_ne_of_ne hxz.symm hx'z.symm
      · left
        exact swap_apply_of_ne_of_ne hxz'.symm hx'z'.symm
    · intro i
      rcases hex i with rfl | rfl | rfl | rfl
      · rw [swap_apply_left]
        exact hact _ _ _ c1
      · rw [swap_apply_right]
        exact hact _ _ _ c2
      · rw [swap_apply_of_ne_of_ne hxz.symm hx'z.symm]
        exact hact _ _ _ c3
      · rw [swap_apply_of_ne_of_ne hxz'.symm hx'z'.symm]
        exact hact _ _ _ c4
    · intro i
      rcases hex i with rfl | rfl | rfl | rfl
      · rw [swap_apply_of_ne_of_ne hxz hxz']
        exact hact _ _ _ c5
      · rw [swap_apply_of_ne_of_ne hx'z hx'z']
        exact hact _ _ _ c6
      · rw [swap_apply_left]
        exact hact _ _ _ c7
      · rw [swap_apply_right]
        exact hact _ _ _ c8

end CFSG.GH74.GLS.C3.Layer2.Model
