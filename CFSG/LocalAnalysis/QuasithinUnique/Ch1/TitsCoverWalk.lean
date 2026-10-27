module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.Ch1.TitsCover

abbrev Letter := Fin 2 × Bool

@[expose] def fo (n : ℕ) : Fin 2 := ⟨n % 2, Nat.mod_lt n (by norm_num)⟩

theorem fo_edge (v : ℕ) (i : Fin 2) : fo (2 * v + i) = i := by
  ext
  simp only [fo]
  omega

@[expose] def posW (w : List (Fin 2)) : List Letter := w.map fun i => (i, true)

@[expose] def invW (w : List (Fin 2)) : List Letter := w.reverse.map fun i => (i, false)

structure CayTab where
  nV : ℕ
  word : ℕ → List (Fin 2)
  tgt : ℕ → Fin 2 → ℕ
  back : ℕ → Fin 2 → ℕ

namespace CayTab

variable (T : CayTab)

@[expose] def step (v : ℕ) (l : Letter) : ℕ := if l.2 then T.tgt v l.1 else T.back v l.1

@[expose] def edge (v : ℕ) (l : Letter) : ℕ :=
  if l.2 then 2 * v + l.1 else 2 * T.back v l.1 + l.1

@[expose] def walkEnd : ℕ → List Letter → ℕ
  | v, [] => v
  | v, l :: w => walkEnd (T.step v l) w

@[expose] def walkEdges : ℕ → List Letter → List ℕ
  | _, [] => []
  | v, l :: w => T.edge v l :: walkEdges (T.step v l) w

variable {G : Type*} [Group G]

@[expose] def el (x : Fin 2 → G) (v : ℕ) : G := ((T.word v).map x).prod

structure Good (x : Fin 2 → G) : Prop where
  word_zero : T.word 0 = []
  zero_lt : 0 < T.nV
  tgt_lt : ∀ v < T.nV, ∀ i, T.tgt v i < T.nV
  back_lt : ∀ v < T.nV, ∀ i, T.back v i < T.nV
  el_tgt : ∀ v < T.nV, ∀ i, T.el x (T.tgt v i) = T.el x v * x i
  tgt_back : ∀ v < T.nV, ∀ i, T.tgt (T.back v i) i = v
  el_inj : ∀ u < T.nV, ∀ v < T.nV, T.el x u = T.el x v → u = v

end CayTab

namespace CayTab

variable {G : Type*} [Group G] {T : CayTab} {x : Fin 2 → G}

theorem Good.step_lt (hT : T.Good x) {v : ℕ} (hv : v < T.nV) (l : Letter) : T.step v l < T.nV := by
  unfold step
  split_ifs
  · exact hT.tgt_lt v hv _
  · exact hT.back_lt v hv _

theorem Good.edge_lt (hT : T.Good x) {v : ℕ} (hv : v < T.nV) (l : Letter) :
    T.edge v l < 2 * T.nV := by
  unfold edge
  split_ifs
  · have := l.1.2
    omega
  · have := hT.back_lt v hv l.1
    have := l.1.2
    omega

theorem Good.walkEnd_lt (hT : T.Good x) {v : ℕ} (hv : v < T.nV) :
    ∀ w : List Letter, T.walkEnd v w < T.nV := by
  intro w
  induction w generalizing v with
  | nil => exact hv
  | cons l w ih => exact ih (hT.step_lt hv l)

theorem Good.walkEdges_lt (hT : T.Good x) {v : ℕ} (hv : v < T.nV) :
    ∀ w : List Letter, ∀ e ∈ T.walkEdges v w, e < 2 * T.nV := by
  intro w
  induction w generalizing v with
  | nil => intro e he; simp [walkEdges] at he
  | cons l w ih =>
    intro e he
    simp only [walkEdges, List.mem_cons] at he
    rcases he with rfl | he
    · exact hT.edge_lt hv l
    · exact ih (hT.step_lt hv l) e he

theorem Good.el_walk (hT : T.Good x) {u : ℕ} (hu : u < T.nV) (w : List (Fin 2)) :
    T.el x (T.walkEnd u (posW w)) = T.el x u * (w.map x).prod := by
  induction w generalizing u with
  | nil => simp [posW, walkEnd]
  | cons i w ih =>
    have h := ih (hT.tgt_lt u hu i)
    simp only [posW, List.map_cons, walkEnd, step, ite_true] at h ⊢
    rw [h, hT.el_tgt u hu i]
    simp [mul_assoc]

end CayTab

structure CentralExt (E G : Type*) [Group E] [Group G] where
  φ : E →* G
  ζ : E
  ne_one : ζ ≠ 1
  sq : ζ * ζ = 1
  central : ∀ e, ζ * e = e * ζ
  ker : ∀ e, φ e = 1 → e = 1 ∨ e = ζ

section Ext

variable {E G : Type*} [Group E] [Group G] (X : CentralExt E G)

@[expose] def CentralExt.toZ (a : ZMod 2) : E := if a = 0 then 1 else X.ζ

theorem CentralExt.toZ_zero : X.toZ 0 = 1 := by simp [CentralExt.toZ]

theorem CentralExt.toZ_one : X.toZ 1 = X.ζ := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  simp [CentralExt.toZ, h10]

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem CentralExt.toZ_central (a : ZMod 2) (e : E) : X.toZ a * e = e * X.toZ a := by
  rcases zmod_two_cases a with rfl | rfl
  · simp [X.toZ_zero]
  · rw [X.toZ_one]
    exact X.central e

theorem CentralExt.toZ_add (a b : ZMod 2) : X.toZ (a + b) = X.toZ a * X.toZ b := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    simp [X.toZ_zero, X.toZ_one, h11, X.sq]

theorem CentralExt.toZ_inj {a b : ZMod 2} (h : X.toZ a = X.toZ b) : a = b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · rw [X.toZ_zero, X.toZ_one] at h
    exact absurd h.symm X.ne_one
  · rw [X.toZ_zero, X.toZ_one] at h
    exact absurd h X.ne_one
  · rfl

theorem CentralExt.toZ_inv (a : ZMod 2) : (X.toZ a)⁻¹ = X.toZ a := by
  have : X.toZ a * X.toZ a = 1 := by rw [← X.toZ_add, CharTwo.add_self_eq_zero, X.toZ_zero]
  exact inv_eq_of_mul_eq_one_right this

theorem CentralExt.exists_toZ {z : E} (hz : X.φ z = 1) : ∃ a : ZMod 2, z = X.toZ a := by
  rcases X.ker z hz with rfl | rfl
  · exact ⟨0, X.toZ_zero.symm⟩
  · exact ⟨1, X.toZ_one.symm⟩

end Ext


section Cochain

open CayTab

variable {E G : Type*} [Group E] [Group G] (X : CentralExt E G) {T : CayTab} {x : Fin 2 → G}
  (xt : Fin 2 → E)

@[expose] def sig (T : CayTab) (xt : Fin 2 → E) (v : ℕ) : E := ((T.word v).map xt).prod

@[expose] def lt (xt : Fin 2 → E) (l : Letter) : E := if l.2 then xt l.1 else (xt l.1)⁻¹

@[expose] def psi (xt : Fin 2 → E) (w : List Letter) : E := (w.map (lt xt)).prod

theorem psi_append (w₁ w₂ : List Letter) : psi xt (w₁ ++ w₂) = psi xt w₁ * psi xt w₂ := by
  simp [psi]

theorem psi_cons (l : Letter) (w : List Letter) : psi xt (l :: w) = lt xt l * psi xt w := by
  simp [psi]

theorem psi_posW (w : List (Fin 2)) : psi xt (posW w) = (w.map xt).prod := by
  simp [psi, posW, lt, List.map_map, Function.comp_def]

theorem psi_invW (w : List (Fin 2)) : psi xt (invW w) = ((w.map xt).prod)⁻¹ := by
  rw [List.prod_inv_reverse]
  simp [psi, invW, lt, List.map_map, Function.comp_def, List.map_reverse]

@[expose] def kap (T : CayTab) (xt : Fin 2 → E) (v : ℕ) (i : Fin 2) : E :=
  (sig T xt (T.tgt v i))⁻¹ * (sig T xt v * xt i)

open Classical in
@[expose] noncomputable def cE (T : CayTab) (xt : Fin 2 → E) (e : ℕ) : ZMod 2 :=
  if kap T xt (e / 2) (fo e) = 1 then 0 else 1

theorem phi_sig (hxt : ∀ i, X.φ (xt i) = x i) (T : CayTab) (v : ℕ) :
    X.φ (sig T xt v) = T.el x v := by
  unfold sig CayTab.el
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => hxt i

theorem phi_kap (hT : T.Good x) (hxt : ∀ i, X.φ (xt i) = x i) {v : ℕ} (hv : v < T.nV)
    (i : Fin 2) : X.φ (kap T xt v i) = 1 := by
  unfold kap
  rw [map_mul, map_inv, map_mul, phi_sig X xt hxt, phi_sig X xt hxt, hxt, hT.el_tgt v hv i]
  group

theorem kap_eq (hT : T.Good x) (hxt : ∀ i, X.φ (xt i) = x i) {v : ℕ} (hv : v < T.nV)
    (i : Fin 2) : kap T xt v i = X.toZ (cE T xt (2 * v + i)) := by
  obtain ⟨a, ha⟩ := X.exists_toZ (phi_kap X xt hT hxt hv i)
  have hdiv : (2 * v + (i : ℕ)) / 2 = v := by omega
  have hc : cE T xt (2 * v + i) = a := by
    unfold cE
    rw [hdiv, fo_edge]
    by_cases h1 : kap T xt v i = 1
    · simp only [h1, ↓reduceIte]
      rw [h1] at ha
      exact (X.toZ_inj (ha.symm.trans X.toZ_zero.symm)).symm
    · simp only [h1, ↓reduceIte]
      rcases zmod_two_cases a with rfl | rfl
      · exact absurd (ha.trans X.toZ_zero) h1
      · rfl
  rw [hc]
  exact ha

theorem step_eq (hT : T.Good x) (hxt : ∀ i, X.φ (xt i) = x i) {v : ℕ} (hv : v < T.nV)
    (l : Letter) :
    sig T xt v * lt xt l = sig T xt (T.step v l) * X.toZ (cE T xt (T.edge v l)) := by
  obtain ⟨i, b⟩ := l
  cases b
  ·
    simp only [lt, CayTab.step, CayTab.edge, Bool.false_eq_true, ite_false]
    have hu : T.back v i < T.nV := hT.back_lt v hv i
    have hk := kap_eq X xt hT hxt hu i
    unfold kap at hk
    rw [hT.tgt_back v hv i] at hk
    set z := X.toZ (cE T xt (2 * T.back v i + i)) with hz
    have h1 : sig T xt (T.back v i) * xt i = sig T xt v * z := by
      rw [← hk]
      group
    have h2 : sig T xt (T.back v i) = sig T xt v * z * (xt i)⁻¹ := by
      rw [← h1]
      group
    have hzz : z * z = 1 := by
      rw [hz, ← X.toZ_add, CharTwo.add_self_eq_zero, X.toZ_zero]
    calc sig T xt v * (xt i)⁻¹ = sig T xt v * (z * z) * (xt i)⁻¹ := by rw [hzz, mul_one]
      _ = sig T xt v * z * (z * (xt i)⁻¹) := by group
      _ = sig T xt v * z * ((xt i)⁻¹ * z) := by rw [hz, X.toZ_central]
      _ = sig T xt v * z * (xt i)⁻¹ * z := by group
      _ = sig T xt (T.back v i) * z := by rw [h2]
  ·
    simp only [lt, CayTab.step, CayTab.edge, ite_true]
    have hk := kap_eq X xt hT hxt hv i
    unfold kap at hk
    rw [← hk]
    group

theorem step_lt_of (hT : T.Good x) {v : ℕ} (hv : v < T.nV) (l : Letter) : T.step v l < T.nV :=
  hT.step_lt hv l

theorem telescope (hT : T.Good x) (hxt : ∀ i, X.φ (xt i) = x i) {v : ℕ} (hv : v < T.nV)
    (w : List Letter) :
    sig T xt v * psi xt w =
      sig T xt (T.walkEnd v w) * X.toZ ((T.walkEdges v w).map (cE T xt)).sum := by
  induction w generalizing v with
  | nil => simp [psi, walkEnd, walkEdges, X.toZ_zero]
  | cons l w ih =>
    have hs := hT.step_lt hv l
    have h1 := step_eq X xt hT hxt hv l
    have h2 := ih hs
    simp only [walkEnd, walkEdges, List.map_cons, List.sum_cons]
    calc sig T xt v * psi xt (l :: w)
        = (sig T xt v * lt xt l) * psi xt w := by rw [psi_cons, mul_assoc]
      _ = (sig T xt (T.step v l) * X.toZ (cE T xt (T.edge v l))) * psi xt w := by rw [h1]
      _ = sig T xt (T.step v l) * (psi xt w * X.toZ (cE T xt (T.edge v l))) := by
          rw [mul_assoc, X.toZ_central]
      _ = (sig T xt (T.step v l) * psi xt w) * X.toZ (cE T xt (T.edge v l)) := by rw [mul_assoc]
      _ = (sig T xt (T.walkEnd (T.step v l) w) *
            X.toZ ((T.walkEdges (T.step v l) w).map (cE T xt)).sum) *
            X.toZ (cE T xt (T.edge v l)) := by rw [h2]
      _ = sig T xt (T.walkEnd (T.step v l) w) *
            X.toZ (cE T xt (T.edge v l) + ((T.walkEdges (T.step v l) w).map (cE T xt)).sum) := by
          rw [mul_assoc, ← X.toZ_add, add_comm]

theorem closed_walk (hT : T.Good x) (hxt : ∀ i, X.φ (xt i) = x i) {v : ℕ} (hv : v < T.nV)
    {w : List Letter} (h : T.walkEnd v w = v) :
    psi xt w = X.toZ ((T.walkEdges v w).map (cE T xt)).sum := by
  have := telescope X xt hT hxt hv w
  rw [h] at this
  exact mul_left_cancel this

theorem trans_sound (hT : T.Good x) (hxt : ∀ i, X.φ (xt i) = x i) {v₀ v₁ : ℕ}
    (h₀ : v₀ < T.nV) (h₁ : v₁ < T.nV) {w : List Letter} (e₀ : T.walkEnd v₀ w = v₀)
    (e₁ : T.walkEnd v₁ w = v₁) :
    ((T.walkEdges v₀ w).map (cE T xt)).sum = ((T.walkEdges v₁ w).map (cE T xt)).sum :=
  X.toZ_inj ((closed_walk X xt hT hxt h₀ e₀).symm.trans (closed_walk X xt hT hxt h₁ e₁))

theorem tree_sound (hT : T.Good x) (hxt : ∀ i, X.φ (xt i) = x i) {v : ℕ} (hv : v < T.nV)
    (i : Fin 2) (h : T.word (T.tgt v i) = T.word v ++ [i]) : cE T xt (2 * v + i) = 0 := by
  have hk := kap_eq X xt hT hxt hv i
  have h1 : kap T xt v i = 1 := by
    unfold kap sig
    rw [h, List.map_append, List.prod_append]
    simp
  rw [h1, ← X.toZ_zero] at hk
  exact (X.toZ_inj hk).symm

@[expose] def substW (T : CayTab) (v : ℕ → ℕ) (ρ : List (ℕ × Bool)) : List Letter :=
  ρ.flatMap fun p => if p.2 then posW (T.word (v p.1)) else invW (T.word (v p.1))

theorem substW_cons (T : CayTab) (v : ℕ → ℕ) (p : ℕ × Bool) (ρ : List (ℕ × Bool)) :
    substW T v (p :: ρ) =
      (if p.2 then posW (T.word (v p.1)) else invW (T.word (v p.1))) ++ substW T v ρ := by
  simp [substW]

theorem exists_gamma (hxt : ∀ i, X.φ (xt i) = x i) {gt : E} {g : G} (hg : X.φ gt = g)
    (va vb : ℕ → ℕ) (J : ℕ) (hrel : ∀ j < J, g * T.el x (va j) * g⁻¹ = T.el x (vb j)) :
    ∃ γ : ℕ → ZMod 2, ∀ j < J,
      gt * sig T xt (va j) * gt⁻¹ = sig T xt (vb j) * X.toZ (γ j) := by
  have h : ∀ j : ℕ, ∃ a : ZMod 2, j < J →
      gt * sig T xt (va j) * gt⁻¹ = sig T xt (vb j) * X.toZ a := by
    intro j
    by_cases hj : j < J
    · have hz : X.φ ((sig T xt (vb j))⁻¹ * (gt * sig T xt (va j) * gt⁻¹)) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, map_inv, hg, phi_sig X xt hxt,
          phi_sig X xt hxt, ← hrel j hj]
        group
      obtain ⟨a, ha⟩ := X.exists_toZ hz
      exact ⟨a, fun _ => by rw [← ha]; group⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose γ hγ using h
  exact ⟨γ, fun j hj => hγ j hj⟩

theorem conj_substW {gt : E} {J : ℕ} {va vb : ℕ → ℕ} {γ : ℕ → ZMod 2}
    (hγ : ∀ j < J, gt * sig T xt (va j) * gt⁻¹ = sig T xt (vb j) * X.toZ (γ j)) :
    ∀ ρ : List (ℕ × Bool), (∀ p ∈ ρ, p.1 < J) →
      gt * psi xt (substW T va ρ) * gt⁻¹ =
        psi xt (substW T vb ρ) * X.toZ ((ρ.map fun p => γ p.1).sum) := by
  intro ρ
  induction ρ with
  | nil => intro _; simp [substW, psi, X.toZ_zero]
  | cons p ρ ih =>
    intro hρ
    have hp : p.1 < J := hρ p (List.mem_cons_self ..)
    have ih' := ih fun q hq => hρ q (List.mem_cons_of_mem _ hq)
    obtain ⟨c, b⟩ := p
    have hj : gt * sig T xt (va c) * gt⁻¹ = sig T xt (vb c) * X.toZ (γ c) := hγ c hp
    have hsum : (((c, b) :: ρ).map fun p => γ p.1).sum = γ c + (ρ.map fun p => γ p.1).sum := by
      simp
    rw [substW_cons, substW_cons, psi_append, psi_append, hsum, X.toZ_add]
    set A := psi xt (substW T va ρ)
    set B := psi xt (substW T vb ρ)
    set S := X.toZ (ρ.map fun p => γ p.1).sum
    cases b
    · simp only [Bool.false_eq_true, ite_false, psi_invW]
      have hsig : ((T.word (va c)).map xt).prod = sig T xt (va c) := rfl
      have hsig' : ((T.word (vb c)).map xt).prod = sig T xt (vb c) := rfl
      rw [hsig, hsig']
      have hc : gt * (sig T xt (va c))⁻¹ * gt⁻¹ =
          X.toZ (γ c) * (sig T xt (vb c))⁻¹ := by
        have : gt * (sig T xt (va c))⁻¹ * gt⁻¹ = (gt * sig T xt (va c) * gt⁻¹)⁻¹ := by group
        rw [this, hj, mul_inv_rev, X.toZ_inv]
      calc gt * ((sig T xt (va c))⁻¹ * A) * gt⁻¹
          = (gt * (sig T xt (va c))⁻¹ * gt⁻¹) * (gt * A * gt⁻¹) := by group
        _ = (X.toZ (γ c) * (sig T xt (vb c))⁻¹) * (B * S) := by rw [hc, ih']
        _ = (sig T xt (vb c))⁻¹ * (X.toZ (γ c) * B) * S := by
            rw [X.toZ_central (γ c) (sig T xt (vb c))⁻¹]
            simp only [mul_assoc]
        _ = (sig T xt (vb c))⁻¹ * (B * X.toZ (γ c)) * S := by rw [X.toZ_central]
        _ = ((sig T xt (vb c))⁻¹ * B) * (X.toZ (γ c) * S) := by simp only [mul_assoc]
    · simp only [ite_true, psi_posW]
      have hsig : ((T.word (va c)).map xt).prod = sig T xt (va c) := rfl
      have hsig' : ((T.word (vb c)).map xt).prod = sig T xt (vb c) := rfl
      rw [hsig, hsig']
      calc gt * (sig T xt (va c) * A) * gt⁻¹
          = (gt * sig T xt (va c) * gt⁻¹) * (gt * A * gt⁻¹) := by group
        _ = (sig T xt (vb c) * X.toZ (γ c)) * (B * S) := by rw [hj, ih']
        _ = sig T xt (vb c) * (X.toZ (γ c) * B) * S := by simp only [mul_assoc]
        _ = sig T xt (vb c) * (B * X.toZ (γ c)) * S := by rw [X.toZ_central]
        _ = (sig T xt (vb c) * B) * (X.toZ (γ c) * S) := by simp only [mul_assoc]

theorem fus_sound (hT : T.Good x) (hxt : ∀ i, X.φ (xt i) = x i) {gt : E} {J : ℕ}
    {va vb : ℕ → ℕ} {γ : ℕ → ZMod 2}
    (hγ : ∀ j < J, gt * sig T xt (va j) * gt⁻¹ = sig T xt (vb j) * X.toZ (γ j))
    {ρ : List (ℕ × Bool)} (hρ : ∀ p ∈ ρ, p.1 < J)
    (hA : T.walkEnd 0 (substW T va ρ) = 0) (hB : T.walkEnd 0 (substW T vb ρ) = 0) :
    ((T.walkEdges 0 (substW T va ρ)).map (cE T xt)).sum =
      ((T.walkEdges 0 (substW T vb ρ)).map (cE T xt)).sum + (ρ.map fun p => γ p.1).sum := by
  have h0 : 0 < T.nV := hT.zero_lt
  have hcj := conj_substW X xt hγ ρ hρ
  rw [closed_walk X xt hT hxt h0 hA, closed_walk X xt hT hxt h0 hB] at hcj
  have e1 : gt * X.toZ ((T.walkEdges 0 (substW T va ρ)).map (cE T xt)).sum * gt⁻¹ =
      X.toZ ((T.walkEdges 0 (substW T va ρ)).map (cE T xt)).sum := by
    rw [← X.toZ_central, mul_assoc, mul_inv_cancel, mul_one]
  rw [e1, ← X.toZ_add] at hcj
  exact X.toZ_inj hcj

end Cochain


section Sect

open CayTab

variable {G : Type*} [Group G] [Finite G] {T : CayTab} {x : Fin 2 → G}

@[expose] def subSet (T : CayTab) (x : Fin 2 → G) : Set G := {g | ∃ v < T.nV, T.el x v = g}

omit [Finite G] in
theorem subSet_one (hT : T.Good x) : (1 : G) ∈ subSet T x :=
  ⟨0, hT.zero_lt, by simp [CayTab.el, hT.word_zero]⟩

omit [Finite G] in
theorem subSet_mul (hT : T.Good x) {g h : G} (hg : g ∈ subSet T x) (hh : h ∈ subSet T x) :
    g * h ∈ subSet T x := by
  obtain ⟨u, hu, rfl⟩ := hg
  obtain ⟨v, hv, rfl⟩ := hh
  exact ⟨T.walkEnd u (posW (T.word v)), hT.walkEnd_lt hu _, by rw [hT.el_walk hu]; rfl⟩

omit [Finite G] in
theorem subSet_pow (hT : T.Good x) {g : G} (hg : g ∈ subSet T x) :
    ∀ n : ℕ, g ^ n ∈ subSet T x := by
  intro n
  induction n with
  | zero => simpa using subSet_one hT
  | succ n ih => rw [pow_succ]; exact subSet_mul hT ih hg

theorem subSet_inv (hT : T.Good x) {g : G} (hg : g ∈ subSet T x) : g⁻¹ ∈ subSet T x := by
  obtain ⟨n, hn⟩ : ∃ n, orderOf g = n + 1 := ⟨orderOf g - 1, by have := orderOf_pos g; omega⟩
  have h1 : g * g ^ n = 1 := by rw [← pow_succ', ← hn, pow_orderOf_eq_one]
  rw [inv_eq_of_mul_eq_one_right h1]
  exact subSet_pow hT hg n

@[expose] def CayTab.sub (T : CayTab) (x : Fin 2 → G) (hT : T.Good x) : Subgroup G where
  carrier := subSet T x
  one_mem' := subSet_one hT
  mul_mem' := fun hg hh => subSet_mul hT hg hh
  inv_mem' := fun hg => subSet_inv hT hg

theorem CayTab.mem_sub {hT : T.Good x} {g : G} : g ∈ T.sub x hT ↔ ∃ v < T.nV, T.el x v = g :=
  Iff.rfl

theorem CayTab.card_sub (hT : T.Good x) : Nat.card (T.sub x hT) = T.nV := by
  have hinj : Set.InjOn (T.el x) (Finset.range T.nV : Set ℕ) := fun u hu v hv h =>
    hT.el_inj u (Finset.mem_range.1 hu) v (Finset.mem_range.1 hv) h
  have himg : ((T.sub x hT : Subgroup G) : Set G) = (T.el x) '' (Finset.range T.nV : Set ℕ) := by
    ext g
    simp only [SetLike.mem_coe, CayTab.mem_sub, Set.mem_image, Finset.coe_range, Set.mem_Iio]
  change Nat.card ((T.sub x hT : Subgroup G) : Set G) = _
  rw [Nat.card_coe_set_eq, himg, (Set.ncard_image_iff (Finset.finite_toSet _)).2 hinj,
    Set.ncard_coe_finset, Finset.card_range]

variable {E : Type*} [Group E] (X : CentralExt E G) (xt : Fin 2 → E)

theorem exists_section (hT : T.Good x) (hxt : ∀ i, X.φ (xt i) = x i)
    (hzero : ∀ e < 2 * T.nV, cE T xt e = 0) :
    ∃ s : T.sub x hT →* E, ∀ g : T.sub x hT, X.φ (s g) = (g : G) := by
  classical
  have htel : ∀ u < T.nV, ∀ w : List Letter,
      sig T xt u * psi xt w = sig T xt (T.walkEnd u w) := by
    intro u hu w
    rw [telescope X xt hT hxt hu w]
    have : ((T.walkEdges u w).map (cE T xt)).sum = 0 := by
      apply List.sum_eq_zero
      intro a ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      exact hzero e (hT.walkEdges_lt hu w e he)
    rw [this, X.toZ_zero, mul_one]
  let idx : T.sub x hT → ℕ := fun g => Classical.choose g.2
  have idx_spec : ∀ g : T.sub x hT, idx g < T.nV ∧ T.el x (idx g) = g :=
    fun g => Classical.choose_spec g.2
  have idx_el : ∀ v < T.nV, ∀ g : T.sub x hT, T.el x v = g → idx g = v := fun v hv g h =>
    hT.el_inj _ (idx_spec g).1 _ hv ((idx_spec g).2.trans h.symm)
  refine ⟨MonoidHom.mk' (fun g => sig T xt (idx g)) fun g h => ?_, fun g => ?_⟩
  · have hu := (idx_spec g).1
    have hv := (idx_spec h).1
    have hel : T.el x (T.walkEnd (idx g) (posW (T.word (idx h)))) = ((g * h : T.sub x hT) : G) := by
      rw [hT.el_walk hu]
      show T.el x (idx g) * T.el x (idx h) = _
      rw [(idx_spec g).2, (idx_spec h).2]
      rfl
    have hidx : idx (g * h) = T.walkEnd (idx g) (posW (T.word (idx h))) :=
      idx_el _ (hT.walkEnd_lt hu _) _ hel
    show sig T xt (idx (g * h)) = sig T xt (idx g) * sig T xt (idx h)
    rw [hidx, ← htel _ hu, psi_posW]
    rfl
  · show X.φ (sig T xt (idx g)) = (g : G)
    rw [phi_sig X xt hxt, (idx_spec g).2]

end Sect

end CFSG.QuasithinUnique.Ch1.TitsCover
