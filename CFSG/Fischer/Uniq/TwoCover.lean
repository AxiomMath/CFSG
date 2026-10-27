module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Fischer

variable {V : Type*} (G : SimpleGraph V) (H : V → V → V → Prop)

structure TwoCover where
  C : Type*
  π : C → V
  adj : SimpleGraph C
  proj : ∀ {c c'}, adj.Adj c c' → G.Adj (π c) (π c')
  lift : ∀ c w, G.Adj (π c) w → ∃! c', adj.Adj c c' ∧ π c' = w
  two : ∀ v, ∃ c c', c ≠ c' ∧ π c = v ∧ π c' = v ∧ ∀ x, π x = v → x = c ∨ x = c'
  tri : ∀ c c₁ c₂, adj.Adj c c₁ → adj.Adj c c₂ → G.Adj (π c₁) (π c₂) →
    (adj.Adj c₁ c₂ ↔ H (π c) (π c₁) (π c₂))

namespace TwoCover

variable {G H} (P : TwoCover G H)

theorem exists_other (c : P.C) : ∃ c', c' ≠ c ∧ P.π c' = P.π c ∧
    ∀ x, P.π x = P.π c → x = c ∨ x = c' := by
  obtain ⟨a, b, hab, ha, hb, hx⟩ := P.two (P.π c)
  rcases hx c rfl with rfl | rfl
  · exact ⟨b, hab.symm, hb, fun x h => hx x h⟩
  · exact ⟨a, hab, ha, fun x h => (hx x h).symm⟩

noncomputable def other (c : P.C) : P.C := Classical.choose (P.exists_other c)

theorem other_ne (c : P.C) : P.other c ≠ c := (Classical.choose_spec (P.exists_other c)).1

theorem π_other (c : P.C) : P.π (P.other c) = P.π c :=
  (Classical.choose_spec (P.exists_other c)).2.1

theorem eq_or_eq_other {c x : P.C} (h : P.π x = P.π c) : x = c ∨ x = P.other c :=
  (Classical.choose_spec (P.exists_other c)).2.2 x h

theorem other_other (c : P.C) : P.other (P.other c) = c := by
  rcases P.eq_or_eq_other (c := P.other c) (x := c) (P.π_other c).symm with h | h
  · exact absurd h.symm (P.other_ne c)
  · exact h.symm

theorem adj_iff_not_adj_other {c d : P.C} (h : G.Adj (P.π c) (P.π d)) :
    P.adj.Adj c d ↔ ¬ P.adj.Adj c (P.other d) := by
  obtain ⟨c', ⟨hc', hπ⟩, huniq⟩ := P.lift c (P.π d) h
  have hd := P.eq_or_eq_other hπ
  constructor
  · intro hcd hco
    have h1 := huniq d ⟨hcd, rfl⟩
    have h2 := huniq (P.other d) ⟨hco, P.π_other d⟩
    exact P.other_ne d (h2.trans h1.symm)
  · intro hco
    rcases hd with h1 | h1
    · rw [← h1]; exact hc'
    · exact absurd (h1 ▸ hc') hco

theorem adj_other_other {c d : P.C} (h : G.Adj (P.π c) (P.π d)) :
    P.adj.Adj (P.other c) (P.other d) ↔ P.adj.Adj c d := by
  have h' : G.Adj (P.π (P.other c)) (P.π d) := by rw [P.π_other]; exact h
  have e1 := P.adj_iff_not_adj_other h'
  have e2 := P.adj_iff_not_adj_other h'.symm
  rw [P.other_other, P.adj.adj_comm d, P.adj.adj_comm d c] at e2
  tauto

noncomputable def liftAt (c : P.C) (w : V) (h : G.Adj (P.π c) w) : P.C :=
  Classical.choose (P.lift c w h).exists

theorem adj_liftAt (c : P.C) (w : V) (h : G.Adj (P.π c) w) : P.adj.Adj c (P.liftAt c w h) :=
  (Classical.choose_spec (P.lift c w h).exists).1

theorem π_liftAt (c : P.C) (w : V) (h : G.Adj (P.π c) w) : P.π (P.liftAt c w h) = w :=
  (Classical.choose_spec (P.lift c w h).exists).2

theorem eq_liftAt {c c' : P.C} (h : P.adj.Adj c c') :
    c' = P.liftAt c (P.π c') (P.proj h) :=
  (P.lift c (P.π c') (P.proj h)).unique ⟨h, rfl⟩ ⟨P.adj_liftAt _ _ _, P.π_liftAt _ _ _⟩

theorem adj_iff_tri {a c d : P.C} (hc : G.Adj (P.π a) (P.π c)) (hd : G.Adj (P.π a) (P.π d))
    (hcd : G.Adj (P.π c) (P.π d)) :
    P.adj.Adj c d ↔ (H (P.π a) (P.π c) (P.π d) ↔ (P.adj.Adj a c ↔ P.adj.Adj a d)) := by
  set ac := P.liftAt a (P.π c) hc
  set ad := P.liftAt a (P.π d) hd
  have hac : P.adj.Adj a ac := P.adj_liftAt _ _ _
  have had : P.adj.Adj a ad := P.adj_liftAt _ _ _
  have hπc : P.π ac = P.π c := P.π_liftAt _ _ _
  have hπd : P.π ad = P.π d := P.π_liftAt _ _ _
  have htri := P.tri a ac ad hac had (by rw [hπc, hπd]; exact hcd)
  rw [hπc, hπd] at htri
  have hac' : G.Adj (P.π a) (P.π ac) := by rw [hπc]; exact hc
  have had' : G.Adj (P.π a) (P.π ad) := by rw [hπd]; exact hd
  have hacad : G.Adj (P.π ac) (P.π ad) := by rw [hπc, hπd]; exact hcd
  have key : ∀ x y : P.C, (x = ac ∨ x = P.other ac) → (y = ad ∨ y = P.other ad) →
      (P.adj.Adj x y ↔ (H (P.π a) (P.π c) (P.π d) ↔ (P.adj.Adj a x ↔ P.adj.Adj a y))) := by
    intro x y hx hy
    have h1 := (P.adj_iff_not_adj_other hac').1 hac
    have h2 := (P.adj_iff_not_adj_other had').1 had
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simp only [hac, had, iff_true]; exact htri
    · have h3 := P.adj_iff_not_adj_other hacad
      simp only [hac, h2, iff_false]
      rw [htri] at h3
      tauto
    · have h3 := P.adj_iff_not_adj_other hacad.symm
      simp only [had, h1, iff_true, iff_false]
      rw [P.adj.adj_comm ad ac, htri] at h3
      rw [P.adj.adj_comm]
      tauto
    · simp only [h1, h2]
      rw [P.adj_other_other hacad, htri]
      tauto
  exact key c d (P.eq_or_eq_other hπc.symm) (P.eq_or_eq_other hπd.symm)

end TwoCover

section Rigid

variable {G H} (r : V) (hD2 : ∀ v, v ≠ r → ¬ G.Adj r v → ∃ x, G.Adj r x ∧ G.Adj x v)
include hD2

noncomputable def par (v : V) : V := by
  classical
  exact if h : v ≠ r ∧ ¬ G.Adj r v then Classical.choose (hD2 v h.1 h.2) else r

theorem par_spec {v : V} (h1 : v ≠ r) (h2 : ¬ G.Adj r v) :
    G.Adj r (par r hD2 v) ∧ G.Adj (par r hD2 v) v := by
  unfold par
  simp only [ne_eq, h1, not_false_eq_true, h2, and_self, dite_true]
  exact Classical.choose_spec (hD2 v h1 h2)

namespace TwoCover

variable (P : TwoCover G H)

omit hD2 in
theorem exists_root : ∃ c : P.C, P.π c = r := by
  obtain ⟨c, -, -, hc, -⟩ := P.two r
  exact ⟨c, hc⟩

noncomputable def root : P.C := Classical.choose (P.exists_root r)

omit hD2 in
theorem π_root : P.π (P.root r) = r := Classical.choose_spec (P.exists_root r)

noncomputable def sec (v : V) : P.C := by
  classical
  exact if h0 : v = r then P.root r
    else if h1 : G.Adj r v then P.liftAt (P.root r) v (by rw [P.π_root]; exact h1)
    else P.liftAt (P.liftAt (P.root r) (par r hD2 v)
        (by rw [P.π_root]; exact (par_spec r hD2 h0 h1).1))
      v (by rw [P.π_liftAt]; exact (par_spec r hD2 h0 h1).2)

theorem sec_root : P.sec r hD2 r = P.root r := by
  unfold sec; simp

theorem sec_near {v : V} (hv : G.Adj r v) :
    P.sec r hD2 v = P.liftAt (P.root r) v (by rw [P.π_root]; exact hv) := by
  unfold sec
  simp only [(G.ne_of_adj hv).symm, dite_false, hv, dite_true]

theorem sec_far {v : V} (h0 : v ≠ r) (h1 : ¬ G.Adj r v) :
    P.sec r hD2 v = P.liftAt (P.sec r hD2 (par r hD2 v)) v
      (by
        rw [P.sec_near r hD2 (par_spec r hD2 h0 h1).1, P.π_liftAt]
        exact (par_spec r hD2 h0 h1).2) := by
  conv_lhs => unfold sec
  simp only [h0, dite_false, h1]
  congr 1
  rw [P.sec_near r hD2 (par_spec r hD2 h0 h1).1]

theorem π_sec (v : V) : P.π (P.sec r hD2 v) = v := by
  by_cases h0 : v = r
  · rw [h0, sec_root, π_root]
  · by_cases h1 : G.Adj r v
    · rw [P.sec_near r hD2 h1, P.π_liftAt]
    · rw [P.sec_far r hD2 h0 h1, P.π_liftAt]

theorem adj_sec_root {v : V} (hv : G.Adj r v) : P.adj.Adj (P.sec r hD2 r) (P.sec r hD2 v) := by
  rw [sec_root, P.sec_near r hD2 hv]
  exact P.adj_liftAt _ _ _

theorem adj_sec_par {v : V} (h0 : v ≠ r) (h1 : ¬ G.Adj r v) :
    P.adj.Adj (P.sec r hD2 (par r hD2 v)) (P.sec r hD2 v) := by
  conv_rhs => rw [P.sec_far r hD2 h0 h1]
  exact P.adj_liftAt _ _ _

def bit (u w : V) : Prop := P.adj.Adj (P.sec r hD2 u) (P.sec r hD2 w)

theorem bit_comm (u w : V) : P.bit r hD2 u w ↔ P.bit r hD2 w u := P.adj.adj_comm _ _

theorem bit_tri {x u w : V} (hu : G.Adj x u) (hw : G.Adj x w) (huw : G.Adj u w) :
    P.bit r hD2 u w ↔ (H x u w ↔ (P.bit r hD2 x u ↔ P.bit r hD2 x w)) := by
  have h := P.adj_iff_tri (a := P.sec r hD2 x) (c := P.sec r hD2 u) (d := P.sec r hD2 w)
    (by rw [π_sec, π_sec]; exact hu) (by rw [π_sec, π_sec]; exact hw)
    (by rw [π_sec, π_sec]; exact huw)
  rw [π_sec, π_sec, π_sec] at h
  exact h

theorem bit_root {v : V} (hv : G.Adj r v) : P.bit r hD2 r v := P.adj_sec_root r hD2 hv

theorem bit_par {v : V} (h0 : v ≠ r) (h1 : ¬ G.Adj r v) : P.bit r hD2 (par r hD2 v) v :=
  P.adj_sec_par r hD2 h0 h1

end TwoCover

omit hD2 in
theorem connected_induction {W : Type*} {Γ : SimpleGraph W} (hΓ : Γ.Connected) {p : W → Prop}
    {w₀ : W} (h₀ : p w₀) (hstep : ∀ a b, Γ.Adj a b → p a → p b) (w : W) : p w := by
  obtain ⟨q⟩ := hΓ.preconnected w₀ w
  induction q with
  | nil => exact h₀
  | cons hab _ ih => exact ih (hstep _ _ hab h₀)

variable (hMU : ∀ v, v ≠ r → ¬ G.Adj r v → (G.induce {x | G.Adj r x ∧ G.Adj x v}).Connected)
  (hED : ∀ v w, v ≠ r → ¬ G.Adj r v → w ≠ r → ¬ G.Adj r w → G.Adj v w →
    ∃ x, G.Adj r x ∧ G.Adj x v ∧ G.Adj x w)

include hMU hED in
theorem bit_agree (P Q : TwoCover G H) {u w : V} (huw : G.Adj u w) :
    P.bit r hD2 u w ↔ Q.bit r hD2 u w := by
  have near_near : ∀ u w, G.Adj r u → G.Adj r w → G.Adj u w →
      (P.bit r hD2 u w ↔ Q.bit r hD2 u w) := by
    intro u w hu hw huw
    rw [P.bit_tri r hD2 hu hw huw, Q.bit_tri r hD2 hu hw huw]
    simp only [P.bit_root r hD2 hu, P.bit_root r hD2 hw, Q.bit_root r hD2 hu,
      Q.bit_root r hD2 hw]
  have near_far : ∀ w, w ≠ r → ¬ G.Adj r w → ∀ u, G.Adj r u → G.Adj u w →
      (P.bit r hD2 u w ↔ Q.bit r hD2 u w) := by
    intro w h0 h1 u hu huw
    have hc := hMU w h0 h1
    let w₀ : {x | G.Adj r x ∧ G.Adj x w} := ⟨par r hD2 w, par_spec r hD2 h0 h1⟩
    refine connected_induction hc (p := fun x => P.bit r hD2 x w ↔ Q.bit r hD2 x w) (w₀ := w₀)
      ?_ ?_ ⟨u, hu, huw⟩
    · exact iff_of_true (P.bit_par r hD2 h0 h1) (Q.bit_par r hD2 h0 h1)
    · rintro ⟨x, hxr, hxw⟩ ⟨y, hyr, hyw⟩ hxy hx
      simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype] at hxy
      rw [P.bit_tri r hD2 hxy hxw hyw, Q.bit_tri r hD2 hxy hxw hyw,
        near_near x y hxr hyr hxy, hx]
  by_cases hu0 : u = r
  · rw [hu0] at huw ⊢
    exact iff_of_true (P.bit_root r hD2 huw) (Q.bit_root r hD2 huw)
  by_cases hw0 : w = r
  · rw [hw0] at huw ⊢
    rw [P.bit_comm, Q.bit_comm]
    exact iff_of_true (P.bit_root r hD2 huw.symm) (Q.bit_root r hD2 huw.symm)
  by_cases hu1 : G.Adj r u <;> by_cases hw1 : G.Adj r w
  · exact near_near u w hu1 hw1 huw
  · exact near_far w hw0 hw1 u hu1 huw
  · rw [P.bit_comm, Q.bit_comm]
    exact near_far u hu0 hu1 w hw1 huw.symm
  · obtain ⟨x, hxr, hxu, hxw⟩ := hED u w hu0 hu1 hw0 hw1 huw
    rw [P.bit_tri r hD2 hxu hxw huw, Q.bit_tri r hD2 hxu hxw huw, near_far u hu0 hu1 x hxr hxu,
      near_far w hw0 hw1 x hxr hxw]

noncomputable def matchMap (P Q : TwoCover G H) (c : P.C) : Q.C := by
  classical
  exact if c = P.sec r hD2 (P.π c) then Q.sec r hD2 (P.π c) else Q.other (Q.sec r hD2 (P.π c))

theorem matchMap_sec (P Q : TwoCover G H) (v : V) :
    matchMap r hD2 P Q (P.sec r hD2 v) = Q.sec r hD2 v := by
  unfold matchMap
  simp [TwoCover.π_sec]

theorem matchMap_other (P Q : TwoCover G H) (v : V) :
    matchMap r hD2 P Q (P.other (P.sec r hD2 v)) = Q.other (Q.sec r hD2 v) := by
  unfold matchMap
  rw [P.π_other, TwoCover.π_sec, ite_eq_right (P.other_ne _)]

theorem eq_sec_or (P : TwoCover G H) (c : P.C) :
    ∃ v, c = P.sec r hD2 v ∨ c = P.other (P.sec r hD2 v) :=
  ⟨P.π c, P.eq_or_eq_other (P.π_sec r hD2 (P.π c)).symm⟩

theorem matchMap_matchMap (P Q : TwoCover G H) (c : P.C) :
    matchMap r hD2 Q P (matchMap r hD2 P Q c) = c := by
  obtain ⟨v, rfl | rfl⟩ := eq_sec_or r hD2 P c
  · rw [matchMap_sec, matchMap_sec]
  · rw [matchMap_other, matchMap_other]

theorem π_matchMap (P Q : TwoCover G H) (c : P.C) : Q.π (matchMap r hD2 P Q c) = P.π c := by
  obtain ⟨v, rfl | rfl⟩ := eq_sec_or r hD2 P c
  · rw [matchMap_sec, TwoCover.π_sec, TwoCover.π_sec]
  · rw [matchMap_other, Q.π_other, P.π_other, TwoCover.π_sec, TwoCover.π_sec]

theorem adj_cases (P : TwoCover G H) {v w : V} (hvw : G.Adj v w) :
    (P.adj.Adj (P.sec r hD2 v) (P.sec r hD2 w) ↔ P.bit r hD2 v w) ∧
    (P.adj.Adj (P.sec r hD2 v) (P.other (P.sec r hD2 w)) ↔ ¬ P.bit r hD2 v w) ∧
    (P.adj.Adj (P.other (P.sec r hD2 v)) (P.sec r hD2 w) ↔ ¬ P.bit r hD2 v w) ∧
    (P.adj.Adj (P.other (P.sec r hD2 v)) (P.other (P.sec r hD2 w)) ↔ P.bit r hD2 v w) := by
  have h : G.Adj (P.π (P.sec r hD2 v)) (P.π (P.sec r hD2 w)) := by
    rw [TwoCover.π_sec, TwoCover.π_sec]; exact hvw
  have h' : G.Adj (P.π (P.sec r hD2 w)) (P.π (P.sec r hD2 v)) := h.symm
  have e1 := P.adj_iff_not_adj_other h
  have e2 := P.adj_iff_not_adj_other h'
  have e3 := P.adj.adj_comm (P.sec r hD2 v) (P.sec r hD2 w)
  have e4 := P.adj.adj_comm (P.other (P.sec r hD2 v)) (P.sec r hD2 w)
  unfold TwoCover.bit
  refine ⟨Iff.rfl, by tauto, by tauto, P.adj_other_other h⟩

include hMU hED in
theorem TwoCover.exists_iso (P Q : TwoCover G H) :
    ∃ β : P.C ≃ Q.C, (∀ c, Q.π (β c) = P.π c) ∧
      ∀ c c', P.adj.Adj c c' ↔ Q.adj.Adj (β c) (β c') := by
  refine ⟨⟨matchMap r hD2 P Q, matchMap r hD2 Q P, matchMap_matchMap r hD2 P Q,
    matchMap_matchMap r hD2 Q P⟩, π_matchMap r hD2 P Q, fun c c' => ?_⟩
  show P.adj.Adj c c' ↔ Q.adj.Adj (matchMap r hD2 P Q c) (matchMap r hD2 P Q c')
  by_cases hadj : G.Adj (P.π c) (P.π c')
  · obtain ⟨v, hc⟩ := eq_sec_or r hD2 P c
    obtain ⟨w, hc'⟩ := eq_sec_or r hD2 P c'
    have hvw : G.Adj v w := by
      have e1 : P.π c = v := by rcases hc with rfl | rfl <;> simp [P.π_other, TwoCover.π_sec]
      have e2 : P.π c' = w := by rcases hc' with rfl | rfl <;> simp [P.π_other, TwoCover.π_sec]
      rw [← e1, ← e2]; exact hadj
    have hb := bit_agree r hD2 hMU hED P Q hvw
    obtain ⟨p1, p2, p3, p4⟩ := adj_cases r hD2 P hvw
    obtain ⟨q1, q2, q3, q4⟩ := adj_cases r hD2 Q hvw
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
    · rw [matchMap_sec, matchMap_sec, p1, q1, hb]
    · rw [matchMap_sec, matchMap_other, p2, q2, hb]
    · rw [matchMap_other, matchMap_sec, p3, q3, hb]
    · rw [matchMap_other, matchMap_other, p4, q4, hb]
  · constructor
    · intro h; exact absurd (P.proj h) hadj
    · intro h
      have := Q.proj h
      rw [π_matchMap, π_matchMap] at this
      exact absurd this hadj

end Rigid

end CFSG.Fischer
