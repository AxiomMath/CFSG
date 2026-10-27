module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthModel

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

section Planes

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

abbrev OFrame (Q : QuadraticForm K V) : Type _ :=
  CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame Q

@[expose] def mkFrame (P P' : HypPair Q) (h : P.Orth P') : OFrame Q := ⟨P, P', h⟩

@[expose] def hypPlane (P : HypPair Q) : Submodule K V := Submodule.span K {P.e, P.f}

@[expose] def swapPair (P : HypPair Q) : HypPair Q :=
  ⟨P.f, P.e, P.Q_f, P.Q_e, HypPair.polar_fe P⟩

theorem hypPlane_swapPair (P : HypPair Q) : hypPlane (swapPair P) = hypPlane P := by
  simp only [hypPlane, swapPair]
  rw [Set.pair_comm]

theorem e_mem_hypPlane (P : HypPair Q) : P.e ∈ hypPlane P := Submodule.subset_span (by simp)

theorem f_mem_hypPlane (P : HypPair Q) : P.f ∈ hypPlane P := Submodule.subset_span (by simp)

theorem mem_hypPlane_iff (P : HypPair Q) {x : V} :
    x ∈ hypPlane P ↔ ∃ a b : K, x = a • P.e + b • P.f := by
  unfold hypPlane
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, h.symm⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, h.symm⟩

theorem polar_hypPlane_of_orth {P P' : HypPair Q} (h : P.Orth P') :
    ∀ x ∈ hypPlane P, ∀ y ∈ hypPlane P', polar Q x y = 0 := by
  intro x hx y hy
  obtain ⟨a, b, rfl⟩ := (mem_hypPlane_iff P).mp hx
  obtain ⟨c, d, rfl⟩ := (mem_hypPlane_iff P').mp hy
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, h.ee, h.ef,
    h.fe, h.ff]
  ring

theorem orth_of_polar_hypPlane {P P' : HypPair Q}
    (h : ∀ x ∈ hypPlane P, ∀ y ∈ hypPlane P', polar Q x y = 0) : P.Orth P' :=
  ⟨h _ (e_mem_hypPlane P) _ (e_mem_hypPlane P'), h _ (e_mem_hypPlane P) _ (f_mem_hypPlane P'),
    h _ (f_mem_hypPlane P) _ (e_mem_hypPlane P'), h _ (f_mem_hypPlane P) _ (f_mem_hypPlane P')⟩

theorem frame_span_eq (F : OFrame Q) : F.span = hypPlane F.P ⊔ hypPlane F.P' := by
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    rw [Frame.incl_apply]
    refine Submodule.mem_sup.mpr ⟨X 0 0 • F.e₁ + X 1 1 • F.f₁, ?_, (-X 0 1) • F.e₂ + X 1 0 • F.f₂,
      ?_, by abel⟩
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (e_mem_hypPlane F.P))
        (Submodule.smul_mem _ _ (f_mem_hypPlane F.P))
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (e_mem_hypPlane F.P'))
        (Submodule.smul_mem _ _ (f_mem_hypPlane F.P'))
  · refine sup_le ?_ ?_
    · rw [hypPlane, Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact F.e₁_mem_span
      · exact F.f₁_mem_span
    · rw [hypPlane, Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact F.e₂_mem_span
      · exact F.f₂_mem_span

theorem polarNondegOn_hypPlane (P : HypPair Q) : PolarNondegOn Q (hypPlane P) := by
  intro x hx h
  obtain ⟨a, b, rfl⟩ := (mem_hypPlane_iff P).mp hx
  have h1 := h _ (e_mem_hypPlane P)
  have h2 := h _ (f_mem_hypPlane P)
  simp only [polar_add_left, polar_smul_left_eq, P.polar_ee, P.polar_fe, P.polar_ef,
    HypPair.polar_ff] at h1 h2
  simp only [mul_zero, zero_add, mul_one, add_zero] at h1 h2
  simp [h1, h2]

end Planes

section Orient

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem orth_swapPair {P P' : HypPair Q} (h : P.Orth P') : P.Orth (swapPair P') :=
  ⟨h.ef, h.ee, h.ff, h.fe⟩

theorem mkFrame_swap {P P' : HypPair Q} (h : P.Orth P') :
    (mkFrame P P' h).swap = mkFrame P (swapPair P') (orth_swapPair h) := rfl

theorem La_range_orient (h2 : (2 : K) ≠ 0) {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}
    (hL : IsFundamental Q L i) {P P' : HypPair Q} (h : P.Orth P')
    (hspan : hypPlane P ⊔ hypPlane P' = negSpace i) :
    L = (mkFrame P P' h).La.range ∨
      L = (mkFrame P (swapPair P') (orth_swapPair h)).La.range := by
  obtain ⟨F₀, rfl, rfl⟩ := hL
  set F : OFrame Q := mkFrame P P' h with hF
  have hs : F.span = F₀.span := by
    rw [frame_span_eq, ← negSpace_La_neg_one h2 F₀]
    exact hspan
  have hi : F.La (-1) = F₀.La (-1) := Frame.La_neg_one_eq_of_span_eq hs
  have hiS : F.swap.La (-1) = F₀.La (-1) := by rw [Frame.La_swap_neg_one, hi]
  have hne : F.La.range ≠ F.swap.La.range := Frame.La_range_ne_swap_La_range F
  rw [← mkFrame_swap h]
  rcases Frame.La_range_eq_or_eq_swap h2 hi with h1 | h1
  · exact Or.inl h1.symm
  · rcases Frame.La_range_eq_or_eq_swap h2 hiS with h3 | h3
    · exact Or.inr h3.symm
    · exact absurd (h1.trans h3.symm) hne


@[expose] def twistPair (ε : Bool) (P : HypPair Q) : HypPair Q := if ε then swapPair P else P

theorem orth_twistPair (ε : Bool) {P P' : HypPair Q} (h : P.Orth P') : P.Orth (twistPair ε P') := by
  cases ε
  · exact h
  · exact orth_swapPair h

@[expose] def oFrame (ε : Bool) (P P' : HypPair Q) (h : P.Orth P') : OFrame Q :=
  mkFrame P (twistPair ε P') (orth_twistPair ε h)

theorem La_range_orientE (ε : Bool) (h2 : (2 : K) ≠ 0) {L : Subgroup (V ≃ₗ[K] V)}
    {i : V ≃ₗ[K] V} (hL : IsFundamental Q L i) {P P' : HypPair Q} (h : P.Orth P')
    (hspan : hypPlane P ⊔ hypPlane P' = negSpace i) :
    L = (oFrame ε P P' h).La.range ∨
      L = (oFrame ε P (swapPair P') (orth_swapPair h)).La.range := by
  rcases La_range_orient h2 hL h hspan with h1 | h1
  · cases ε
    · exact Or.inl h1
    · exact Or.inr h1
  · cases ε
    · exact Or.inr h1
    · exact Or.inl h1

end Orient

section Chain

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

structure VChain (Q : QuadraticForm K V) (r : ℕ) (L : ℕ → Subgroup (V ≃ₗ[K] V))
    (i : ℕ → V ≃ₗ[K] V) : Prop where
  fund : ∀ a < r, IsFundamental Q (L a) (i a)
  comm : ∀ a, a + 1 < r → i a * i (a + 1) = i (a + 1) * i a
  norm : ∀ a, a + 1 < r → i (a + 1) ∈ Subgroup.normalizer (L a : Set (V ≃ₗ[K] V))
  ncent : ∀ a, a + 1 < r → i (a + 1) ∉ Subgroup.centralizer (L a : Set (V ≃ₗ[K] V))
  hyp : ∀ a, a + 1 < r → HasSingularVector Q (negSpace (i a) ⊓ negSpace (i (a + 1)))
  orth : ∀ a b, a + 1 < b → b < r → ∀ x ∈ negSpace (i a), ∀ y ∈ negSpace (i b), polar Q x y = 0

@[expose] def chainPlane (r : ℕ) (i : ℕ → V ≃ₗ[K] V) (a : ℕ) : Submodule K V :=
  if a = 0 then negSpace (i 0) ⊓ posSpace (i 1)
  else if a = r then negSpace (i (r - 1)) ⊓ posSpace (i (r - 2))
  else negSpace (i (a - 1)) ⊓ negSpace (i a)

omit [Finite K] [FiniteDimensional K V] in
theorem chainPlane_zero (r : ℕ) (i : ℕ → V ≃ₗ[K] V) :
    chainPlane r i 0 = negSpace (i 0) ⊓ posSpace (i 1) := by
  simp [chainPlane]

omit [Finite K] [FiniteDimensional K V] in
theorem chainPlane_last {r : ℕ} (hr : 1 ≤ r) (i : ℕ → V ≃ₗ[K] V) :
    chainPlane r i r = negSpace (i (r - 1)) ⊓ posSpace (i (r - 2)) := by
  simp [chainPlane, Nat.pos_iff_ne_zero.mp hr]

omit [Finite K] [FiniteDimensional K V] in
theorem chainPlane_mid {r a : ℕ} (i : ℕ → V ≃ₗ[K] V) (h0 : 0 < a) (hr : a < r) :
    chainPlane r i a = negSpace (i (a - 1)) ⊓ negSpace (i a) := by
  simp [chainPlane, Nat.pos_iff_ne_zero.mp h0, Nat.ne_of_lt hr]

omit [Finite K] [FiniteDimensional K V] in
theorem disjoint_of_orth {U U' : Submodule K V} (hU' : PolarNondegOn Q U')
    (horth : ∀ x ∈ U, ∀ y ∈ U', polar Q x y = 0) : Disjoint U U' := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  exact hU' x hx' fun y hy => horth x hx y hy

omit [Finite K] in
theorem eq_sup_of_orth {W U U' : Submodule K V} (hU : U ≤ W) (hU' : U' ≤ W)
    (hnd : PolarNondegOn Q U') (horth : ∀ x ∈ U, ∀ y ∈ U', polar Q x y = 0)
    (h : Module.finrank K U + Module.finrank K U' = Module.finrank K W) : W = U ⊔ U' := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq (sup_le hU hU') ?_
  rw [Frame.finrank_sup_of_disjoint (disjoint_of_orth hnd horth)]
  exact h

variable {r : ℕ} {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}

theorem VChain.pd (hodd : Odd (Nat.card K)) (hc : VChain Q r L i) {a : ℕ} (ha : a + 1 < r) :
    PairDecomposition Q (i a) (i (a + 1)) :=
  (lemma_6_10 hodd (hc.fund a (by omega)) (hc.fund (a + 1) ha) (hc.comm a ha) (hc.norm a ha)
    (hc.ncent a ha)).1

end Chain

section PlaneFacts

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {r : ℕ} {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}

theorem VChain.pd' (hodd : Odd (Nat.card K)) (hc : VChain Q r L i) {a b : ℕ} (hab : a + 1 = b)
    (hb : b < r) : PairDecomposition Q (i a) (i b) := by
  subst hab
  exact hc.pd hodd hb

omit [Finite K] [FiniteDimensional K V] in
theorem VChain.hyp' (hc : VChain Q r L i) {a b : ℕ} (hab : a + 1 = b) (hb : b < r) :
    HasSingularVector Q (negSpace (i a) ⊓ negSpace (i b)) := by
  subst hab
  exact hc.hyp a hb

omit [Finite K] [FiniteDimensional K V] in
theorem chainPlane_le_right {a : ℕ} (ha : a < r) :
    chainPlane r i a ≤ negSpace (i a) := by
  by_cases h0 : a = 0
  · subst h0
    rw [chainPlane_zero]
    exact inf_le_left
  · rw [chainPlane_mid i (Nat.pos_of_ne_zero h0) ha]
    exact inf_le_right

omit [Finite K] [FiniteDimensional K V] in
theorem chainPlane_le_left (hr : 1 ≤ r) {a : ℕ} (h0 : 1 ≤ a) (ha : a ≤ r) :
    chainPlane r i a ≤ negSpace (i (a - 1)) := by
  by_cases h : a = r
  · subst h
    rw [chainPlane_last hr]
    exact inf_le_left
  · rw [chainPlane_mid i h0 (lt_of_le_of_ne ha h)]
    exact inf_le_left

theorem chainPlane_facts (hodd : Odd (Nat.card K)) (hc : VChain Q r L i) (hr : 2 ≤ r) {a : ℕ}
    (ha : a ≤ r) :
    Module.finrank K (chainPlane r i a) = 2 ∧ PolarNondegOn Q (chainPlane r i a) ∧
      HasSingularVector Q (chainPlane r i a) := by
  by_cases h0 : a = 0
  · subst h0
    have pd := hc.pd' hodd (a := 0) (b := 1) rfl (by omega)
    rw [chainPlane_zero]
    exact ⟨pd.finrank_U₁, pd.nondeg₁, pd.type₁₂.mpr (hc.hyp' rfl (by omega))⟩
  · by_cases h : a = r
    · subst h
      have pd := hc.pd' hodd (a := a - 2) (b := a - 1) (by omega) (by omega)
      rw [chainPlane_last (by omega), inf_comm]
      exact ⟨pd.finrank_U₃, pd.nondeg₃, pd.type₂₃.mp (hc.hyp' (by omega) (by omega))⟩
    · have pd := hc.pd' hodd (a := a - 1) (b := a) (by omega) (lt_of_le_of_ne ha h)
      rw [chainPlane_mid i (Nat.pos_of_ne_zero h0) (lt_of_le_of_ne ha h)]
      exact ⟨pd.finrank_U₂, pd.nondeg₂, hc.hyp' (by omega) (lt_of_le_of_ne ha h)⟩

theorem chainPlane_sup (hodd : Odd (Nat.card K)) (hc : VChain Q r L i) (hr : 2 ≤ r) {a : ℕ}
    (ha : a < r) :
    negSpace (i a) = chainPlane r i a ⊔ chainPlane r i (a + 1) ∧
      ∀ x ∈ chainPlane r i a, ∀ y ∈ chainPlane r i (a + 1), polar Q x y = 0 := by
  by_cases h0 : a = 0
  · subst h0
    have pd := hc.pd' hodd (a := 0) (b := 1) rfl (by omega)
    rw [chainPlane_zero, chainPlane_mid i (by omega) (by omega : 0 + 1 < r)]
    exact ⟨by simpa using pd.negSpace_i₁, by simpa using pd.orth₁₂⟩
  · by_cases hl : a + 1 = r
    · have pd := hc.pd' hodd (a := a - 1) (b := a) (by omega) ha
      rw [chainPlane_mid i (Nat.pos_of_ne_zero h0) ha, hl, chainPlane_last (by omega), inf_comm
        (negSpace (i (r - 1)))]
      have e1 : a - 1 = r - 2 := by omega
      have e2 : a = r - 1 := by omega
      rw [e1, e2] at pd
      rw [e1, e2]
      exact ⟨pd.negSpace_i₂, pd.orth₂₃⟩
    · have hlt : a + 1 < r := by omega
      have hpos : 0 < a := Nat.pos_of_ne_zero h0
      have hne : Module.finrank K (chainPlane r i a) = 2 :=
        (chainPlane_facts hodd hc hr ha.le).1
      have h1 := chainPlane_facts hodd hc hr hlt.le
      have horth : ∀ x ∈ chainPlane r i a, ∀ y ∈ chainPlane r i (a + 1), polar Q x y = 0 := by
        intro x hx y hy
        have hx' := chainPlane_le_left (i := i) (by omega) hpos ha.le hx
        have hy' := chainPlane_le_right (i := i) hlt hy
        exact hc.orth (a - 1) (a + 1) (by omega) hlt x hx' y hy'
      refine ⟨?_, horth⟩
      refine eq_sup_of_orth (chainPlane_le_right ha) ?_ h1.2.1 horth ?_
      · rw [chainPlane_mid i (by omega) hlt]
        simp only [Nat.add_sub_cancel]
        exact inf_le_left
      · rw [hne, h1.1, finrank_negSpace hodd (hc.fund a ha)]

end PlaneFacts

section Pairs

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {r : ℕ} {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}

theorem chainPlane_orth (hodd : Odd (Nat.card K)) (hc : VChain Q r L i) (hr : 2 ≤ r) {a b : ℕ}
    (hab : a + 2 ≤ b) (hb : b ≤ r) :
    ∀ x ∈ chainPlane r i a, ∀ y ∈ chainPlane r i b, polar Q x y = 0 := by
  intro x hx y hy
  by_cases h3 : a + 3 ≤ b
  · have hx' := chainPlane_le_right (i := i) (by omega : a < r) hx
    have hy' := chainPlane_le_left (i := i) (by omega : 1 ≤ r) (by omega : 1 ≤ b) hb hy
    exact hc.orth a (b - 1) (by omega) (by omega) x hx' y hy'
  · have hb2 : b = a + 2 := by omega
    subst hb2
    by_cases h1 : 1 ≤ a
    · have hx' := chainPlane_le_left (i := i) (by omega : 1 ≤ r) h1 (by omega) hx
      have hy' := chainPlane_le_left (i := i) (by omega : 1 ≤ r) (by omega : 1 ≤ a + 2) hb hy
      have e : a + 2 - 1 = a + 1 := by omega
      rw [e] at hy'
      exact hc.orth (a - 1) (a + 1) (by omega) (by omega) x hx' y hy'
    · have ha0 : a = 0 := by omega
      subst ha0
      by_cases hr2 : 2 < r
      · have hx' := chainPlane_le_right (i := i) (by omega : 0 < r) hx
        have hy' := chainPlane_le_right (i := i) hr2 hy
        exact hc.orth 0 2 (by omega) hr2 x hx' y hy'
      · have hr2' : r = 2 := by omega
        subst hr2'
        have pd := hc.pd' hodd (a := 0) (b := 1) rfl (by omega)
        rw [chainPlane_zero] at hx
        rw [zero_add, chainPlane_last (by omega), inf_comm] at hy
        exact pd.orth₁₃ x hx y hy

theorem exists_pairs_planes (hodd : Odd (Nat.card K))
    (hc : VChain Q r L i) (hr : 2 ≤ r) :
    ∃ P0 : ℕ → HypPair Q, ∀ a ≤ r, hypPlane (P0 a) = chainPlane r i a := by
  obtain ⟨hf0, hn0, hs0⟩ := chainPlane_facts hodd hc hr (Nat.zero_le r)
  obtain ⟨P00, -, -, hP00⟩ := exists_hypPair_of_hasSingularVector hn0 hf0 hs0
  have : ∀ a : ℕ, ∃ P : HypPair Q, a ≤ r → hypPlane P = chainPlane r i a := fun a => by
    by_cases ha : a ≤ r
    · obtain ⟨hf, hn, hs⟩ := chainPlane_facts hodd hc hr ha
      obtain ⟨P, -, -, hP⟩ := exists_hypPair_of_hasSingularVector hn hf hs
      exact ⟨P, fun _ => hP.symm⟩
    · exact ⟨P00, fun h => absurd h ha⟩
  choose P hP using this
  exact ⟨P, fun a ha => hP a ha⟩

open scoped Classical in
noncomputable def orientedPairs (ε : Bool) (L : ℕ → Subgroup (V ≃ₗ[K] V)) (P0 : ℕ → HypPair Q) :
    ℕ → HypPair Q
  | 0 => P0 0
  | a + 1 =>
    if h : (orientedPairs ε L P0 a).Orth (P0 (a + 1)) then
      if L a = (oFrame ε (orientedPairs ε L P0 a) (P0 (a + 1)) h).La.range then P0 (a + 1)
      else swapPair (P0 (a + 1))
    else P0 (a + 1)

omit [Finite K] [FiniteDimensional K V] in
theorem hypPlane_orientedPairs (ε : Bool) (L : ℕ → Subgroup (V ≃ₗ[K] V)) (P0 : ℕ → HypPair Q)
    (a : ℕ) : hypPlane (orientedPairs ε L P0 a) = hypPlane (P0 a) := by
  cases a with
  | zero => rfl
  | succ a =>
    unfold orientedPairs
    split_ifs
    · rfl
    · exact hypPlane_swapPair _
    · rfl

theorem exists_chain_pairs (ε : Bool) (hodd : Odd (Nat.card K)) (hc : VChain Q r L i)
    (hr : 2 ≤ r) :
    ∃ p : ℕ → HypPair Q, ∃ horth : ∀ a b, a ≤ r → b ≤ r → a ≠ b → (p a).Orth (p b),
      (∀ a ≤ r, hypPlane (p a) = chainPlane r i a) ∧
      ∀ a (ha : a < r),
        L a = (oFrame ε (p a) (p (a + 1)) (horth a (a + 1) ha.le ha (by omega))).La.range := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨P0, hP0⟩ := exists_pairs_planes hodd hc hr
  set p : ℕ → HypPair Q := orientedPairs ε L P0 with hp
  have hpl : ∀ a ≤ r, hypPlane (p a) = chainPlane r i a := fun a ha => by
    rw [hp, hypPlane_orientedPairs, hP0 a ha]
  have hpo : ∀ a b, a ≤ r → b ≤ r → a ≠ b → (p a).Orth (p b) := by
    intro a b ha hb hab
    refine orth_of_polar_hypPlane fun x hx y hy => ?_
    rw [hpl a ha] at hx
    rw [hpl b hb] at hy
    rcases lt_or_gt_of_ne hab with h | h
    · rcases Nat.lt_or_ge (a + 1) b with h' | h'
      · exact chainPlane_orth hodd hc hr (by omega) hb x hx y hy
      · have hb' : b = a + 1 := by omega
        subst hb'
        exact (chainPlane_sup hodd hc hr (by omega)).2 x hx y hy
    · rw [polar_comm]
      rcases Nat.lt_or_ge (b + 1) a with h' | h'
      · exact chainPlane_orth hodd hc hr (by omega) ha y hy x hx
      · have ha' : a = b + 1 := by omega
        subst ha'
        exact (chainPlane_sup hodd hc hr (by omega)).2 y hy x hx
  refine ⟨p, hpo, hpl, fun a ha => ?_⟩
  have hspan : hypPlane (p a) ⊔ hypPlane (P0 (a + 1)) = negSpace (i a) := by
    rw [hpl a ha.le, hP0 (a + 1) ha]
    exact ((chainPlane_sup hodd hc hr ha).1).symm
  have hO : (p a).Orth (P0 (a + 1)) := by
    refine orth_of_polar_hypPlane fun x hx y hy => ?_
    rw [hpl a ha.le] at hx
    rw [hP0 (a + 1) ha] at hy
    exact (chainPlane_sup hodd hc hr ha).2 x hx y hy
  have hor := La_range_orientE ε h2 (hc.fund a ha) hO hspan
  classical
  have hdef : p (a + 1) = if h : (p a).Orth (P0 (a + 1)) then
      (if L a = (oFrame ε (p a) (P0 (a + 1)) h).La.range then P0 (a + 1)
        else swapPair (P0 (a + 1)))
      else P0 (a + 1) := by
    rw [hp]
    simp only [orientedPairs]
  by_cases hcond : L a = (oFrame ε (p a) (P0 (a + 1)) hO).La.range
  · have hq : p (a + 1) = P0 (a + 1) := by
      rw [hdef]
      simp [hO, hcond]
    have key : ∀ (q : HypPair Q) (_ : q = P0 (a + 1)) (h' : (p a).Orth q),
        L a = (oFrame ε (p a) q h').La.range := by
      intro q hq' h'
      subst hq'
      exact hcond
    exact key (p (a + 1)) hq _
  · have hq : p (a + 1) = swapPair (P0 (a + 1)) := by
      rw [hdef]
      simp [hO, hcond]
    have key : ∀ (q : HypPair Q) (_ : q = swapPair (P0 (a + 1))) (h' : (p a).Orth q),
        L a = (oFrame ε (p a) q h').La.range := by
      intro q hq' h'
      subst hq'
      exact hor.resolve_left hcond
    exact key (p (a + 1)) hq _

end Pairs

end CFSG.ClassicalInvolution.RouteD.Gaps
