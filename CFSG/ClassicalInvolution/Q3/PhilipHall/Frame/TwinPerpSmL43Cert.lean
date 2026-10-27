module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocLin
public import Certificates.Certificate397502

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.L43

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc CFSG.Monster.B.Fischer Certificates.L43TwinQ8

set_option linter.unusedSectionVars false

@[expose] def q8Set {G : Type*} [Group G] (a b : G) : Set G :=
  {1, a * a, a, a⁻¹, b, b⁻¹, a * b, b * a}

theorem q8Set_subset_closure {G : Type*} [Group G] (a b : G) :
    q8Set a b ⊆ Subgroup.closure ({a, b} : Set G) := by
  have ha : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hb : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  intro x hx
  simp only [q8Set, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact mul_mem ha ha
  · exact ha
  · exact inv_mem ha
  · exact hb
  · exact inv_mem hb
  · exact mul_mem ha hb
  · exact mul_mem hb ha

section Defs

variable (𝕜 : Type) [Field 𝕜] [CharP 𝕜 3]

@[expose] noncomputable def S0 : Subgroup (MulAut (projectiveSL 4 𝕜)) :=
  Subgroup.closure ((fun k => ev 4 𝕜 gens[k]!) '' {k | k < gens.size})

@[expose] noncomputable def tw : MulAut (projectiveSL 4 𝕜) := ev 4 𝕜 t0

@[expose] noncomputable def cw : MulAut (projectiveSL 4 𝕜) := ev 4 𝕜 wc

@[expose] noncomputable def Q1 : Subgroup (MulAut (projectiveSL 4 𝕜)) :=
  Subgroup.closure {ev 4 𝕜 q1a, ev 4 𝕜 q1b}

@[expose] noncomputable def Q2 : Subgroup (MulAut (projectiveSL 4 𝕜)) :=
  Subgroup.closure {ev 4 𝕜 q2a, ev 4 𝕜 q2b}

end Defs

structure CheckFacts : Prop where
  gens_valid : ∀ k < gens.size, eltValid 4 gens[k]! = true
  cert : arrCertOK (locAct 4 gens) gens.size (eltValid 4) (eltKey 4) (eltOne 4) (bfs ()) = true
  size : (bfs ()).pts.size = 2 ^ 9
  t0_valid : eltValid 4 t0 = true
  q1a_valid : eltValid 4 q1a = true
  q1b_valid : eltValid 4 q1b = true
  q2a_valid : eltValid 4 q2a = true
  q2b_valid : eltValid 4 q2b = true
  wc_valid : eltValid 4 wc = true
  wc_eE : eE 4 wc = 0
  wc_inF : inF4 wc = true
  gens_comm : ∀ k < gens.size, commutes gens[k]! t0 = true
  wc_comm : commutes wc t0 = true
  pairs : pairsOK (bfs ()).pts = true

theorem checkFacts (h : check () = true) : CheckFacts := by
  unfold check at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

section Sound

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 3] [Finite 𝕜]

theorem S0_spec (h𝕜 : Nat.card 𝕜 = 3) (hc : CheckFacts) :
    (∀ x, x ∈ S0 𝕜 ↔ ∃ i < (bfs ()).pts.size, ev 4 𝕜 (bfs ()).pts[i]! = x) ∧
      Nat.card (S0 𝕜) = 2 ^ 9 := by
  have hn : (0 : ℕ) < 4 := by norm_num
  have hact : ∀ k < gens.size, ∀ a, eltValid 4 a = true →
      ev 4 𝕜 (locAct 4 gens k a) = ev 4 𝕜 gens[k]! * ev 4 𝕜 a := by
    intro k hk a ha
    unfold locAct
    rw [ev_eltNorm hn (eltValid_eltMul (n := 4) hn (hc.gens_valid k hk) ha),
      ev_eltMul hn (hc.gens_valid k hk) ha]
  have hkey : ∀ a b, eltValid 4 a = true → eltValid 4 b = true → ev 4 𝕜 a = ev 4 𝕜 b →
      eltKey 4 a = eltKey 4 b := fun a b ha hb hab =>
    eltKey_eq_of_eltEq (eltEq_of_ev_eq 𝕜 (by norm_num) h𝕜 ha hb hab)
  obtain ⟨hmem, hcard⟩ := card_closure_of_arrCertOK (G := MulAut (projectiveSL 4 𝕜))
    (dec := ev 4 𝕜) (gens := fun k => ev 4 𝕜 gens[k]!) hc.cert hact hkey (ev_eltOne hn)
  exact ⟨hmem, by rw [S0, hcard, hc.size]⟩

omit [Finite 𝕜] in
theorem ev_eq_of_commutes {x y : Array ℕ} (hx : eltValid 4 x = true) (hy : eltValid 4 y = true)
    (h : commutes x y = true) : ev 4 𝕜 x * ev 4 𝕜 y = ev 4 𝕜 y * ev 4 𝕜 x := by
  have hn : (0 : ℕ) < 4 := by norm_num
  have := ev_eq_of_eltEq 𝕜 hn (eltValid_eltMul (n := 4) hn hx hy)
    (eltValid_eltMul (n := 4) hn hy hx) h
  rwa [ev_eltMul hn hx hy, ev_eltMul hn hy hx] at this

theorem ne_of_commutes_eq_false (h𝕜 : Nat.card 𝕜 = 3) {x y : Array ℕ}
    (hx : eltValid 4 x = true) (hy : eltValid 4 y = true) (h : commutes x y = false) :
    ev 4 𝕜 x * ev 4 𝕜 y ≠ ev 4 𝕜 y * ev 4 𝕜 x := by
  have hn : (0 : ℕ) < 4 := by norm_num
  intro he
  have h1 : commutes x y = true := by
    refine eltEq_of_ev_eq 𝕜 (by norm_num) h𝕜 (eltValid_eltMul (n := 4) hn hx hy)
      (eltValid_eltMul (n := 4) hn hy hx) ?_
    rw [ev_eltMul hn hx hy, ev_eltMul hn hy hx, he]
  rw [h] at h1
  exact Bool.false_ne_true h1

theorem memQ8_iff (h𝕜 : Nat.card 𝕜 = 3) {x a b : Array ℕ} (hx : eltValid 4 x = true)
    (ha : eltValid 4 a = true) (hb : eltValid 4 b = true) :
    memQ8 x a b = true ↔ ev 4 𝕜 x ∈ q8Set (ev 4 𝕜 a) (ev 4 𝕜 b) := by
  have hn : (0 : ℕ) < 4 := by norm_num
  have key : ∀ z, eltValid 4 z = true → (eltEq 4 x z = true ↔ ev 4 𝕜 x = ev 4 𝕜 z) :=
    fun z hz => ⟨ev_eq_of_eltEq 𝕜 hn hx hz, eltEq_of_ev_eq 𝕜 (by norm_num) h𝕜 hx hz⟩
  have v1 := eltValid_eltOne (n := 4) hn
  have v2 := eltValid_eltMul (n := 4) hn ha ha
  have v3 := eltValid_eltInv (n := 4) hn ha
  have v4 := eltValid_eltInv (n := 4) hn hb
  have v5 := eltValid_eltMul (n := 4) hn ha hb
  have v6 := eltValid_eltMul (n := 4) hn hb ha
  simp only [memQ8, q8Words, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    key _ v1, key _ v2, key _ ha, key _ v3, key _ hb, key _ v4, key _ v5, key _ v6,
    ev_eltOne hn, ev_eltMul hn ha ha, ev_eltInv hn ha, ev_eltInv hn hb, ev_eltMul hn ha hb,
    ev_eltMul hn hb ha, q8Set, Set.mem_insert_iff, Set.mem_singleton_iff]

omit [Finite 𝕜] in
theorem S0_le_centralizer (hc : CheckFacts) :
    S0 𝕜 ≤ Subgroup.centralizer ({tw 𝕜} : Set (MulAut (projectiveSL 4 𝕜))) := by
  rw [S0, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact ev_eq_of_commutes (hc.gens_valid k hk) hc.t0_valid (hc.gens_comm k hk)

omit [Finite 𝕜] in
theorem cw_comm (hc : CheckFacts) : cw 𝕜 * tw 𝕜 = tw 𝕜 * cw 𝕜 :=
  ev_eq_of_commutes hc.wc_valid hc.t0_valid hc.wc_comm

omit [Finite 𝕜] in
theorem cw_mem_inner (hc : CheckFacts) :
    cw 𝕜 ∈ (MulAut.conj : projectiveSL 4 𝕜 →* MulAut (projectiveSL 4 𝕜)).range := by
  obtain ⟨G, hG⟩ := inF4_spec (K := 𝕜) hc.wc_valid hc.wc_eE hc.wc_inF
  exact ⟨proj 4 𝕜 G, hG.symm⟩

theorem pair_classify (h𝕜 : Nat.card 𝕜 = 3)
    {a b : MulAut (projectiveSL 4 𝕜)} (ha : a ∈ S0 𝕜) (hb : b ∈ S0 𝕜) (ha2 : a * a = tw 𝕜)
    (hb2 : b * b = tw 𝕜) (hab : b * a * b⁻¹ = a⁻¹) :
    Subgroup.closure {a, b} = Q1 𝕜 ∨ Subgroup.closure {a, b} = Q2 𝕜 ∨
      ((cw 𝕜 * a * (cw 𝕜)⁻¹ ∉ q8Set a b ∨ cw 𝕜 * b * (cw 𝕜)⁻¹ ∉ q8Set a b) ∧
        (a * (cw 𝕜 * a * (cw 𝕜)⁻¹) ≠ cw 𝕜 * a * (cw 𝕜)⁻¹ * a ∨
          a * (cw 𝕜 * b * (cw 𝕜)⁻¹) ≠ cw 𝕜 * b * (cw 𝕜)⁻¹ * a ∨
          b * (cw 𝕜 * a * (cw 𝕜)⁻¹) ≠ cw 𝕜 * a * (cw 𝕜)⁻¹ * b ∨
          b * (cw 𝕜 * b * (cw 𝕜)⁻¹) ≠ cw 𝕜 * b * (cw 𝕜)⁻¹ * b)) := by
  have hn : (0 : ℕ) < 4 := by norm_num
  have hc := checkFacts Certificates.certificate397502
  obtain ⟨hmem, -⟩ := S0_spec h𝕜 hc
  obtain ⟨i, hi, rfl⟩ := (hmem a).1 ha
  obtain ⟨j, hj, rfl⟩ := (hmem b).1 hb
  have hvi : eltValid 4 (bfs ()).pts[i]! = true := arrCertOK_valid hc.cert hi
  have hvj : eltValid 4 (bfs ()).pts[j]! = true := arrCertOK_valid hc.cert hj
  have hsq : ∀ k < (bfs ()).pts.size, eltValid 4 (bfs ()).pts[k]! = true →
      ev 4 𝕜 (bfs ()).pts[k]! * ev 4 𝕜 (bfs ()).pts[k]! = tw 𝕜 →
      eltEq 4 (eltMul 4 (bfs ()).pts[k]! (bfs ()).pts[k]!) t0 = true := by
    intro k _ hv he
    refine eltEq_of_ev_eq 𝕜 (by norm_num) h𝕜 (eltValid_eltMul (n := 4) hn hv hv) hc.t0_valid ?_
    rw [ev_eltMul hn hv hv, he]
    rfl
  have hpair : pairOK (bfs ()).pts[i]! (bfs ()).pts[j]! = true := by
    have h0 := hc.pairs
    unfold pairsOK at h0
    simp only [List.all_eq_true, List.mem_filter, List.mem_range] at h0
    exact h0 i ⟨hi, hsq i hi hvi ha2⟩ j ⟨hj, hsq j hj hvj hb2⟩
  set A := (bfs ()).pts[i]! with hA
  set B := (bfs ()).pts[j]! with hB
  have hrel : eltEq 4 (eltConj 4 B A) (eltInv 4 A) = true := by
    refine eltEq_of_ev_eq 𝕜 (by norm_num) h𝕜 (eltValid_eltConj (n := 4) hn hvj hvi)
      (eltValid_eltInv (n := 4) hn hvi) ?_
    rw [ev_eltConj hn hvj hvi, ev_eltInv hn hvi, hab]
  unfold pairOK at hpair
  rw [hrel] at hpair
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hpair
  have hsame : ∀ {qa qb : Array ℕ}, eltValid 4 qa = true → eltValid 4 qb = true →
      sameQ8 A B qa qb = true →
      Subgroup.closure {ev 4 𝕜 A, ev 4 𝕜 B} = Subgroup.closure {ev 4 𝕜 qa, ev 4 𝕜 qb} := by
    intro qa qb hqa hqb hs
    simp only [sameQ8, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
    rw [memQ8_iff h𝕜 hvi hqa hqb] at h1
    rw [memQ8_iff h𝕜 hvj hqa hqb] at h2
    rw [memQ8_iff h𝕜 hqa hvi hvj] at h3
    rw [memQ8_iff h𝕜 hqb hvi hvj] at h4
    apply le_antisymm
    · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨q8Set_subset_closure _ _ h1, q8Set_subset_closure _ _ h2⟩
    · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨q8Set_subset_closure _ _ h3, q8Set_subset_closure _ _ h4⟩
  rcases hpair with (h1 | h2) | hw
  · exact Or.inl (hsame hc.q1a_valid hc.q1b_valid h1)
  · exact Or.inr (Or.inl (hsame hc.q2a_valid hc.q2b_valid h2))
  · right; right
    have hca := eltValid_eltConj (n := 4) hn hc.wc_valid hvi
    have hcb := eltValid_eltConj (n := 4) hn hc.wc_valid hvj
    have eca : ev 4 𝕜 (eltConj 4 wc A) = cw 𝕜 * ev 4 𝕜 A * (cw 𝕜)⁻¹ :=
      ev_eltConj hn hc.wc_valid hvi
    have ecb : ev 4 𝕜 (eltConj 4 wc B) = cw 𝕜 * ev 4 𝕜 B * (cw 𝕜)⁻¹ :=
      ev_eltConj hn hc.wc_valid hvj
    simp only [omega4Wit, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨hm, hco⟩ := hw
    refine ⟨?_, ?_⟩
    · rcases hm with hm | hm
      · left
        rw [← eca]
        intro hmem'
        rw [← memQ8_iff h𝕜 hca hvi hvj, hm] at hmem'
        exact Bool.false_ne_true hmem'
      · right
        rw [← ecb]
        intro hmem'
        rw [← memQ8_iff h𝕜 hcb hvi hvj, hm] at hmem'
        exact Bool.false_ne_true hmem'
    · rw [← eca, ← ecb]
      rcases hco with ((h | h) | h) | h
      · exact Or.inl (ne_of_commutes_eq_false h𝕜 hvi hca h)
      · exact Or.inr (Or.inl (ne_of_commutes_eq_false h𝕜 hvi hcb h))
      · exact Or.inr (Or.inr (Or.inl (ne_of_commutes_eq_false h𝕜 hvj hca h)))
      · exact Or.inr (Or.inr (Or.inr (ne_of_commutes_eq_false h𝕜 hvj hcb h)))

end Sound

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.L43
