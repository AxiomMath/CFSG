module

public import CFSG.GroupTheory.SevenInvolutionWreathLawGraph
public import CFSG.GroupTheory.InvolutionHexagonIncidence

public section

namespace CFSG.GroupTheory.InvolutionHexagon

open CFSG.Assembly CFSG.GroupTheory.SevenInvolutionWreathLaw

variable {G : Type*} [Group G]

abbrev InvLine (G : Type*) [Group G] : Type _ :=
  {T : Set G // ∃ u v : G, orderOf u = 2 ∧ orderOf v = 2 ∧ u ≠ v ∧ u * v = v * u ∧
    T = {u, v, u * v}}

abbrev invInc (G : Type*) [Group G] (p : {g : G // orderOf g = 2}) (T : InvLine G) : Prop :=
  (p : G) ∈ T.1

theorem orderOf_mul_eq_two {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v)
    (hc : u * v = v * u) : orderOf (u * v) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu1 := mul_self_of_orderOf_eq_two hu
  have hv1 := mul_self_of_orderOf_eq_two hv
  refine orderOf_eq_prime ?_ fun h => huv ?_
  · rw [sq, mul_assoc, ← mul_assoc v, ← hc, mul_assoc, hv1, mul_one, hu1]
  · calc u = u * (v * v) := by rw [hv1, mul_one]
      _ = (u * v) * v := by rw [mul_assoc]
      _ = v := by rw [h, one_mul]

theorem InvLine.orderOf_of_mem (T : InvLine G) {x : G} (hx : x ∈ T.1) : orderOf x = 2 := by
  obtain ⟨u, v, hu, hv, huv, hc, hT⟩ := T.2
  rw [hT] at hx
  rcases hx with rfl | rfl | rfl
  · exact hu
  · exact hv
  · exact orderOf_mul_eq_two hu hv huv hc

theorem InvLine.commute_of_mem (T : InvLine G) {x y : G} (hx : x ∈ T.1) (hy : y ∈ T.1) :
    x * y = y * x := by
  obtain ⟨u, v, -, -, -, hc, hT⟩ := T.2
  have huv : Commute u v := hc
  have h1 : Commute u (u * v) := (Commute.refl u).mul_right huv
  have h2 : Commute v (u * v) := huv.symm.mul_right (Commute.refl v)
  rw [hT] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  exacts [rfl, huv, h1, huv.symm, rfl, h2, h1.symm, h2.symm, rfl]

omit [Group G] in
theorem ncard_triple {a b c : G} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Set G).ncard = 3 :=
  Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩

theorem ncard_line_triple {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v) :
    ({u, v, u * v} : Set G).ncard = 3 := by
  refine ncard_triple huv (fun h => ne_one_of_orderOf_eq_two hv ?_)
    (fun h => ne_one_of_orderOf_eq_two hu ?_)
  · exact (mul_eq_left.mp h.symm)
  · exact (mul_eq_right.mp h.symm)

theorem InvLine.ncard (T : InvLine G) : T.1.ncard = 3 := by
  obtain ⟨u, v, hu, hv, huv, -, hT⟩ := T.2
  rw [hT]
  exact ncard_line_triple hu hv huv

theorem InvLine.mul_mem (T : InvLine G) {x y : G} (hx : x ∈ T.1) (hy : y ∈ T.1) (hxy : x ≠ y) :
    x * y ∈ T.1 := by
  obtain ⟨u, v, hu, hv, -, hc, hT⟩ := T.2
  have hu1 := mul_self_of_orderOf_eq_two hu
  have hv1 := mul_self_of_orderOf_eq_two hv
  rw [hT] at hx hy ⊢
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact absurd rfl hxy
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (by rw [← mul_assoc, hu1, one_mul]))
  · exact Or.inr (Or.inr hc.symm)
  · exact absurd rfl hxy
  · exact Or.inl (by rw [← mul_assoc, ← hc, mul_assoc, hv1, mul_one])
  · exact Or.inr (Or.inl (by rw [hc, mul_assoc, hu1, mul_one]))
  · exact Or.inl (by rw [mul_assoc, hv1, mul_one])
  · exact absurd rfl hxy

theorem InvLine.eq_triple (T : InvLine G) {x y : G} (hx : x ∈ T.1) (hy : y ∈ T.1)
    (hxy : x ≠ y) : T.1 = {x, y, x * y} := by
  have hT3 := T.ncard
  have hfin : T.1.Finite := Set.finite_of_ncard_pos (by rw [hT3]; norm_num)
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_ hfin).symm
  · intro z hz
    rcases hz with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact T.mul_mem hx hy hxy
  · rw [hT3, ncard_line_triple (T.orderOf_of_mem hx) (T.orderOf_of_mem hy) hxy]

@[expose] def lineOf {p q : G} (hp : orderOf p = 2) (hq : orderOf q = 2) (hpq : p ≠ q)
    (hc : p * q = q * p) : InvLine G :=
  ⟨{p, q, p * q}, p, q, hp, hq, hpq, hc, rfl⟩

theorem left_mem_lineOf {p q : G} (hp : orderOf p = 2) (hq : orderOf q = 2) (hpq : p ≠ q)
    (hc : p * q = q * p) : p ∈ (lineOf hp hq hpq hc).1 :=
  Or.inl rfl

theorem right_mem_lineOf {p q : G} (hp : orderOf p = 2) (hq : orderOf q = 2) (hpq : p ≠ q)
    (hc : p * q = q * p) : q ∈ (lineOf hp hq hpq hc).1 :=
  Or.inr (Or.inl rfl)

theorem InvLine.eq_of_mem {T T' : InvLine G} {x y : G} (hxy : x ≠ y) (hx : x ∈ T.1)
    (hy : y ∈ T.1) (hx' : x ∈ T'.1) (hy' : y ∈ T'.1) : T = T' :=
  Subtype.ext ((T.eq_triple hx hy hxy).trans (T'.eq_triple hx' hy' hxy).symm)

theorem collinear_iff {p q : {g : G // orderOf g = 2}} (hpq : p ≠ q) :
    Collinear (invInc G) p q ↔ (p : G) * q = q * p := by
  constructor
  · rintro ⟨T, hp, hq⟩
    exact T.commute_of_mem hp hq
  · intro hc
    have hpq' : (p : G) ≠ q := fun h => hpq (Subtype.ext h)
    exact ⟨lineOf p.2 q.2 hpq' hc, left_mem_lineOf p.2 q.2 hpq' hc,
      right_mem_lineOf p.2 q.2 hpq' hc⟩

theorem involutionGraph_eq_collinearityGraph :
    involutionGraph G = collinearityGraph (invInc G) := by
  ext p q
  rw [adj_iff_ne_and_commute, collinearityGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hpq, hc⟩
    exact ⟨hpq, Or.inl ((collinear_iff hpq).mpr hc)⟩
  · rintro ⟨hpq, h | h⟩
    · exact ⟨hpq, (collinear_iff hpq).mp h⟩
    · exact ⟨hpq, ((collinear_iff (Ne.symm hpq)).mp h).symm⟩

theorem adj_iff_collinear {p q : {g : G // orderOf g = 2}} :
    (involutionGraph G).Adj p q ↔ p ≠ q ∧ Collinear (invInc G) p q := by
  rw [adj_iff_ne_and_commute]
  constructor
  · rintro ⟨hpq, hc⟩
    exact ⟨hpq, (collinear_iff hpq).mpr hc⟩
  · rintro ⟨hpq, h⟩
    exact ⟨hpq, (collinear_iff hpq).mp h⟩

theorem ncard_lines_through [Finite G]
    (hval : ∀ z : {g : G // orderOf g = 2}, ((involutionGraph G).neighborSet z).ncard = 6)
    (p : {g : G // orderOf g = 2}) : {T : InvLine G | (p : G) ∈ T.1}.ncard = 3 := by
  classical
  have := Fintype.ofFinite {g : G // orderOf g = 2}
  have : Finite (InvLine G) := Subtype.finite
  have := Fintype.ofFinite (InvLine G)
  set s : Finset {g : G // orderOf g = 2} :=
    Finset.univ.filter fun q => (involutionGraph G).Adj p q with hs
  set t : Finset (InvLine G) := Finset.univ.filter fun T => (p : G) ∈ T.1 with ht
  have hs6 : s.card = 6 := by
    rw [← hval p, ← Set.ncard_coe_finset, hs, Finset.coe_filter]
    congr 1
    ext q
    simp
  have hm : ∀ q ∈ s, (t.bipartiteAbove (invInc G) q).card = 1 := by
    intro q hq
    have hpq := (adj_iff_ne_and_commute.mp (Finset.mem_filter.mp hq).2)
    have hpq' : (p : G) ≠ q := fun h => hpq.1 (Subtype.ext h)
    rw [Finset.card_eq_one]
    refine ⟨lineOf p.2 q.2 hpq' hpq.2,
      Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun T' hT' => ?_⟩⟩
    · rw [Finset.mem_bipartiteAbove, ht, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, left_mem_lineOf p.2 q.2 hpq' hpq.2⟩,
        right_mem_lineOf p.2 q.2 hpq' hpq.2⟩
    · rw [Finset.mem_bipartiteAbove, ht, Finset.mem_filter] at hT'
      exact InvLine.eq_of_mem hpq' hT'.1.2 hT'.2 (left_mem_lineOf p.2 q.2 hpq' hpq.2)
        (right_mem_lineOf p.2 q.2 hpq' hpq.2)
  have hn : ∀ T ∈ t, (s.bipartiteBelow (invInc G) T).card = 2 := by
    intro T hT
    have hpT : (p : G) ∈ T.1 := (Finset.mem_filter.mp hT).2
    have heq : (s.bipartiteBelow (invInc G) T : Set {g : G // orderOf g = 2}) =
        {q : {g : G // orderOf g = 2} | (q : G) ∈ T.1} \ {p} := by
      ext q
      simp only [Finset.mem_coe, Finset.mem_bipartiteBelow, hs, Finset.mem_filter,
        Finset.mem_univ, true_and, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
        adj_iff_ne_and_commute, invInc]
      constructor
      · rintro ⟨⟨hpq, -⟩, hqT⟩
        exact ⟨hqT, Ne.symm hpq⟩
      · rintro ⟨hqT, hqp⟩
        exact ⟨⟨Ne.symm hqp, T.commute_of_mem hpT hqT⟩, hqT⟩
    have hT3 : {q : {g : G // orderOf g = 2} | (q : G) ∈ T.1}.ncard = 3 := by
      rw [← T.ncard, ← Set.ncard_image_of_injective _ Subtype.val_injective]
      congr 1
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact hq
      · intro hx
        exact ⟨⟨x, T.orderOf_of_mem hx⟩, hx, rfl⟩
    rw [← Set.ncard_coe_finset, heq, Set.ncard_sdiff_singleton_of_mem (by exact hpT), hT3]
  have hdc := Finset.card_mul_eq_card_mul (invInc G) hm hn
  rw [hs6] at hdc
  have hset : {T : InvLine G | (p : G) ∈ T.1} = (t : Set (InvLine G)) := by
    ext T
    simp [ht]
  rw [hset, Set.ncard_coe_finset]
  omega

theorem involutionHexagonData [Finite G] (hcard : Nat.card {g : G // orderOf g = 2} = 63)
    (hlaw : InvolutionProductLaw G)
    (hval : ∀ z : {g : G // orderOf g = 2}, ((involutionGraph G).neighborSet z).ncard = 6) :
    HexagonData (invInc G) where
  finite_points := Subtype.finite
  finite_lines := Subtype.finite
  card_points := hcard
  ncard_points T := by
    rw [← T.ncard, ← Set.ncard_image_of_injective _ Subtype.val_injective]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hx
      exact ⟨⟨x, T.orderOf_of_mem hx⟩, hx, rfl⟩
  ncard_lines := ncard_lines_through hval
  eq_of_inc {p q ℓ ℓ'} hpq hp hq hp' hq' :=
    InvLine.eq_of_mem (fun h => hpq (Subtype.ext h)) hp hq hp' hq'
  exists_inc_of_triangle {a b c} hab hbc hac hcab hcbc hcac := by
    have hab' : (a : G) * b = b * a := (collinear_iff hab).mp hcab
    have hbc' : (b : G) * c = c * b := (collinear_iff hbc).mp hcbc
    have hac' : (a : G) * c = c * a := (collinear_iff hac).mp hcac
    have habv : (a : G) ≠ b := fun h => hab (Subtype.ext h)
    have hcen : ∀ x : {g : G // orderOf g = 2}, (x : G) * c = c * x →
        (x : G) ∈ Subgroup.centralizer {(c : G)} := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr hx
    have hprod : (a : G) * b = c := (hlaw c a b c.2 a.2 b.2 (hcen a hac') (hcen b hbc') habv
      (fun h => hac (Subtype.ext h)) (fun h => hbc (Subtype.ext h))).1 hab'
    refine ⟨lineOf a.2 b.2 habv hab', left_mem_lineOf a.2 b.2 habv hab',
      right_mem_lineOf a.2 b.2 habv hab', ?_⟩
    show (c : G) ∈ ({(a : G), (b : G), (a : G) * (b : G)} : Set G)
    rw [hprod]
    exact Or.inr (Or.inr rfl)
  not_square := by
    rintro ⟨a, b, c, d, hnd, hab, hbc, hcd, hda, hac, hbd⟩
    have hne : ∀ {x y : {g : G // orderOf g = 2}}, Collinear (invInc G) x y → x ≠ y →
        (involutionGraph G).Adj x y := fun hxy hne => adj_iff_collinear.mpr ⟨hne, hxy⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true] at hnd'
    obtain ⟨⟨hab', -, had'⟩, ⟨hbc', -⟩, hcd'⟩ := hnd'
    exact not_exists_induced_square hlaw ⟨a, b, c, d, hnd, hne hab hab', hne hbc hbc',
      hne hcd hcd', hne hda (Ne.symm had'), fun h => hac (adj_iff_collinear.mp h).2,
      fun h => hbd (adj_iff_collinear.mp h).2⟩
  not_pentagon := by
    rintro ⟨a, b, c, d, e, hnd, hab, hbc, hcd, hde, hea, hac, had, hbd, hbe, hce⟩
    have hne : ∀ {x y : {g : G // orderOf g = 2}}, Collinear (invInc G) x y → x ≠ y →
        (involutionGraph G).Adj x y := fun hxy hne => adj_iff_collinear.mpr ⟨hne, hxy⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true] at hnd'
    obtain ⟨⟨hab', -, -, hae'⟩, ⟨hbc', -, -⟩, ⟨hcd', -⟩, hde'⟩ := hnd'
    exact not_exists_induced_pentagon hlaw ⟨a, b, c, d, e, hnd,
      hne hab hab', hne hbc hbc', hne hcd hcd', hne hde hde', hne hea (Ne.symm hae'),
      fun h => hac (adj_iff_collinear.mp h).2, fun h => had (adj_iff_collinear.mp h).2,
      fun h => hbd (adj_iff_collinear.mp h).2, fun h => hbe (adj_iff_collinear.mp h).2,
      fun h => hce (adj_iff_collinear.mp h).2⟩

end CFSG.GroupTheory.InvolutionHexagon
