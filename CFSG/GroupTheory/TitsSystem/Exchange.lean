module

public import CFSG.GroupTheory.TitsSystem.Basic
public import CFSG.GroupTheory.TitsSystem.Coxeter

public section

namespace CFSG.GroupTheory.TitsSystem

open CFSG.GH74.BNPair
open scoped Pointwise

theorem exchange_wordLength_eq {W : Type*} [Group W] (S : Set W) (w : W) :
    CFSG.GroupActions.Exchange.wordLength S w = wordLength S w := by
  unfold CFSG.GroupActions.Exchange.wordLength wordLength
  congr 1
  ext n
  constructor
  · rintro ⟨l, hlen, hprod⟩
    refine ⟨l.map Subtype.val, fun x hx => ?_, by rw [List.length_map, hlen], hprod⟩
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact y.2
  · rintro ⟨L, hL, hlen, hprod⟩
    refine ⟨L.pmap Subtype.mk hL, by rw [List.length_pmap, hlen], ?_⟩
    rw [CFSG.GroupActions.Exchange.wordProd, List.map_pmap, List.pmap_eq_map, List.map_id', hprod]

variable {G : Type*} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}

namespace IsBNPair

theorem length_mul_le (h : IsBNPair B N S) {s : WeylGroup B N} (hs : s ∈ S) (w : WeylGroup B N) :
    wordLength S (s * w) ≤ wordLength S w + 1 :=
  wordLength_gen_mul_le h.bnCore.mul_self_eq_one hs (h.mem_closure w)

theorem length_le_mul (h : IsBNPair B N S) {s : WeylGroup B N} (hs : s ∈ S) (w : WeylGroup B N) :
    wordLength S w ≤ wordLength S (s * w) + 1 := by
  have := h.length_mul_le hs (s * w)
  rwa [← mul_assoc, h.mul_self_eq_one hs, one_mul] at this

theorem length_mul_le_right (h : IsBNPair B N S) {t : WeylGroup B N} (ht : t ∈ S)
    (w : WeylGroup B N) : wordLength S (w * t) ≤ wordLength S w + 1 :=
  wordLength_mul_gen_le h.bnCore.mul_self_eq_one ht (h.mem_closure w)

theorem length_inv_le (h : IsBNPair B N S) (w : WeylGroup B N) :
    wordLength S w⁻¹ ≤ wordLength S w := by
  obtain ⟨l, hl, hlen, hprod⟩ :=
    exists_list_length_eq_wordLength h.bnCore.mul_self_eq_one (h.mem_closure w)
  have hmap : l.map (fun x => x⁻¹) = l := by
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left fun x hx =>
      inv_eq_of_mul_eq_one_right (h.mul_self_eq_one (hl x hx))
  have hrev : l.reverse.prod = w⁻¹ := by
    rw [← hprod, List.prod_inv_reverse, hmap]
  have := wordLength_le (J := S) (l := l.reverse) (fun x hx => hl x (List.mem_reverse.1 hx))
  rwa [hrev, List.length_reverse, hlen] at this

theorem length_inv (h : IsBNPair B N S) (w : WeylGroup B N) :
    wordLength S w⁻¹ = wordLength S w :=
  le_antisymm (h.length_inv_le w) (by simpa using h.length_inv_le w⁻¹)

theorem inv_eq_self (h : IsBNPair B N S) {s : WeylGroup B N} (hs : s ∈ S) : s⁻¹ = s :=
  inv_eq_of_mul_eq_one_right (h.mul_self_eq_one hs)

theorem dc_mul_dc_of_lt (h : IsBNPair B N S) {s w : WeylGroup B N} (hs : s ∈ S)
    (hlt : wordLength S w < wordLength S (s * w)) : dc B N s * dc B N w = dc B N (s * w) :=
  (h.bnCore.mul_subset_of_lt hs (h.mem_closure w) hlt).antisymm (dc_subset_mul s w)

theorem dc_mul_dc_of_lt_right (h : IsBNPair B N S) {w t : WeylGroup B N} (ht : t ∈ S)
    (hlt : wordLength S w < wordLength S (w * t)) : dc B N w * dc B N t = dc B N (w * t) := by
  refine Set.Subset.antisymm ?_ (dc_subset_mul w t)
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
  have hlt' : wordLength S w⁻¹ < wordLength S (t * w⁻¹) := by
    rw [h.length_inv, ← h.inv_eq_self ht, ← mul_inv_rev, h.length_inv]
    exact hlt
  have hz' : z⁻¹ ∈ dc B N t := by simpa [h.inv_eq_self ht] using inv_mem_dc hz
  have hmem := (h.dc_mul_dc_of_lt ht hlt').subset (Set.mem_mul.2 ⟨z⁻¹, hz', y⁻¹, inv_mem_dc hy,
    rfl⟩)
  have h1 := inv_mem_dc hmem
  simp only [mul_inv_rev, inv_inv, h.inv_eq_self ht] at h1
  exact h1

theorem dc_mul_dc_of_gt (h : IsBNPair B N S) {s w : WeylGroup B N} (hs : s ∈ S)
    (hlt : wordLength S (s * w) < wordLength S w) :
    dc B N s * dc B N w = dc B N w ∪ dc B N (s * w) := by
  refine Set.Subset.antisymm ?_ (Set.union_subset ?_ (dc_subset_mul s w))
  · intro x hx
    rcases h.bnCore.mul_subset s hs w hx with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
  · have hsw : s * (s * w) = w := by rw [← mul_assoc, h.mul_self_eq_one hs, one_mul]
    have hlt' : wordLength S (s * w) < wordLength S (s * (s * w)) := by rwa [hsw]
    have e := h.dc_mul_dc_of_lt hs hlt'
    rw [hsw] at e
    calc dc B N w = dc B N s * dc B N (s * w) := e.symm
      _ ⊆ ((B : Set G) ∪ dc B N s) * dc B N (s * w) :=
          Set.mul_subset_mul_right Set.subset_union_right
      _ = dc B N s * dc B N w := by
          rw [← h.bnCore.mul_self hs, mul_assoc, e]

theorem dc_mul_dc_of_gt_right (h : IsBNPair B N S) {w t : WeylGroup B N} (ht : t ∈ S)
    (hlt : wordLength S (w * t) < wordLength S w) :
    dc B N w * dc B N t = dc B N w ∪ dc B N (w * t) := by
  refine Set.Subset.antisymm ?_ (Set.union_subset ?_ (dc_subset_mul w t))
  · intro x hx
    rcases h.bnCore.mul_subset_right ht w hx with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
  · have hwt : w * t * t = w := by rw [mul_assoc, h.mul_self_eq_one ht, mul_one]
    have hlt' : wordLength S (w * t) < wordLength S (w * t * t) := by rwa [hwt]
    have e := h.dc_mul_dc_of_lt_right ht hlt'
    rw [hwt] at e
    calc dc B N w = dc B N (w * t) * dc B N t := e.symm
      _ ⊆ dc B N (w * t) * ((B : Set G) ∪ dc B N t) :=
          Set.mul_subset_mul_left Set.subset_union_right
      _ = dc B N w * dc B N t := by
          rw [← h.bnCore.mul_self ht, ← mul_assoc, e]

theorem dc_mul_dc_subset_of_length_eq (h : IsBNPair B N S) {s x : WeylGroup B N} (hs : s ∈ S)
    {k : ℕ} (hxk : wordLength S x = k) (hsxk : wordLength S (s * x) = k)
    (ih : ∀ m < k, ∀ y : WeylGroup B N, ∀ r ∈ S, wordLength S y = m → wordLength S (r * y) ≠ m) :
    dc B N s * dc B N x ⊆ dc B N (s * x) := by
  have hJ1 := h.bnCore.mul_self_eq_one
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [wordLength_one] at hxk
    rw [mul_one, ← hxk] at hsxk
    exact h.ne_one hs ((wordLength_eq_zero_iff hJ1 (h.mem_closure s)).1 hsxk)
  obtain ⟨t, ht, hdesc⟩ := exists_right_descent hJ1 (h.mem_closure x) hx1
  set y := x * t with hy
  have hyt : y * t = x := by rw [hy, mul_assoc, hJ1 t ht, mul_one]
  have hylen : wordLength S y = k - 1 := by omega
  have hsy_ne := ih (k - 1) (by omega) y s hs hylen
  have h1 := h.length_mul_le hs y
  have h2 := h.length_mul_le_right ht (s * y)
  rw [mul_assoc, hyt] at h2
  have hsy : wordLength S (s * y) = k := by omega
  have e1 := h.dc_mul_dc_of_lt hs (show wordLength S y < wordLength S (s * y) by omega)
  have e2 := h.dc_mul_dc_of_lt_right ht (show wordLength S y < wordLength S (y * t) by
    rw [hyt]; omega)
  rw [hyt] at e2
  intro z hz
  have hz1 := h.bnCore.mul_subset s hs x hz
  have hz2 : z ∈ dc B N (s * y * t) ∪ dc B N (s * y) := by
    have : z ∈ dc B N (s * y) * dc B N t := by
      rw [← e1, mul_assoc, e2]
      exact hz
    exact h.bnCore.mul_subset_right ht (s * y) this
  rw [mul_assoc, hyt] at hz2
  rcases hz1 with hz1 | hz1
  · exact hz1
  · rcases hz2 with hz2 | hz2
    · exact hz2
    · exfalso
      have he : x = s * y := h.eq_of_mem_dc hz1 hz2
      have : s * x = y := by rw [he, ← mul_assoc, hJ1 s hs, one_mul]
      rw [this] at hsxk
      omega

theorem length_mul_ne (h : IsBNPair B N S) {s : WeylGroup B N} (hs : s ∈ S) (w : WeylGroup B N) :
    wordLength S (s * w) ≠ wordLength S w := by
  have hJ1 := h.bnCore.mul_self_eq_one
  suffices key : ∀ k : ℕ, ∀ w : WeylGroup B N, ∀ s ∈ S, wordLength S w = k →
      wordLength S (s * w) ≠ k from key _ w s hs rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro w s hs hlen heq
    have hsw : s * (s * w) = w := by rw [← mul_assoc, hJ1 s hs, one_mul]
    have hA := h.dc_mul_dc_subset_of_length_eq hs hlen heq ih
    have hB' := h.dc_mul_dc_subset_of_length_eq hs heq (by rw [hsw]; exact hlen) ih
    rw [hsw] at hB'
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (s * w)
    have hnsw : (n : G) ∈ dc B N (s * w) := hn ▸ coe_mem_dc n
    have hnw : (n : G) ∈ dc B N w := by
      have h3 : (n : G) ∈ dc B N s * dc B N w := dc_subset_mul s w hnsw
      have h4 : dc B N s * dc B N w ⊆ dc B N s * (dc B N s * dc B N w) := by
        rw [← mul_assoc, h.bnCore.mul_self hs]
        exact Set.mul_subset_mul_right Set.subset_union_right
      exact hB' (Set.mul_subset_mul_left hA (h4 h3))
    have he := h.eq_of_mem_dc hnsw hnw
    exact h.ne_one hs (by simpa using he)

theorem length_mul_eq_or (h : IsBNPair B N S) {s : WeylGroup B N} (hs : s ∈ S)
    (w : WeylGroup B N) :
    wordLength S (s * w) = wordLength S w + 1 ∨ wordLength S (s * w) + 1 = wordLength S w := by
  have h1 := h.length_mul_le hs w
  have h2 := h.length_le_mul hs w
  have h3 := h.length_mul_ne hs w
  omega

theorem length_take (h : IsBNPair B N S) {l : List (WeylGroup B N)} (hl : ∀ x ∈ l, x ∈ S)
    (hred : l.length = wordLength S l.prod) {j : ℕ} (hj : j ≤ l.length) :
    wordLength S (l.take j).prod = j := by
  have hJ1 := h.bnCore.mul_self_eq_one
  have hle1 : wordLength S (l.take j).prod ≤ j := by
    have := wordLength_le (J := S) (l := l.take j) (fun x hx => hl x (List.mem_of_mem_take hx))
    rwa [List.length_take, min_eq_left hj] at this
  have hle2 : wordLength S (l.drop j).prod ≤ l.length - j := by
    have := wordLength_le (J := S) (l := l.drop j) (fun x hx => hl x (List.mem_of_mem_drop hx))
    rwa [List.length_drop] at this
  have hmul := wordLength_mul_le hJ1 (h.mem_closure (l.take j).prod) (h.mem_closure (l.drop j).prod)
  rw [List.prod_take_mul_prod_drop] at hmul
  omega

theorem exchange (h : IsBNPair B N S) {s : WeylGroup B N} (hs : s ∈ S) {l : List (WeylGroup B N)}
    (hl : ∀ x ∈ l, x ∈ S) (hred : l.length = wordLength S l.prod)
    (hlt : wordLength S (s * l.prod) < wordLength S l.prod) :
    ∃ j < l.length, s * (l.take j).prod = (l.take (j + 1)).prod := by
  have hJ1 := h.bnCore.mul_self_eq_one
  have hne : l ≠ [] := by
    rintro rfl
    rw [List.prod_nil, wordLength_one] at hlt
    exact Nat.not_lt_zero _ hlt
  have hex : ∃ j, j < l.length ∧
      wordLength S (s * (l.take (j + 1)).prod) < wordLength S (l.take (j + 1)).prod := by
    refine ⟨l.length - 1, by
      have := List.length_pos_iff.2 hne
      omega, ?_⟩
    rw [Nat.sub_add_cancel (List.length_pos_iff.2 hne), List.take_length]
    exact hlt
  classical
  set j := Nat.find hex with hjdef
  obtain ⟨hjl, hjlt⟩ := Nat.find_spec hex
  have hmin : ∀ i < j, ¬ (i < l.length ∧
      wordLength S (s * (l.take (i + 1)).prod) < wordLength S (l.take (i + 1)).prod) :=
    fun i hi => Nat.find_min hex hi
  set u := (l.take j).prod with hu
  set t := l[j] with htdef
  have ht : t ∈ S := hl t (List.getElem_mem hjl)
  have hut : (l.take (j + 1)).prod = u * t := List.prod_take_succ l j hjl
  rw [hut] at hjlt
  have hulen : wordLength S u = j := h.length_take hl hred (by omega)
  have hutlen : wordLength S (u * t) = j + 1 := by
    rw [← hut]
    exact h.length_take hl hred (by omega)
  have hsu_ge : wordLength S u ≤ wordLength S (s * u) := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · omega
    · have := hmin (j - 1) (by omega)
      rw [Nat.sub_add_cancel hj0] at this
      push Not at this
      exact this (by omega)
  have hsu_ne := h.length_mul_ne hs u
  have hsu_le := h.length_mul_le hs u
  have hsulen : wordLength S (s * u) = j + 1 := by omega
  have hsut_ge := h.length_le_mul hs (u * t)
  have hsutlen : wordLength S (s * (u * t)) = j := by omega
  have e1 := h.dc_mul_dc_of_lt hs (show wordLength S u < wordLength S (s * u) by omega)
  have e2 := h.dc_mul_dc_of_lt_right ht (show wordLength S u < wordLength S (u * t) by omega)
  have e3 := h.dc_mul_dc_of_gt hs hjlt
  have e4 := h.dc_mul_dc_of_gt_right ht (show wordLength S (s * u * t) < wordLength S (s * u) by
    rw [mul_assoc]; omega)
  have key : dc B N (u * t) ∪ dc B N (s * (u * t)) = dc B N (s * u) ∪ dc B N (s * u * t) := by
    rw [← e3, ← e4, ← e1, ← e2, mul_assoc]
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (s * u)
  have hnsu : (n : G) ∈ dc B N (s * u) := hn ▸ coe_mem_dc n
  have hmem : (n : G) ∈ dc B N (u * t) ∪ dc B N (s * (u * t)) := by
    rw [key]
    exact Or.inl hnsu
  refine ⟨j, hjl, ?_⟩
  rw [hut]
  rcases hmem with h1 | h1
  · exact h.eq_of_mem_dc hnsu h1
  · exfalso
    have he : s * u = s * (u * t) := h.eq_of_mem_dc hnsu h1
    exact h.ne_one ht (left_eq_mul.1 (mul_left_cancel he))

theorem exchangeCondition (h : IsBNPair B N S) :
    CFSG.GroupActions.Exchange.ExchangeCondition S := by
  intro s l hred _ hle
  have hred' : (l.map Subtype.val).length = wordLength S (l.map Subtype.val).prod := by
    rw [List.length_map, ← exchange_wordLength_eq]
    exact hred
  have hlt : wordLength S ((s : WeylGroup B N) * (l.map Subtype.val).prod) <
      wordLength S (l.map Subtype.val).prod := by
    have hle' := hle
    rw [exchange_wordLength_eq, exchange_wordLength_eq] at hle'
    exact lt_of_le_of_ne hle' (h.length_mul_ne s.2 _)
  obtain ⟨j, hj, hjeq⟩ := h.exchange s.2 (fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact y.2) hred' hlt
  refine ⟨j, by rwa [List.length_map] at hj, ?_⟩
  simpa [CFSG.GroupActions.Exchange.wordProd, List.map_take] using hjeq

theorem exists_coxeterSystem (h : IsBNPair B N S) :
    ∃ cs : CoxeterSystem (orderMatrix h.orderOf_eq_two) (WeylGroup B N),
      ∀ s : S, cs.simple s = s :=
  CFSG.GroupTheory.TitsSystem.exists_coxeterSystem h.orderOf_eq_two h.closure_eq
    h.exchangeCondition

end IsBNPair

end CFSG.GroupTheory.TitsSystem
