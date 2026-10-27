module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.BalanceSC

open Equiv Equiv.Perm Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def IsWit (e w : Perm α) : Prop := (w * e * w⁻¹) * e ≠ e * (w * e * w⁻¹)

@[expose] def blk (e : Perm α) (x : α) : Finset α := univ.filter (e.SameCycle x)

@[expose] def cycParts (e : Perm α) : Finset (Finset α) := e.support.image (blk e)

theorem mem_blk {e : Perm α} {x y : α} : y ∈ blk e x ↔ e.SameCycle x y := by
  simp [blk]

theorem blk_eq_of_sameCycle {e : Perm α} {x y : α} (h : e.SameCycle x y) : blk e x = blk e y := by
  ext z
  simp only [mem_blk]
  exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

theorem sameCycle_apply_of_commute {f σ : Perm α} (h : Commute f σ) {x y : α}
    (hxy : f.SameCycle x y) : f.SameCycle (σ x) (σ y) := by
  obtain ⟨i, rfl⟩ := hxy
  exact ⟨i, by rw [← mul_apply, (h.zpow_left i).eq, mul_apply]⟩

theorem blk_conj (e w : Perm α) (x : α) :
    blk (w * e * w⁻¹) (w x) = (blk e x).map w.toEmbedding := by
  ext z
  simp only [mem_blk, mem_map, Equiv.toEmbedding_apply, sameCycle_conj]
  constructor
  · intro h
    exact ⟨w⁻¹ z, by simpa using h, by simp⟩
  · rintro ⟨u, hu, rfl⟩
    simpa using hu

theorem card_blk {e : Perm α} {r : ℕ} (hr : r.Prime) (her : e ^ r = 1) {x : α}
    (hx : x ∈ e.support) : (blk e x).card = r := by
  have hbs : blk e x = (e.cycleOf x).support := by
    ext y
    rw [mem_blk, mem_support_cycleOf_iff]
    exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩
  have hcyc : (e.cycleOf x).IsCycle := isCycle_cycleOf e (mem_support.1 hx)
  have hdvd : (blk e x).card ∣ r := by
    rw [hbs, ← hcyc.orderOf]
    exact (orderOf_cycleOf_dvd_orderOf e x).trans (orderOf_dvd_of_pow_eq_one her)
  rcases hr.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · rw [hbs] at h1
    exact absurd h1 (card_support_ne_one _)
  · exact h1

theorem card_cycParts_conj (e w : Perm α) : (cycParts (w * e * w⁻¹)).card = (cycParts e).card := by
  have : cycParts (w * e * w⁻¹) = (cycParts e).image (fun B => B.map w.toEmbedding) := by
    simp only [cycParts, support_conj, image_image]
    rw [map_eq_image, image_image]
    congr 1
    funext x
    exact blk_conj e w x
  rw [this, card_image_of_injective _ (map_injective _)]

theorem pow_apply_mem_support_of_commute {e f : Perm α} (hfe : Commute f e) {y : α}
    (hy : y ∈ f.support) (j : ℕ) : (e ^ j) y ∈ f.support := by
  rw [mem_support] at hy ⊢
  intro h
  apply hy
  have : (e ^ j) (f y) = (e ^ j) y := by rw [← mul_apply, ← (hfe.pow_right j).eq, mul_apply, h]
  exact (e ^ j).injective this

theorem pow_mod_apply {e : Perm α} {r : ℕ} (her : e ^ r = 1) (m : ℕ) (z : α) :
    (e ^ (m % r)) z = (e ^ m) z := by
  conv_rhs => rw [← Nat.div_add_mod m r, pow_add, pow_mul, her, one_pow, one_mul]

theorem mapsTo_blk_of_shift {e f : Perm α} {r : ℕ} (hr : r.Prime) (her : e ^ r = 1)
    (hfe : Commute f e) {y : α} {d : ℕ} (hd0 : 0 < d) (hdr : d < r)
    (hd : f.SameCycle y ((e ^ d) y)) : ∀ z ∈ blk f y, e z ∈ blk f y := by
  have hfp : ∀ j : ℕ, Commute f (e ^ j) := fun j => hfe.pow_right j
  have hmul : ∀ m : ℕ, f.SameCycle y ((e ^ (d * m)) y) := by
    intro m
    induction m with
    | zero => rw [mul_zero, pow_zero, one_apply]
    | succ m ih =>
      have h2 := sameCycle_apply_of_commute (hfp (d * m)) hd
      rw [← mul_apply (e ^ (d * m)) (e ^ d), ← pow_add, ← Nat.mul_succ] at h2
      exact ih.trans h2
  have hcop : Nat.Coprime d r :=
    (hr.coprime_iff_not_dvd.2 fun hdv => by have := Nat.le_of_dvd hd0 hdv; omega).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
  have hey : f.SameCycle y (e y) := by
    have := hmul m
    rwa [← pow_mod_apply her, hm, pow_one] at this
  intro z hz
  exact mem_blk.2 (hey.trans (sameCycle_apply_of_commute hfe (mem_blk.1 hz)))

theorem shift_of_sameCycle {e f : Perm α} {r : ℕ} (her : e ^ r = 1) (hfe : Commute f e) {y : α}
    {i j : ℕ} (hi : i < r) (hj : j < r) (hij : i ≠ j)
    (h : f.SameCycle ((e ^ i) y) ((e ^ j) y)) : ∃ d, 0 < d ∧ d < r ∧ f.SameCycle y ((e ^ d) y) := by
  have hpair : ∀ a b : ℕ, a < r → b < r → a < b → f.SameCycle ((e ^ a) y) ((e ^ b) y) →
      ∃ d, 0 < d ∧ d < r ∧ f.SameCycle y ((e ^ d) y) := by
    intro a b ha hb hab h
    refine ⟨b - a, by omega, by omega, ?_⟩
    have h' := sameCycle_apply_of_commute (hfe.pow_right (r - a)) h
    have e1 : (e ^ (r - a)) ((e ^ a) y) = y := by
      rw [← mul_apply, ← pow_add, Nat.sub_add_cancel ha.le, her, one_apply]
    have e2 : (e ^ (r - a)) ((e ^ b) y) = (e ^ (b - a)) y := by
      rw [← mul_apply, ← pow_add, show r - a + b = r + (b - a) by omega, pow_add, her, one_mul]
    rwa [e1, e2] at h'
  rcases lt_or_gt_of_ne hij with h' | h'
  · exact hpair i j hi hj h' h
  · exact hpair j i hj hi h' h.symm

theorem map_mem_cycParts_of_mapsTo {e w : Perm α} {r : ℕ} (hr : r.Prime) (her : e ^ r = 1)
    {x : α} (hx : x ∈ e.support)
    (hinv : ∀ z ∈ blk (w * e * w⁻¹) (w x), e z ∈ blk (w * e * w⁻¹) (w x))
    (hmeet : ∃ u ∈ blk e x, w u ∈ e.support) : (blk e x).map w.toEmbedding ∈ cycParts e := by
  set f := w * e * w⁻¹
  have hO : blk f (w x) = (blk e x).map w.toEmbedding := blk_conj e w x
  have hinvp : ∀ k : ℕ, ∀ z ∈ blk f (w x), (e ^ k) z ∈ blk f (w x) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro z hz
      rw [pow_succ', mul_apply]
      exact hinv _ (ih z hz)
  obtain ⟨u, hu, hwu⟩ := hmeet
  have hwuO : w u ∈ blk f (w x) := by rw [hO]; exact mem_map_of_mem _ hu
  have hsub : blk e (w u) ⊆ blk f (w x) := by
    intro z hz
    obtain ⟨k, -, rfl⟩ := (mem_blk.1 hz).exists_pow_eq'
    exact hinvp k _ hwuO
  have hcard : (blk f (w x)).card ≤ (blk e (w u)).card := by
    rw [hO, card_map, card_blk hr her hx, card_blk hr her hwu]
  rw [← hO, ← eq_of_subset_of_card_le hsub hcard]
  exact mem_image_of_mem _ hwu

theorem isWit_of_sc {e w : Perm α} {r : ℕ} (hr : r.Prime) (her : e ^ r = 1)
    (hk : (cycParts e).card < r) {x : α} (hx : x ∈ e.support)
    (hnot : (blk e x).map w.toEmbedding ∉ cycParts e)
    (hmeet : ∃ u ∈ blk e x, w u ∈ e.support) : IsWit e w := by
  intro hc
  set f := w * e * w⁻¹ with hf
  have hfe : Commute f e := hc
  have hyf : w x ∈ f.support := by
    rw [hf, support_conj]
    exact mem_map_of_mem _ hx
  obtain ⟨i, hi, j, hj, hij, hne⟩ : ∃ i < r, ∃ j < r,
      blk f ((e ^ i) (w x)) = blk f ((e ^ j) (w x)) ∧ i ≠ j := by
    by_contra hcon
    have hle := card_le_card_of_injOn (fun j => blk f ((e ^ j) (w x))) (s := range r)
      (t := cycParts f) (fun j _ => mem_image_of_mem _ (pow_apply_mem_support_of_commute hfe hyf j))
      fun i hi j hj h => by_contra fun hne => hcon ⟨i, mem_range.1 hi, j, mem_range.1 hj, h, hne⟩
    rw [card_range, card_cycParts_conj] at hle
    omega
  have hsame : f.SameCycle ((e ^ i) (w x)) ((e ^ j) (w x)) := by
    have : (e ^ j) (w x) ∈ blk f ((e ^ i) (w x)) := by
      rw [hij]
      exact mem_blk.2 (SameCycle.refl _ _)
    exact mem_blk.1 this
  obtain ⟨d, hd0, hdr, hd⟩ := shift_of_sameCycle her hfe hi hj hne hsame
  exact hnot (map_mem_cycParts_of_mapsTo hr her hx (mapsTo_blk_of_shift hr her hfe hd0 hdr hd)
    hmeet)

theorem isWit_of_sc_orth {e w : Perm α} {r : ℕ} (hr : r.Prime) (her : e ^ r = 1)
    (hk : (cycParts e).card ≤ r) {x : α} (hx : x ∈ e.support)
    (hnot : (blk e x).map w.toEmbedding ∉ cycParts e)
    (hmeet : ∃ u ∈ blk e x, w u ∈ e.support)
    (horth : ∃ x' ∈ e.support, ∃ y' ∈ e.support,
      ((blk e x').map w.toEmbedding ∩ blk e y').card ≠ 1) : IsWit e w := by
  intro hc
  set f := w * e * w⁻¹ with hf
  have hfe : Commute f e := hc
  set y := w x with hy
  have hsuppf : f.support = e.support.map w.toEmbedding := by rw [hf, support_conj]
  have hyf : y ∈ f.support := by rw [hsuppf]; exact mem_map_of_mem _ hx
  have hjf : ∀ j : ℕ, (e ^ j) y ∈ f.support := pow_apply_mem_support_of_commute hfe hyf
  by_cases hsh : ∃ d, 0 < d ∧ d < r ∧ f.SameCycle y ((e ^ d) y)
  · obtain ⟨d, hd0, hdr, hd⟩ := hsh
    exact hnot (map_mem_cycParts_of_mapsTo hr her hx (mapsTo_blk_of_shift hr her hfe hd0 hdr hd)
      hmeet)
  set g : ℕ → Finset α := fun j => blk f ((e ^ j) y) with hg
  have hginj : ∀ i < r, ∀ j < r, g i = g j → i = j := by
    intro i hi j hj h
    by_contra hij
    have : (e ^ j) y ∈ g i := by rw [h]; exact mem_blk.2 (SameCycle.refl _ _)
    exact hsh (shift_of_sameCycle her hfe hi hj hij (mem_blk.1 this))
  have himg : (range r).image g = cycParts f := by
    refine eq_of_subset_of_card_le (fun B hB => ?_) ?_
    · obtain ⟨j, -, rfl⟩ := mem_image.1 hB
      exact mem_image_of_mem _ (hjf j)
    · rw [card_cycParts_conj, card_image_of_injOn (fun i hi j hj h =>
        hginj i (mem_range.1 hi) j (mem_range.1 hj) h), card_range]
      exact hk
  have hcyc : ∀ z ∈ f.support, ∃ j < r, z ∈ g j := by
    intro z hz
    have hm : blk f z ∈ cycParts f := mem_image_of_mem _ hz
    rw [← himg] at hm
    obtain ⟨j, hj, hgj⟩ := mem_image.1 hm
    refine ⟨j, mem_range.1 hj, ?_⟩
    rw [hgj]
    exact mem_blk.2 (SameCycle.refl _ _)
  have hshift : ∀ j i : ℕ, ∀ z ∈ g j, (e ^ i) z ∈ g ((j + i) % r) := by
    intro j i z hz
    have h := sameCycle_apply_of_commute (hfe.pow_right i) (mem_blk.1 hz)
    rw [← mul_apply, ← pow_add, ← pow_mod_apply her, add_comm i j] at h
    exact mem_blk.2 h
  have hr2 : 2 ≤ r := hr.two_le
  have hsub : f.support ⊆ e.support := by
    intro z hz
    obtain ⟨j, hj, hzj⟩ := hcyc z hz
    rw [mem_support]
    intro hez
    have h1 := hshift j 1 z hzj
    rw [pow_one, hez] at h1
    have h2 : g j = g ((j + 1) % r) := (blk_eq_of_sameCycle (mem_blk.1 hzj)).trans
      (blk_eq_of_sameCycle (mem_blk.1 h1)).symm
    have h3 := hginj j hj _ (Nat.mod_lt _ hr.pos) h2
    rcases Nat.lt_or_ge (j + 1) r with h4 | h4
    · rw [Nat.mod_eq_of_lt h4] at h3
      omega
    · rw [show j + 1 = r by omega, Nat.mod_self] at h3
      omega
  have hseq : f.support = e.support :=
    eq_of_subset_of_card_le hsub (by rw [hsuppf, card_map])
  obtain ⟨x', hx', y', hy', hne⟩ := horth
  apply hne
  obtain ⟨j, hj, hj'⟩ : ∃ j < r, (blk e x').map w.toEmbedding = g j := by
    have hwx' : w x' ∈ f.support := by rw [hsuppf]; exact mem_map_of_mem _ hx'
    have hm : blk f (w x') ∈ cycParts f := mem_image_of_mem _ hwx'
    rw [← himg] at hm
    obtain ⟨j, hj, hgj⟩ := mem_image.1 hm
    exact ⟨j, mem_range.1 hj, (blk_conj e w x').symm.trans hgj.symm⟩
  obtain ⟨j', hj'r, hy'g⟩ := hcyc y' (hseq ▸ hy')
  have hord : orderOf e = r := by
    have : Fact r.Prime := ⟨hr⟩
    exact orderOf_eq_prime her fun h => by rw [h] at hx; simp at hx
  have hmod : ∀ a b : ℕ, a < r → b < r → (a + b) % r = if a + b < r then a + b else a + b - r := by
    intro a b ha hb
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  set i₀ := (j + r - j') % r with hi₀
  have hi₀r : i₀ < r := Nat.mod_lt _ hr.pos
  rw [hj', card_eq_one]
  refine ⟨(e ^ i₀) y', ext fun z => ?_⟩
  rw [mem_inter, mem_singleton]
  constructor
  · rintro ⟨hzg, hz⟩
    obtain ⟨i, hi, rfl⟩ := (mem_blk.1 hz).exists_pow_eq'
    rw [hord] at hi
    have h1 := hshift j' i y' hy'g
    have h2 : g j = g ((j' + i) % r) := (blk_eq_of_sameCycle (mem_blk.1 hzg)).trans
      (blk_eq_of_sameCycle (mem_blk.1 h1)).symm
    have h3 := hginj j hj _ (Nat.mod_lt _ hr.pos) h2
    have hii : i = i₀ := by
      rw [hi₀]
      rw [hmod j' i hj'r hi] at h3
      have h5 : j + r - j' = if j + r - j' < r then j + r - j' else (j + r - j' - r) + r := by
        split_ifs <;> omega
      split_ifs at h3 with h6
      · rw [show j + r - j' = i + r by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      · rw [show j + r - j' = i by omega, Nat.mod_eq_of_lt hi]
    rw [hii]
  · rintro rfl
    refine ⟨?_, mem_blk.2 (sameCycle_pow_right.2 (SameCycle.refl _ _))⟩
    have h1 := hshift j' i₀ y' hy'g
    have h2 : (j' + i₀) % r = j := by
      rw [hi₀, Nat.add_mod_mod, show j' + (j + r - j') = j + r by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hj]
    rwa [h2] at h1

theorem mem_zpowers_of_commute_fullCycle {e g : Perm α} (hc : e.IsCycle) (hs : e.support = univ)
    (h : Commute g e) : g ∈ Subgroup.zpowers e := by
  have hall : ∀ z : α, e z ≠ z := fun z => mem_support.1 (hs ▸ mem_univ z)
  obtain ⟨a, -, -⟩ := id hc
  obtain ⟨i, hi⟩ := hc.sameCycle (hall a) (hall (g a))
  refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
  ext z
  obtain ⟨j, rfl⟩ := hc.sameCycle (hall a) (hall z)
  have hg : g ((e ^ j) a) = (e ^ j) (g a) := by rw [← mul_apply, (h.zpow_right j).eq, mul_apply]
  rw [hg, ← hi, ← mul_apply, ← mul_apply, ← zpow_add, ← zpow_add, add_comm]

theorem balance_of_small_bad {e : Perm α} (Q : Subgroup (Perm α)) (B : Finset (Perm α))
    (hB : ∀ w ∈ Q, ¬ IsWit e w → w ∈ B) (hcard : 2 * B.card < Nat.card Q) :
    ∃ w₁ ∈ Q, ∃ w₂ ∈ Q, IsWit e w₁ ∧ IsWit e w₂ ∧ IsWit e (w₁ * w₂) := by
  classical
  set QF : Finset (Perm α) := univ.filter (· ∈ Q) with hQF
  have hQ : QF.card = Nat.card Q := by
    rw [hQF, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hwit : ∀ w ∈ Q, w ∉ B → IsWit e w := fun w hw hwB => by_contra fun h => hwB (hB w hw h)
  obtain ⟨w₁, hw₁, hw₁B⟩ := exists_mem_notMem_of_card_lt_card (s := B) (t := QF) (by omega)
  have hw₁Q : w₁ ∈ Q := (mem_filter.1 hw₁).2
  have hB' : (B ∪ B.image (w₁⁻¹ * ·)).card < QF.card := by
    have := card_union_le B (B.image (w₁⁻¹ * ·))
    have := card_image_le (s := B) (f := (w₁⁻¹ * ·))
    omega
  obtain ⟨w₂, hw₂, hw₂B⟩ := exists_mem_notMem_of_card_lt_card hB'
  have hw₂Q : w₂ ∈ Q := (mem_filter.1 hw₂).2
  refine ⟨w₁, hw₁Q, w₂, hw₂Q, hwit w₁ hw₁Q hw₁B,
    hwit w₂ hw₂Q (fun h => hw₂B (mem_union_left _ h)), hwit _ (Q.mul_mem hw₁Q hw₂Q) ?_⟩
  intro h
  apply hw₂B
  exact mem_union_right _ (mem_image.2 ⟨w₁ * w₂, h, by group⟩)

theorem balance_of_fullCycle {e : Perm α} (hc : e.IsCycle) (hs : e.support = univ)
    (Q : Subgroup (Perm α)) (hcop : (Nat.card Q).Coprime (Fintype.card α))
    (hQ : 2 * Fintype.card α < Nat.card Q) :
    ∃ w₁ ∈ Q, ∃ w₂ ∈ Q, IsWit e w₁ ∧ IsWit e w₂ ∧ IsWit e (w₁ * w₂) := by
  classical
  have hord : orderOf e = Fintype.card α := by rw [hc.orderOf, hs, card_univ]
  set Z := (range (orderOf e)).image (e ^ ·) with hZ
  set B := (univ.filter (fun w => w ∈ Q ∧ ¬ IsWit e w)) with hBdef
  have hmapsto : ∀ w ∈ B, w * e * w⁻¹ ∈ Z := by
    intro w hw
    have hw' : Commute (w * e * w⁻¹) e := not_not.1 (mem_filter.1 hw).2.2
    exact mem_zpowers_iff_mem_range_orderOf.1 (mem_zpowers_of_commute_fullCycle hc hs hw')
  have hinj : Set.InjOn (fun w => w * e * w⁻¹) (B : Set (Perm α)) := by
    intro w hw w' hw' h'
    have h : w * e * w⁻¹ = w' * e * w'⁻¹ := h'
    simp only [hBdef, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
    set u := w'⁻¹ * w
    have hu : Commute u e := by
      change w'⁻¹ * w * e = e * (w'⁻¹ * w)
      have : w = w' * e * w'⁻¹ * w * e⁻¹ := by rw [← h]; group
      calc w'⁻¹ * w * e = w'⁻¹ * (w' * e * w'⁻¹ * w * e⁻¹) * e := by rw [← this]
        _ = e * (w'⁻¹ * w) := by group
    have huQ : u ∈ Q := Q.mul_mem (Q.inv_mem hw'.1) hw.1
    obtain ⟨k, -, hk⟩ := mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1
      (mem_zpowers_of_commute_fullCycle hc hs hu))
    have h1 : orderOf u ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard Q huQ
    have h2 : orderOf u ∣ Fintype.card α := by
      rw [← hk, ← hord]
      exact orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one,
        one_pow])
    have h3 : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    rw [orderOf_eq_one_iff] at h3
    calc w = w' * u := by rw [show u = w'⁻¹ * w from rfl]; group
      _ = w' := by rw [h3, mul_one]
  have hBcard : B.card ≤ Fintype.card α := by
    calc B.card ≤ Z.card := card_le_card_of_injOn _ hmapsto hinj
      _ ≤ (range (orderOf e)).card := card_image_le
      _ = Fintype.card α := by rw [card_range, hord]
  refine balance_of_small_bad Q B (fun w hw hn => ?_) (by omega)
  simp [hBdef, hw, hn]

theorem balance_of_prime_card {e : Perm α} (hp : (Fintype.card α).Prime) (he : e ≠ 1)
    (hep : e ^ Fintype.card α = 1) (Q : Subgroup (Perm α))
    (hcop : (Nat.card Q).Coprime (Fintype.card α)) (hQ : 2 * Fintype.card α < Nat.card Q) :
    ∃ w₁ ∈ Q, ∃ w₂ ∈ Q, IsWit e w₁ ∧ IsWit e w₂ ∧ IsWit e (w₁ * w₂) := by
  have : Fact (Fintype.card α).Prime := ⟨hp⟩
  have hord : orderOf e = Fintype.card α := orderOf_eq_prime hep he
  have hc : e.IsCycle := by
    refine isCycle_of_prime_order (hord ▸ hp) ?_
    rw [hord]
    have := card_le_univ e.support
    have := hp.pos
    omega
  have hs : e.support = univ := by
    apply eq_univ_of_card
    rw [← hc.orderOf, hord]
  exact balance_of_fullCycle hc hs Q hcop hQ

end CFSG.KC.BalanceSC
