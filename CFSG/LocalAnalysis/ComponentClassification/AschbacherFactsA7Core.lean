module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsA7
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open Equiv

theorem alternating_le_of_transitive_of_threeCycle (H : Subgroup (Perm (Fin 7))) (b : Fin 7)
    (htr : ∀ z, ∃ h ∈ H, h b = z) {g : Perm (Fin 7)} (hg3 : g.IsThreeCycle) (hg : g ∈ H) :
    alternatingGroup (Fin 7) ≤ H := by
  have htr' : MulAction.IsPretransitive H (Fin 7) := by
    constructor
    intro x y
    obtain ⟨h₁, hh₁, rfl⟩ := htr x
    obtain ⟨h₂, hh₂, rfl⟩ := htr y
    refine ⟨⟨h₂ * h₁⁻¹, H.mul_mem hh₂ (H.inv_mem hh₁)⟩, ?_⟩
    change (h₂ * h₁⁻¹) (h₁ b) = h₂ b
    simp
  have hprim : MulAction.IsPreprimitive H (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
                                               norm_num)
  exact Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hg3 hg

theorem commute_swap_of_fixed {f : Perm (Fin 7)} {x y : Fin 7} (hx : f x = x) (hy : f y = y) :
    f * swap x y = swap x y * f := by
  rw [mul_swap_eq_swap_mul, hx, hy]

theorem commute_threeCycle_of_fixed {f : Perm (Fin 7)} {a b c : Fin 7} (ha : f a = a)
    (hb : f b = b) (hc : f c = c) : f * (swap a b * swap a c) = swap a b * swap a c * f := by
  rw [← mul_assoc, commute_swap_of_fixed ha hb, mul_assoc, commute_swap_of_fixed ha hc,
    mul_assoc]

theorem threeCycle_mem_alternating {g : Perm (Fin 7)} (hg : g.IsThreeCycle) :
    g ∈ alternatingGroup (Fin 7) :=
  Perm.mem_alternatingGroup.mpr hg.sign

theorem odd_orderOf_threeCycle {g : Perm (Fin 7)} (hg : g.IsThreeCycle) : Odd (orderOf g) := by
  rw [hg.orderOf]
  decide

theorem a7_core_swap {a b : Fin 7} (hab : a ≠ b) (y : Perm (Fin 7)) (hya : y a = a)
    (hyb : y b = b) (hy2 : y ^ 2 = 1) (H : Subgroup (Perm (Fin 7)))
    (hP1x : ∀ x ∈ alternatingGroup (Fin 7), swap a b * x = x * swap a b → Odd (orderOf x) →
      x ∈ H)
    (hP1y : ∀ x ∈ alternatingGroup (Fin 7), y * x = x * y → Odd (orderOf x) → x ∈ H) :
    alternatingGroup (Fin 7) ≤ H := by
  classical
  obtain ⟨c, hca, hcb, hyc⟩ : ∃ c, c ≠ a ∧ c ≠ b ∧ y c = c := by
    have hsupp : y.support ⊆ Finset.univ \ {a, b} := by
      intro z hz
      rw [Perm.mem_support] at hz
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and, not_or]
      exact ⟨fun h => hz (h ▸ hya), fun h => hz (h ▸ hyb)⟩
    have heven : Even y.support.card := by
      rw [← Perm.sum_cycleType]
      by_cases hy1 : y = 1
      · simp [hy1]
      · have hord : orderOf y = 2 := orderOf_eq_prime hy2 hy1
        obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := y) (by rw [hord]; exact Nat.prime_two)
        rw [hn, hord, Multiset.sum_replicate, smul_eq_mul]
        exact ⟨n + 1, by ring⟩
    have hcard : (Finset.univ \ {a, b} : Finset (Fin 7)).card = 5 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, Finset.card_pair hab]
    have hle := Finset.card_le_card hsupp
    rw [hcard] at hle
    have hlt : y.support.card < (Finset.univ \ {a, b} : Finset (Fin 7)).card := by
      rw [hcard]
      obtain ⟨k, hk⟩ := heven
      omega
    obtain ⟨c, hc, hcs⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] at hc
    exact ⟨c, hc.1, hc.2, Perm.notMem_support.mp hcs⟩
  have hg3 : (swap a b * swap a c).IsThreeCycle :=
    Perm.isThreeCycle_swap_mul_swap_same hab (Ne.symm hca) (Ne.symm hcb)
  have hgH : swap a b * swap a c ∈ H :=
    hP1y _ (threeCycle_mem_alternating hg3) (commute_threeCycle_of_fixed hya hyb hyc)
      (odd_orderOf_threeCycle hg3)
  have hΔ : ∀ d e : Fin 7, d ≠ a → d ≠ b → e ≠ a → e ≠ b → d ≠ c → e ≠ c → d ≠ e →
      swap c e * swap c d ∈ H := by
    intro d e hda hdb hea heb hdc hec hde
    have h3 : (swap c e * swap c d).IsThreeCycle :=
      Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hec) (Ne.symm hdc) (Ne.symm hde)
    apply hP1x _ (threeCycle_mem_alternating h3) _ (odd_orderOf_threeCycle h3)
    have hfix : ∀ z, z ≠ a → z ≠ b → swap a b z = z := fun z h1 h2 =>
      swap_apply_of_ne_of_ne h1 h2
    exact commute_threeCycle_of_fixed (hfix c hca hcb) (hfix e hea heb) (hfix d hda hdb)
  refine alternating_le_of_transitive_of_threeCycle H c ?_ hg3 hgH
  intro z
  by_cases hzc : z = c
  · exact ⟨1, H.one_mem, by rw [hzc]; rfl⟩
  by_cases hza : z = a
  · refine ⟨(swap a b * swap a c) ^ 2, H.pow_mem hgH 2, ?_⟩
    rw [hza, pow_two]
    simp only [Perm.mul_apply]
    rw [swap_apply_right, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hcb),
      swap_apply_right]
  by_cases hzb : z = b
  · refine ⟨swap a b * swap a c, hgH, ?_⟩
    rw [hzb, Perm.mul_apply, swap_apply_right, swap_apply_left]
  obtain ⟨e, hea, heb, hec, hez⟩ : ∃ e : Fin 7, e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ z := by
    have hlt : ({a, b, c, z} : Finset (Fin 7)).card < (Finset.univ : Finset (Fin 7)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have := Finset.card_le_four (a := a) (b := b) (c := c) (d := z)
      omega
    obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    exact ⟨e, he.1, he.2.1, he.2.2.1, he.2.2.2⟩
  refine ⟨swap c e * swap c z, hΔ z e hza hzb hea heb hzc hec (Ne.symm hez), ?_⟩
  rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hzc (Ne.symm hez)]

theorem involution_cycleType {w : Perm (Fin 7)} (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) :
    w.cycleType = Multiset.replicate 1 2 ∨ w.cycleType = Multiset.replicate 2 2 ∨
      w.cycleType = Multiset.replicate 3 2 := by
  have hord : orderOf w = 2 := orderOf_eq_prime hw2 hw1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := w) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hn
  have hsum : (n + 1) * 2 ≤ 7 := by
    have h1 := Perm.sum_cycleType w
    rw [hn, Multiset.sum_replicate, smul_eq_mul] at h1
    rw [h1]
    exact (Finset.card_le_univ _).trans (by simp)
  have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases this with rfl | rfl | rfl
  · exact Or.inl hn
  · exact Or.inr (Or.inl hn)
  · exact Or.inr (Or.inr hn)

theorem sign_of_cycleType_replicate {w : Perm (Fin 7)} {k : ℕ}
    (h : w.cycleType = Multiset.replicate k 2) : Perm.sign w = (-1) ^ (k * 2 + k) := by
  rw [Perm.sign_of_cycleType, h, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]

theorem card_support_of_even_involution {w : Perm (Fin 7)} (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1)
    (hw : Perm.sign w = 1) : w.support.card = 4 := by
  rw [← Perm.sum_cycleType]
  rcases involution_cycleType hw2 hw1 with h | h | h
  · rw [sign_of_cycleType_replicate h] at hw
    exact absurd hw (by decide)
  · rw [h, Multiset.sum_replicate, smul_eq_mul]
  · rw [sign_of_cycleType_replicate h] at hw
    exact absurd hw (by decide)

theorem sq_mul_eq_one_of_commute {G : Type*} [Group G] {x w : G} (hx2 : x ^ 2 = 1)
    (hw2 : w ^ 2 = 1) (hxw : x * w = w * x) : (x * w) ^ 2 = 1 := by
  calc (x * w) ^ 2 = x * (w * x) * w := by rw [pow_two]; group
    _ = x * (x * w) * w := by rw [hxw]
    _ = x ^ 2 * w ^ 2 := by simp only [pow_two, mul_assoc]
    _ = 1 := by rw [hx2, hw2, one_mul]

theorem conj_apply_eq_iff {π x₀ : Perm (Fin 7)} {y : Fin 7} :
    (π * x₀ * π⁻¹) y = y ↔ x₀ (π⁻¹ y) = π⁻¹ y := by
  rw [Perm.mul_apply, Perm.mul_apply]
  exact Perm.eq_inv_iff_eq.symm

theorem fixed_triple_swap (i : Fin 7) (h : (swap 0 1 * swap 2 3 * swap 4 5 : Perm (Fin 7)) i = i) :
    i = 6 := by
  revert i
  decide

theorem triple_swap_centralizer_data :
    ∃ t₁ t₂ : Perm (Fin 7), t₁ ^ 3 = 1 ∧ t₁ ≠ 1 ∧ t₂ ^ 3 = 1 ∧ t₂ ≠ 1 ∧
      Perm.sign t₁ = 1 ∧ Perm.sign t₂ = 1 ∧
      t₁ * (swap 0 1 * swap 2 3 * swap 4 5) = swap 0 1 * swap 2 3 * swap 4 5 * t₁ ∧
      t₂ * (swap 0 1 * swap 2 3 * swap 4 5) = swap 0 1 * swap 2 3 * swap 4 5 * t₂ ∧
      ∀ i : Fin 7, i ≠ 6 → i = 0 ∨ i = t₁ 0 ∨ i = (t₁ * t₁) 0 ∨ i = (t₂ * t₁) 0 ∨
        i = (t₂ * (t₁ * t₁)) 0 ∨ i = (t₁ * (t₂ * (t₁ * t₁))) 0 := by
  refine ⟨swap 0 4 * swap 0 2 * (swap 1 5 * swap 1 3),
    swap 0 5 * swap 0 2 * (swap 1 4 * swap 1 3), ?_⟩
  decide

theorem a7_core_triple (π : Perm (Fin 7)) {x w : Perm (Fin 7)}
    (hπ : π * (swap 0 1 * swap 2 3 * swap 4 5) * π⁻¹ = x) (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1)
    (hw : Perm.sign w = 1) (hxw : x * w = w * x) (H : Subgroup (Perm (Fin 7)))
    (hP1x : ∀ g ∈ alternatingGroup (Fin 7), x * g = g * x → Odd (orderOf g) → g ∈ H)
    (hP1w : ∀ g ∈ alternatingGroup (Fin 7), w * g = g * w → Odd (orderOf g) → g ∈ H) :
    alternatingGroup (Fin 7) ≤ H := by
  classical
  obtain ⟨t₁, t₂, ht₁3, ht₁1, ht₂3, ht₂1, ht₁s, ht₂s, ht₁x, ht₂x, horb⟩ :=
    triple_swap_centralizer_data
  have hconjH : ∀ t : Perm (Fin 7), t ^ 3 = 1 → t ≠ 1 → Perm.sign t = 1 →
      t * (swap 0 1 * swap 2 3 * swap 4 5) = swap 0 1 * swap 2 3 * swap 4 5 * t →
      π * t * π⁻¹ ∈ H := by
    intro t ht3 ht1 hts htx
    apply hP1x
    · exact (alternatingGroup.normal (α := Fin 7)).conj_mem t
        (Perm.mem_alternatingGroup.mpr hts) π
    · rw [← hπ]
      calc π * (swap 0 1 * swap 2 3 * swap 4 5) * π⁻¹ * (π * t * π⁻¹)
          = π * ((swap 0 1 * swap 2 3 * swap 4 5) * t) * π⁻¹ := by group
        _ = π * (t * (swap 0 1 * swap 2 3 * swap 4 5)) * π⁻¹ := by rw [htx]
        _ = π * t * π⁻¹ * (π * (swap 0 1 * swap 2 3 * swap 4 5) * π⁻¹) := by group
    · have h3 : orderOf (π * t * π⁻¹) = 3 := by
        refine orderOf_eq_prime ?_ ?_
        · rw [conj_pow, ht3]
          group
        · intro h
          apply ht1
          calc t = π⁻¹ * (π * t * π⁻¹) * π := by group
            _ = 1 := by rw [h]; group
      rw [h3]
      decide
  let H' : Subgroup (Perm (Fin 7)) := H.comap (MulAut.conj π).toMonoidHom
  have ht₁H' : t₁ ∈ H' := hconjH t₁ ht₁3 ht₁1 ht₁s ht₁x
  have ht₂H' : t₂ ∈ H' := hconjH t₂ ht₂3 ht₂1 ht₂s ht₂x
  have horbH : ∀ i : Fin 7, i ≠ 6 → ∃ h ∈ H, h (π 0) = π i := by
    intro i hi
    obtain ⟨g, hg, hgi⟩ : ∃ g ∈ H', g 0 = i := by
      rcases horb i hi with h | h | h | h | h | h
      · exact ⟨1, H'.one_mem, h.symm⟩
      · exact ⟨t₁, ht₁H', h.symm⟩
      · exact ⟨t₁ * t₁, H'.mul_mem ht₁H' ht₁H', h.symm⟩
      · exact ⟨t₂ * t₁, H'.mul_mem ht₂H' ht₁H', h.symm⟩
      · exact ⟨t₂ * (t₁ * t₁), H'.mul_mem ht₂H' (H'.mul_mem ht₁H' ht₁H'), h.symm⟩
      · exact ⟨t₁ * (t₂ * (t₁ * t₁)),
          H'.mul_mem ht₁H' (H'.mul_mem ht₂H' (H'.mul_mem ht₁H' ht₁H')), h.symm⟩
    refine ⟨π * g * π⁻¹, hg, ?_⟩
    simp only [Perm.mul_apply, Perm.coe_inv, symm_apply_apply, hgi]
  have hxfix : ∀ y, x y = y → y = π 6 := by
    intro y hy
    rw [← hπ, conj_apply_eq_iff] at hy
    calc y = π (π⁻¹ y) := by simp
      _ = π 6 := by rw [fixed_triple_swap _ hy]
  have hx6 : x (π 6) = π 6 := by
    rw [← hπ, conj_apply_eq_iff]
    simp only [Perm.coe_inv, symm_apply_apply]
    decide
  have hw6 : w (π 6) = π 6 := by
    apply hxfix
    rw [← Perm.mul_apply, hxw, Perm.mul_apply, hx6]
  obtain ⟨e, f, he6, hf6, hef, hwe, hwf⟩ :
      ∃ e f, e ≠ π 6 ∧ f ≠ π 6 ∧ e ≠ f ∧ w e = e ∧ w f = f := by
    have hcard : w.support.card = 4 := card_support_of_even_involution hw2 hw1 hw
    have hsub : w.support ⊆ Finset.univ.erase (π 6) := by
      intro z hz
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact (Perm.mem_support.mp hz) hw6
    have hc : 1 < ((Finset.univ.erase (π 6)) \ w.support).card := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin, hcard]
      norm_num
    obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp hc
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true,
      Perm.notMem_support] at he hf
    exact ⟨e, f, he.1, hf.1, hef, he.2, hf.2⟩
  have hc3 : (swap (π 6) e * swap (π 6) f).IsThreeCycle :=
    Perm.isThreeCycle_swap_mul_swap_same (Ne.symm he6) (Ne.symm hf6) hef
  have hcH : swap (π 6) e * swap (π 6) f ∈ H :=
    hP1w _ (threeCycle_mem_alternating hc3) (commute_threeCycle_of_fixed hw6 hwe hwf)
      (odd_orderOf_threeCycle hc3)
  refine alternating_le_of_transitive_of_threeCycle H (π 0) ?_ hc3 hcH
  intro z
  by_cases hz : π⁻¹ z = 6
  · have hz' : z = π 6 := by rw [← hz]; simp
    have hj : π⁻¹ e ≠ 6 := fun h => he6 (by rw [← h]; simp)
    obtain ⟨h, hh, hhe⟩ := horbH _ hj
    have hπe : π (π⁻¹ e) = e := by simp
    refine ⟨swap (π 6) e * swap (π 6) f * h, H.mul_mem hcH hh, ?_⟩
    rw [Perm.mul_apply, hhe, hπe, Perm.mul_apply,
      swap_apply_of_ne_of_ne he6 hef, swap_apply_right, hz']
  · obtain ⟨h, hh, hhz⟩ := horbH _ hz
    exact ⟨h, hh, by rw [hhz]; simp⟩

theorem a7_core_pair {x w : Perm (Fin 7)} (hx2 : x ^ 2 = 1) (hw2 : w ^ 2 = 1)
    (hxw : x * w = w * x) (hw1 : w ≠ 1) (hx : Perm.sign x = -1) (hw : Perm.sign w = 1)
    (H : Subgroup (Perm (Fin 7)))
    (hP1x : ∀ g ∈ alternatingGroup (Fin 7), x * g = g * x → Odd (orderOf g) → g ∈ H)
    (hP1w : ∀ g ∈ alternatingGroup (Fin 7), w * g = g * w → Odd (orderOf g) → g ∈ H)
    (hP1xw : ∀ g ∈ alternatingGroup (Fin 7), x * w * g = g * (x * w) → Odd (orderOf g) →
      g ∈ H) :
    alternatingGroup (Fin 7) ≤ H := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [map_one] at hx
    exact absurd hx (by decide)
  rcases involution_cycleType hx2 hx1 with hxc | hxc | hxc
  ·
    have hsupp : x.support.card = 2 := by
      rw [← Perm.sum_cycleType, hxc, Multiset.sum_replicate, smul_eq_mul]
    obtain ⟨a, b, hab, rfl⟩ := Perm.card_support_eq_two.mp hsupp
    have key : ∀ z, swap a b (w z) = w (swap a b z) := fun z => by
      rw [← Perm.mul_apply, hxw, Perm.mul_apply]
    by_cases ha : w a = a
    · have hb : w b = b := by
        have h := key b
        rw [swap_apply_right, ha, swap_apply_eq_iff, swap_apply_left] at h
        exact h
      exact a7_core_swap hab w ha hb hw2 H hP1x hP1w
    by_cases ha' : w a = b
    · have hb : w b = a := by
        have h := key b
        rw [swap_apply_right, ha', swap_apply_eq_iff, swap_apply_right] at h
        exact h
      refine a7_core_swap hab (swap a b * w) ?_ ?_ (sq_mul_eq_one_of_commute hx2 hw2 hxw) H
        hP1x hP1xw
      · rw [Perm.mul_apply, ha', swap_apply_right]
      · rw [Perm.mul_apply, hb, swap_apply_left]
    · exfalso
      have h := key a
      rw [swap_apply_left, swap_apply_of_ne_of_ne ha ha'] at h
      exact hab (w.injective h)
  · rw [sign_of_cycleType_replicate hxc] at hx
    exact absurd hx (by decide)
  ·
    obtain ⟨π, hπ⟩ : ∃ π : Perm (Fin 7), π * (swap 0 1 * swap 2 3 * swap 4 5) * π⁻¹ = x := by
      have : IsConj (swap (0 : Fin 7) 1 * swap 2 3 * swap 4 5) x :=
        Perm.isConj_iff_cycleType_eq.mpr (by rw [cycleType_swap_three, hxc])
      exact isConj_iff.mp this
    exact a7_core_triple π hπ hw2 hw1 hw hxw H hP1x hP1w

theorem a7_core {σ τ : Perm (Fin 7)} (hσ2 : σ ^ 2 = 1) (hτ2 : τ ^ 2 = 1) (hστ : σ * τ = τ * σ)
    (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) (hne : σ ≠ τ) (H : Subgroup (Perm (Fin 7)))
    (hP1σ : ∀ g ∈ alternatingGroup (Fin 7), σ * g = g * σ → Odd (orderOf g) → g ∈ H)
    (hP1τ : ∀ g ∈ alternatingGroup (Fin 7), τ * g = g * τ → Odd (orderOf g) → g ∈ H)
    (hP1στ : ∀ g ∈ alternatingGroup (Fin 7), σ * τ * g = g * (σ * τ) → Odd (orderOf g) →
      g ∈ H) :
    alternatingGroup (Fin 7) ≤ H ∨
      (σ ∈ alternatingGroup (Fin 7) ∧ τ ∈ alternatingGroup (Fin 7)) := by
  rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs <;>
    rcases Int.units_eq_one_or (Perm.sign τ) with ht | ht
  · exact Or.inr ⟨Perm.mem_alternatingGroup.mpr hs, Perm.mem_alternatingGroup.mpr ht⟩
  · refine Or.inl (a7_core_pair hτ2 hσ2 hστ.symm hσ1 ht hs H hP1τ hP1σ ?_)
    intro g hg h hodd
    exact hP1στ g hg (by rw [hστ]; exact h) hodd
  · exact Or.inl (a7_core_pair hσ2 hτ2 hστ hτ1 hs ht H hP1σ hP1τ hP1στ)
  · have hστ1 : σ * τ ≠ 1 := by
      intro h
      apply hne
      have hτ' : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hτ2)
      rw [← hτ']
      exact eq_inv_of_mul_eq_one_left h
    have hσστ : σ * (σ * τ) = τ := by rw [← mul_assoc, ← pow_two, hσ2, one_mul]
    refine Or.inl (a7_core_pair (x := σ) (w := σ * τ) hσ2
      (sq_mul_eq_one_of_commute hσ2 hτ2 hστ) (by rw [hσστ, mul_assoc, ← hστ, hσστ]) hστ1 hs
      (by rw [map_mul, hs, ht]; decide) H hP1σ hP1στ ?_)
    intro g hg h hodd
    rw [hσστ] at h
    exact hP1τ g hg h hodd

theorem fourGroupGeneration_a7 {Q : Type} [Group Q] (e : Q ≃* alternatingGroup (Fin 7))
    {α β : MulAut Q} (hαβ : α * β = β * α) (hα2 : α ^ 2 = 1) (hβ2 : β ^ 2 = 1) (hα1 : α ≠ 1)
    (hβ1 : β ≠ 1) (hne : α ≠ β) (H : Subgroup Q)
    (hP1 : ∀ γ ∈ ({α, β, α * β} : Set (MulAut Q)), ∀ x : Q, γ x = x → Odd (orderOf x) →
      x ∈ H) :
    H = ⊤ ∨ (IsSmallDihedralSimple Q ∧ ∃ a b : Q, α = MulAut.conj a ∧ β = MulAut.conj b) := by
  have hc := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)
  let eAut : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective _ hc
  let κ : MulAut Q ≃* Perm (Fin 7) := (MulAut.congr e).trans eAut.symm
  have hκ : ∀ (γ : MulAut Q) (q : Q), ((e (γ q) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      κ γ * (e q : Perm (Fin 7)) * (κ γ)⁻¹ := by
    intro γ q
    have h1 : eAut (κ γ) = MulAut.congr e γ := eAut.apply_symm_apply _
    have h2 : (eAut (κ γ) (e q) : Perm (Fin 7)) = κ γ * (e q : Perm (Fin 7)) * (κ γ)⁻¹ :=
      MulAut.conjNormal_apply _ _
    have h3 : MulAut.congr e γ (e q) = e (γ q) := by
      change e (γ (e.symm (e q))) = e (γ q)
      rw [MulEquiv.symm_apply_apply]
    rw [← h2, h1, h3]
  let H₇ : Subgroup (Perm (Fin 7)) :=
    (H.map (e : Q →* alternatingGroup (Fin 7))).map (alternatingGroup (Fin 7)).subtype
  have hP1₇ : ∀ γ ∈ ({α, β, α * β} : Set (MulAut Q)), ∀ g ∈ alternatingGroup (Fin 7),
      κ γ * g = g * κ γ → Odd (orderOf g) → g ∈ H₇ := by
    intro γ hγ g hg hcomm hodd
    have heq : e (e.symm ⟨g, hg⟩) = ⟨g, hg⟩ := e.apply_symm_apply _
    have hfix : γ (e.symm ⟨g, hg⟩) = e.symm ⟨g, hg⟩ := by
      apply e.injective
      apply Subtype.ext
      rw [hκ, heq]
      change κ γ * g * (κ γ)⁻¹ = g
      rw [hcomm]
      group
    have hord : Odd (orderOf (e.symm ⟨g, hg⟩)) := by
      rw [← MulEquiv.orderOf_eq e, heq, Subgroup.orderOf_mk]
      exact hodd
    exact ⟨e (e.symm ⟨g, hg⟩), ⟨_, hP1 γ hγ _ hfix hord, rfl⟩, by rw [heq]; rfl⟩
  have hκ1 : ∀ γ : MulAut Q, γ ≠ 1 → κ γ ≠ 1 := fun γ hγ h =>
    hγ ((map_eq_one_iff κ κ.injective).mp h)
  rcases a7_core (σ := κ α) (τ := κ β) (by rw [← map_pow, hα2, map_one])
      (by rw [← map_pow, hβ2, map_one]) (by rw [← map_mul, ← map_mul, hαβ]) (hκ1 α hα1)
      (hκ1 β hβ1) (fun h => hne (κ.injective h)) H₇ (hP1₇ α (by simp)) (hP1₇ β (by simp))
      (fun g hg h hodd => hP1₇ (α * β) (by simp) g hg (by rwa [map_mul]) hodd) with
    h | ⟨hσ, hτ⟩
  · left
    rw [eq_top_iff]
    intro q _
    obtain ⟨b, ⟨q', hq'H, rfl⟩, hb⟩ := h (e q).2
    have : q' = q := e.injective (Subtype.ext hb)
    rw [← this]
    exact hq'H
  · right
    refine ⟨Or.inl ⟨e⟩, e.symm ⟨κ α, hσ⟩, e.symm ⟨κ β, hτ⟩, ?_, ?_⟩
    · ext q
      apply e.injective
      apply Subtype.ext
      rw [hκ α q, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl
    · ext q
      apply e.injective
      apply Subtype.ext
      rw [hκ β q, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
