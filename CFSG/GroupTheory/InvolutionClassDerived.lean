module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Solvable

import CFSG.GroupTheory.InvolutionClassProducts
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

theorem odd_orderOf_of_mem_closure_of_odd {Y : Type*} [Group Y] {S : Set Y}
    (hS : ∀ s ∈ S, Odd (orderOf s))
    (hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, Commute a b)
    {x : Y} (hx : x ∈ Subgroup.closure S) : Odd (orderOf x) := by
  refine Subgroup.closure_induction (p := fun x _ => Odd (orderOf x)) hS ?_ ?_ ?_ hx
  · simp
  · intro a b ha hb hao hbo
    exact odd_orderOf_mul_of_commute (hcomm a ha b hb) hao hbo
  · intro a ha hao
    rwa [orderOf_inv]

theorem sup_closure_mul_zpowers_eq_top {Y : Type*} [Group Y] {T : Set Y} {t₀ : Y}
    (ht₀ : t₀ ∈ T) (hsq : ∀ t ∈ T, t * t = 1) (hgen : Subgroup.closure T = ⊤) :
    Subgroup.closure {z : Y | ∃ t ∈ T, z = t₀ * t} ⊔ Subgroup.zpowers t₀ = ⊤ := by
  rw [eq_top_iff, ← hgen]
  rw [Subgroup.closure_le]
  intro t ht
  have hb : t₀ * t ∈ Subgroup.closure {z : Y | ∃ u ∈ T, z = t₀ * u} :=
    Subgroup.subset_closure ⟨t, ht, rfl⟩
  have ht' : t = t₀ * (t₀ * t) := by rw [← mul_assoc, hsq t₀ ht₀, one_mul]
  have hmem : t₀ * (t₀ * t) ∈ Subgroup.zpowers t₀ ⊔
      Subgroup.closure {z : Y | ∃ u ∈ T, z = t₀ * u} :=
    Subgroup.mul_mem_sup (Subgroup.mem_zpowers t₀) hb
  rw [ht']
  rwa [sup_comm] at hmem

theorem conj_mul_inv_of_mem {Y : Type*} [Group Y] {T : Set Y} {t₀ : Y}
    (ht₀ : t₀ ∈ T) (hsq : ∀ t ∈ T, t * t = 1) {t : Y} (ht : t ∈ T) :
    t₀ * (t₀ * t) * t₀ = (t₀ * t)⁻¹ := by
  calc t₀ * (t₀ * t) * t₀ = (t₀ * t₀) * (t * t₀) := by group
    _ = t * t₀ := by rw [hsq t₀ ht₀, one_mul]
    _ = (t₀ * t)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq t ht),
        inv_eq_of_mul_eq_one_right (hsq t₀ ht₀)]

theorem conj_mem_normalizer_closure_mul {Y : Type*} [Group Y] {T : Set Y} {t₀ : Y}
    (ht₀ : t₀ ∈ T) (hsq : ∀ t ∈ T, t * t = 1) :
    t₀ ∈ Subgroup.normalizer
      (Subgroup.closure {z : Y | ∃ t ∈ T, z = t₀ * t} : Set Y) := by
  let S : Set Y := {z : Y | ∃ t ∈ T, z = t₀ * t}
  let S' : Set Y := {z : Y | z ∈ S ∨ z⁻¹ ∈ S}
  have hclosure : Subgroup.closure S' = Subgroup.closure S := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      rcases hz with hz | hz
      · exact Subgroup.subset_closure hz
      · simpa using (Subgroup.closure S).inv_mem (Subgroup.subset_closure hz)
    · exact Subgroup.closure_mono fun z hz => Or.inl hz
  have hmap : ∀ z ∈ S', t₀ * z * t₀ ∈ S' := by
    rintro z (hz | hz)
    · obtain ⟨t, ht, rfl⟩ := hz
      exact Or.inr ⟨t, ht, by rw [conj_mul_inv_of_mem ht₀ hsq ht, inv_inv]⟩
    · obtain ⟨t, ht, hz⟩ := hz
      refine Or.inl ⟨t, ht, ?_⟩
      have hz' : z = (t₀ * t)⁻¹ := by rw [← hz, inv_inv]
      rw [hz']
      have hst : (t₀ * t)⁻¹ = t * t₀ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq t ht),
          inv_eq_of_mul_eq_one_right (hsq t₀ ht₀)]
      calc t₀ * (t₀ * t)⁻¹ * t₀ = t₀ * (t * t₀) * t₀ := by rw [hst]
        _ = (t₀ * t) * (t₀ * t₀) := by group
        _ = t₀ * t := by rw [hsq t₀ ht₀, mul_one]
  have ht₀_norm' : t₀ ∈ Subgroup.normalizer S' := by
    rw [Subgroup.mem_set_normalizer_iff]
    simp only [inv_eq_of_mul_eq_one_right (hsq t₀ ht₀)]
    intro z
    constructor
    · exact hmap z
    · intro hz
      have h := hmap (t₀ * z * t₀) hz
      have hz_eq : t₀ * (t₀ * z * t₀) * t₀ = z := by
        calc t₀ * (t₀ * z * t₀) * t₀ = (t₀ * t₀) * z * (t₀ * t₀) := by group
          _ = z := by rw [hsq t₀ ht₀, one_mul, mul_one]
      rwa [hz_eq] at h
  change t₀ ∈ Subgroup.normalizer (Subgroup.closure S : Set Y)
  rw [← hclosure]
  exact Subgroup.normalizer_le_normalizer_closure S' ht₀_norm'

theorem closure_mul_eq_derivedSeries_one {Y : Type*} [Group Y] {T : Set Y} {t₀ : Y}
    (ht₀ : t₀ ∈ T) (hconj : ∀ t ∈ T, IsConj t₀ t)
    (hsq : ∀ t ∈ T, t * t = 1) (hgen : Subgroup.closure T = ⊤) :
    Subgroup.closure {z : Y | ∃ t ∈ T, z = t₀ * t} = derivedSeries Y 1 := by
  let S : Set Y := {z : Y | ∃ t ∈ T, z = t₀ * t}
  let B : Subgroup Y := Subgroup.closure S
  have hB_le : B ≤ derivedSeries Y 1 := by
    change Subgroup.closure S ≤ derivedSeries Y 1
    rw [Subgroup.closure_le]
    rintro z ⟨t, ht, rfl⟩
    rw [derivedSeries_one]
    exact mul_mem_commutator_of_isConj (hconj t ht) (hsq t₀ ht₀)
  have hsup : B ⊔ Subgroup.zpowers t₀ = ⊤ :=
    sup_closure_mul_zpowers_eq_top ht₀ hsq hgen
  have ht₀_norm : t₀ ∈ Subgroup.normalizer (B : Set Y) :=
    conj_mem_normalizer_closure_mul ht₀ hsq
  have hBnorm : B.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le (Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr ht₀_norm)
  have hA_le_B : derivedSeries Y 1 ≤ B := by
    have hcomm := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      (N := B) (H := Subgroup.zpowers t₀) hsup (Subgroup.zpowers_isMulCommutative t₀)
    rwa [derivedSeries_one]
  exact le_antisymm hB_le hA_le_B

theorem conj_eq_inv_of_mem_derivedSeries_one {Y : Type*} [Group Y] {T : Set Y} {t₀ : Y}
    (ht₀ : t₀ ∈ T) (hconj : ∀ t ∈ T, IsConj t₀ t)
    (hsq : ∀ t ∈ T, t * t = 1) (hgen : Subgroup.closure T = ⊤)
    (hAcomm : IsMulCommutative (derivedSeries Y 1))
    {a : Y} (ha : a ∈ derivedSeries Y 1) : t₀ * a * t₀ = a⁻¹ := by
  let S : Set Y := {z : Y | ∃ t ∈ T, z = t₀ * t}
  have hAeq : derivedSeries Y 1 = Subgroup.closure S :=
    (closure_mul_eq_derivedSeries_one ht₀ hconj hsq hgen).symm
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, Commute x y := by
    intro x hx y hy
    have hxA : x ∈ derivedSeries Y 1 := by rw [hAeq]; exact hx
    have hyA : y ∈ derivedSeries Y 1 := by rw [hAeq]; exact hy
    exact (commute_iff_eq x y).2 (congrArg Subtype.val
      (hAcomm.is_comm.comm ⟨x, hxA⟩ ⟨y, hyA⟩))
  have ha' : a ∈ Subgroup.closure S := by rw [← hAeq]; exact ha
  refine Subgroup.closure_induction (p := fun x _ => t₀ * x * t₀ = x⁻¹) ?_ ?_ ?_ ?_ ha'
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact conj_mul_inv_of_mem ht₀ hsq ht
  · show t₀ * 1 * t₀ = 1⁻¹
    rw [mul_one, inv_one, hsq t₀ ht₀]
  · intro x y hx hy hxo hyo
    have hxy : Commute x y := hcomm x hx y hy
    have h1 : (t₀ * x * t₀) * (t₀ * y * t₀) = t₀ * (x * y) * t₀ := by
      calc (t₀ * x * t₀) * (t₀ * y * t₀) = t₀ * x * (t₀ * t₀) * y * t₀ := by group
        _ = t₀ * x * y * t₀ := by rw [hsq t₀ ht₀]; group
        _ = t₀ * (x * y) * t₀ := by group
    calc t₀ * (x * y) * t₀ = (t₀ * x * t₀) * (t₀ * y * t₀) := h1.symm
      _ = x⁻¹ * y⁻¹ := by rw [hxo, hyo]
      _ = (x * y)⁻¹ := by rw [mul_inv_rev, (hxy.inv_left.inv_right).eq]
  · intro x hx hxo
    have h := congrArg Inv.inv hxo
    simpa [mul_assoc, mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq t₀ ht₀)] using h

theorem eq_of_inv_mul_eq_of_odd {Y : Type*} [Group Y] {A : Subgroup Y}
    (hAodd : ∀ x ∈ A, Odd (orderOf x)) {a b : Y} (ha : a ∈ A) (hb : b ∈ A)
    (h : a⁻¹ * b = b⁻¹ * a) : b = a := by
  have hx : a⁻¹ * b = (a⁻¹ * b)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact h
  have hx2 : (a⁻¹ * b) * (a⁻¹ * b) = 1 := by
    nth_rewrite 2 [hx]
    exact mul_inv_cancel _
  have hA : a⁻¹ * b ∈ A := A.mul_mem (A.inv_mem ha) hb
  have hxodd := hAodd _ hA
  have hdvd : orderOf (a⁻¹ * b) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
  have hx1 : a⁻¹ * b = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hxodd
      exact absurd hxodd (by decide)
  calc b = a * (a⁻¹ * b) := by group
    _ = a * 1 := by rw [hx1]
    _ = a := mul_one _

theorem exists_eq_mul_of_notMem_derivedSeries_one {Y : Type*} [Group Y]
    {T : Set Y} {t₀ : Y} (ht₀ : t₀ ∈ T)
    (hconj : ∀ t ∈ T, ∀ t' ∈ T, IsConj t t')
    (hsq : ∀ t ∈ T, t * t = 1) (hgen : Subgroup.closure T = ⊤)
    {c : Y} (hcA : c ∉ derivedSeries Y 1) :
    ∃ a ∈ derivedSeries Y 1, c = t₀ * a := by
  let S : Set Y := {z : Y | ∃ t ∈ T, z = t₀ * t}
  let B : Subgroup Y := Subgroup.closure S
  have hAeq : derivedSeries Y 1 = B :=
    (closure_mul_eq_derivedSeries_one ht₀
      (fun t ht => hconj t₀ ht₀ t ht) hsq hgen).symm
  have hBnorm : B.Normal := hAeq ▸ derivedSeries_normal Y 1
  have hcB : c ∉ B := by rwa [← hAeq]
  have hsupB : B ⊔ Subgroup.zpowers t₀ = ⊤ :=
    sup_closure_mul_zpowers_eq_top ht₀ hsq hgen
  have hmem : c ∈ B ⊔ Subgroup.zpowers t₀ := by
    rw [hsupB]; exact Subgroup.mem_top c
  obtain ⟨a, ha, z, hz, haz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := B) (t := Subgroup.zpowers t₀)
      (hs := hBnorm)).mp hmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hz_cases : t₀ ^ k = 1 ∨ t₀ ^ k = t₀ := by
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, show t₀ ^ (2 : ℤ) = 1 by rw [zpow_two, hsq t₀ ht₀], one_zpow]
    · right
      rw [zpow_add_one, zpow_mul,
        show t₀ ^ (2 : ℤ) = 1 by rw [zpow_two, hsq t₀ ht₀], one_zpow, one_mul]
  rcases hz_cases with hz1 | hzt
  · rw [hz1, mul_one] at haz
    exact (hcB (haz ▸ ha)).elim
  · have hc_z : c = a * t₀ := by rw [← haz, hzt]
    have haA : a ∈ derivedSeries Y 1 := by rwa [← hAeq] at ha
    have hmemA : t₀ * c ∈ derivedSeries Y 1 := by
      rw [hc_z]
      have h := (derivedSeries_normal Y 1).conj_mem a haA t₀
      simpa [inv_eq_of_mul_eq_one_right (hsq t₀ ht₀), mul_assoc] using h
    exact ⟨t₀ * c, hmemA, by rw [← mul_assoc, hsq t₀ ht₀, one_mul]⟩

theorem forall_eq_of_eq_mul_of_mem_center {Y : Type*} [Group Y] {T : Set Y}
    (hsq : ∀ t ∈ T, t * t = 1) {t₀ : Y} (ht₀ : t₀ ∈ T)
    (hAinv : ∀ a ∈ derivedSeries Y 1, t₀ * a * t₀ = a⁻¹)
    (hAodd : ∀ a ∈ derivedSeries Y 1, Odd (orderOf a))
    (hAeq : derivedSeries Y 1 = Subgroup.closure {z : Y | ∃ t ∈ T, z = t₀ * t})
    {a c : Y} (ha : a ∈ derivedSeries Y 1) (hc : c ∈ Subgroup.center Y)
    (hc_eq : c = t₀ * a) : ∀ t ∈ T, t = c := by
  intro t ht
  have hatB : t₀ * t ∈ Subgroup.closure {z : Y | ∃ u ∈ T, z = t₀ * u} :=
    Subgroup.subset_closure ⟨t, ht, rfl⟩
  have hatA : t₀ * t ∈ derivedSeries Y 1 := by rw [hAeq]; exact hatB
  have ht_eq : t = t₀ * (t₀ * t) := by rw [← mul_assoc, hsq t₀ ht₀, one_mul]
  have hct : c * t = a⁻¹ * (t₀ * t) := by
    calc c * t = (t₀ * a) * (t₀ * (t₀ * t)) := by
          conv_lhs => rw [hc_eq, ht_eq]
      _ = (t₀ * a * t₀) * (t₀ * t) := by group
      _ = a⁻¹ * (t₀ * t) := by rw [hAinv a ha]
  have htc : t * c = (t₀ * t)⁻¹ * a := by
    calc t * c = (t₀ * (t₀ * t)) * (t₀ * a) := by
          conv_lhs => rw [hc_eq, ht_eq]
      _ = (t₀ * (t₀ * t) * t₀) * a := by group
      _ = (t₀ * t)⁻¹ * a := by rw [hAinv (t₀ * t) hatA]
  have heq : a⁻¹ * (t₀ * t) = (t₀ * t)⁻¹ * a := by
    rw [← hct, (Subgroup.mem_center_iff.mp hc t).symm]
    exact htc
  have hat_eq : t₀ * t = a :=
    eq_of_inv_mul_eq_of_odd hAodd ha hatA heq
  calc t = t₀ * (t₀ * t) := ht_eq
    _ = t₀ * a := by rw [hat_eq]
    _ = c := hc_eq.symm

theorem eq_one_of_mem_center_of_isConj {Y : Type*} [Group Y] {T : Set Y}
    (hne : ∃ t ∈ T, ∃ t' ∈ T, t ≠ t')
    (hconj : ∀ t ∈ T, ∀ t' ∈ T, IsConj t t')
    (hsq : ∀ t ∈ T, t * t = 1)
    (hgen : Subgroup.closure T = ⊤)
    (hder : derivedSeries Y 2 = ⊥)
    (hodd : ∀ t ∈ T, ∀ t' ∈ T, Odd (orderOf (t * t')))
    {c : Y} (hc : c ∈ Subgroup.center Y) (hc2 : c * c = 1) : c = 1 := by
  have hne_keep := hne
  obtain ⟨t₀, ht₀, -, -⟩ := hne
  let S : Set Y := {z : Y | ∃ t ∈ T, z = t₀ * t}
  have hAeq : derivedSeries Y 1 = Subgroup.closure S :=
    (closure_mul_eq_derivedSeries_one ht₀
      (fun t ht => hconj t₀ ht₀ t ht) hsq hgen).symm
  have hAcomm : IsMulCommutative (derivedSeries Y 1) := isMulCommutative_derivedSeries_one hder
  have hSodd : ∀ s ∈ S, Odd (orderOf s) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hodd t₀ ht₀ t ht
  have hScomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, Commute a b := by
    intro a ha b hb
    have haA : a ∈ derivedSeries Y 1 := by rw [hAeq]; exact ha
    have hbA : b ∈ derivedSeries Y 1 := by rw [hAeq]; exact hb
    exact (commute_iff_eq a b).2 (congrArg Subtype.val
      (hAcomm.is_comm.comm ⟨a, haA⟩ ⟨b, hbA⟩))
  have hAodd : ∀ a ∈ derivedSeries Y 1, Odd (orderOf a) := by
    intro a ha
    have haS : a ∈ Subgroup.closure S := by rw [← hAeq]; exact ha
    exact odd_orderOf_of_mem_closure_of_odd hSodd hScomm haS
  have hAinv : ∀ a ∈ derivedSeries Y 1, t₀ * a * t₀ = a⁻¹ :=
    fun a ha => conj_eq_inv_of_mem_derivedSeries_one ht₀
      (fun t ht => hconj t₀ ht₀ t ht) hsq hgen hAcomm ha
  by_cases hcA : c ∈ derivedSeries Y 1
  · have hco := hAodd c hcA
    have hdvd : orderOf c ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hco
      exact absurd hco (by decide)
  · obtain ⟨a, ha, hc_eq⟩ :=
      exists_eq_mul_of_notMem_derivedSeries_one ht₀ hconj hsq hgen hcA
    have hall := forall_eq_of_eq_mul_of_mem_center hsq ht₀ hAinv hAodd hAeq ha hc hc_eq
    obtain ⟨u, hu, v, hv, huv⟩ := hne_keep
    exact (huv ((hall u hu).trans (hall v hv).symm)).elim

theorem mem_of_mul_pow_mem_of_conj_mem {Y : Type*} [Group Y] {N : Subgroup Y} {p w : Y}
    (hp : p ∈ N) (hwp : w * p * w⁻¹ ∈ N) (hw2 : w * w = 1) {n : ℕ} (hn : Odd n)
    (h : (p * w) ^ n ∈ N) : w ∈ N := by
  have hsq : (p * w) * (p * w) ∈ N := by
    have heq : (p * w) * (p * w) = p * (w * p * w⁻¹) := by
      calc (p * w) * (p * w) = p * (w * p) * w := by group
        _ = p * (w * p * w⁻¹) * (w * w) := by group
        _ = p * (w * p * w⁻¹) := by rw [hw2, mul_one]
    rw [heq]
    exact N.mul_mem hp hwp
  obtain ⟨k, rfl⟩ := hn
  have heven : (p * w) ^ (2 * k) ∈ N := by
    rw [pow_mul]
    simpa [pow_two] using N.pow_mem hsq k
  have hsplit : (p * w) ^ (2 * k + 1) = ((p * w) ^ (2 * k) * p) * w := by
    rw [pow_succ]
    group
  have hprod : (p * w) ^ (2 * k) * p ∈ N := N.mul_mem heven hp
  have hw_eq : w = ((p * w) ^ (2 * k) * p)⁻¹ * (p * w) ^ (2 * k + 1) := by
    rw [hsplit]
    group
  rw [hw_eq]
  exact N.mul_mem (N.inv_mem hprod) h

end CFSG.GroupTheory

end
