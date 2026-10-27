module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Close

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutatorElement_mul_mul_of_commute {u v a b : G} (hua : Commute u a)
    (hub : Commute u b) (hva : Commute v a) (hvb : Commute v b) (huv : Commute u v) :
    ⁅u * a, v * b⁆ = ⁅a, b⁆ := by
  have h1 : ⁅u * a, v * b⁆ = ⁅u * a, b⁆ := by
    have hc : Commute v (b * (u * a)⁻¹ * b⁻¹) :=
      (hvb.mul_right (huv.symm.mul_right hva).inv_right).mul_right hvb.inv_right
    calc ⁅u * a, v * b⁆ = (u * a) * (v * (b * (u * a)⁻¹ * b⁻¹) * v⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = (u * a) * (b * (u * a)⁻¹ * b⁻¹) := by rw [hc.mul_inv_cancel]
      _ = ⁅u * a, b⁆ := by simp only [commutatorElement_def]; group
  have hc : Commute u (a * b * a⁻¹) := (hua.mul_right hub).mul_right hua.inv_right
  calc ⁅u * a, v * b⁆ = ⁅u * a, b⁆ := h1
    _ = (u * (a * b * a⁻¹) * u⁻¹) * b⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [hc.mul_inv_cancel]; simp only [commutatorElement_def]

theorem commute_commutatorElement_of_commute {y a b : G}
    (h1 : Commute ⁅y, a⁆ a) (h2 : Commute ⁅y, a⁆ b) (h3 : Commute ⁅y, b⁆ a)
    (h4 : Commute ⁅y, b⁆ b) (h5 : Commute ⁅y, a⁆ ⁅y, b⁆) : Commute y ⁅a, b⁆ := by
  have e1 : y * a * y⁻¹ = ⁅y, a⁆ * a := by simp only [commutatorElement_def]; group
  have e2 : y * b * y⁻¹ = ⁅y, b⁆ * b := by simp only [commutatorElement_def]; group
  have hconj : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  rw [e1, e2, commutatorElement_mul_mul_of_commute h1 h2 h3 h4 h5] at hconj
  exact mul_inv_eq_iff_eq_mul.1 hconj

theorem commute_of_perfect_of_central {Q O : Subgroup G} (hQ : ⁅Q, Q⁆ = Q)
    (hQO : ∀ z ∈ Q, z ∈ O → ∀ q ∈ Q, Commute z q) {x : G} (hx : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hxO : ∀ q ∈ Q, ⁅x, q⁆ ∈ O) : ∀ q ∈ Q, Commute x q := by
  have hQmem : ∀ q ∈ Q, ⁅x, q⁆ ∈ Q := fun q hq =>
    Q.mul_mem (hx q hq) (Q.inv_mem hq)
  have hle : ⁅Q, Q⁆ ≤ centralizer ({x} : Set G) := by
    rw [commutator_le]
    intro a ha b hb
    rw [mem_centralizer_singleton_iff]
    exact (commute_commutatorElement_of_commute (hQO _ (hQmem a ha) (hxO a ha) a ha)
      (hQO _ (hQmem a ha) (hxO a ha) b hb) (hQO _ (hQmem b hb) (hxO b hb) a ha)
      (hQO _ (hQmem b hb) (hxO b hb) b hb)
      (hQO _ (hQmem a ha) (hxO a ha) _ (hQmem b hb))).symm.eq
  intro q hq
  rw [hQ] at hle
  exact (mem_centralizer_singleton_iff.1 (hle hq)).symm

theorem commutator_le_centralizer_of_central {H O Z : Subgroup G} (hZ : Z ≤ center G)
    (h : ∀ h ∈ H, ∀ o ∈ O, ⁅h, o⁆ ∈ Z) : ⁅H, H⁆ ≤ centralizer (O : Set G) := by
  have hc : ∀ o ∈ O, ∀ a ∈ H, ∀ g : G, Commute ⁅o, a⁆ g := by
    intro o ho a ha g
    have hmem : ⁅o, a⁆ ∈ Z := by
      rw [← commutatorElement_inv]
      exact Z.inv_mem (h a ha o ho)
    exact (mem_center_iff.1 (hZ hmem) g).symm
  rw [commutator_le]
  intro a ha b hb
  rw [mem_centralizer_iff]
  intro o ho
  exact (commute_commutatorElement_of_commute (hc o ho a ha a) (hc o ho a ha b)
    (hc o ho b hb a) (hc o ho b hb b) (hc o ho a ha _)).eq

theorem exists_perfect_core {H : Type*} [Group H] [Finite G] (ψ : G →* H) {W L : Subgroup G}
    (hL : ∀ w ∈ W, ∀ l ∈ L, w * l * w⁻¹ ∈ L) (hper : ⁅L.map ψ, L.map ψ⁆ = L.map ψ) :
    ∃ Q : Subgroup G, Q ≤ L ∧ (∀ w ∈ W, ∀ q ∈ Q, w * q * w⁻¹ ∈ Q) ∧ Q.map ψ = L.map ψ ∧
      ⁅Q, Q⁆ = Q := by
  let S : Set (Subgroup G) :=
    {Q | Q ≤ L ∧ (∀ w ∈ W, ∀ q ∈ Q, w * q * w⁻¹ ∈ Q) ∧ Q.map ψ = L.map ψ}
  have : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  obtain ⟨Q, ⟨hQL, hQW, hQψ⟩, hmin⟩ := wellFounded_lt.has_min S ⟨L, le_rfl, hL, rfl⟩
  refine ⟨Q, hQL, hQW, hQψ, ?_⟩
  have hle : ⁅Q, Q⁆ ≤ Q := by
    rw [commutator_le]
    intro a ha b hb
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
  have hmem : ⁅Q, Q⁆ ∈ S := by
    refine ⟨hle.trans hQL, ?_, ?_⟩
    · intro w hw c hc
      have hf : (⁅Q, Q⁆).map (MulAut.conj w).toMonoidHom ≤ ⁅Q, Q⁆ := by
        rw [map_commutator]
        refine commutator_mono ?_ ?_ <;>
        · rintro _ ⟨q, hq, rfl⟩
          exact hQW w hw q hq
      exact hf ⟨c, hc, rfl⟩
    · rw [map_commutator, hQψ, hper]
  by_contra hne
  exact hmin _ hmem (lt_of_le_of_ne hle hne)

theorem inv_of_fpf {A : Subgroup G} [Finite A] {t : G} (ht : t * t = 1)
    (hA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (hfix : ∀ a ∈ A, t * a * t⁻¹ = a → a = 1) :
    ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hinj : ∀ a b : G, a ∈ A → b ∈ A → a⁻¹ * (t * a * t⁻¹) = b⁻¹ * (t * b * t⁻¹) → a = b := by
    intro a b ha hb h
    have hd : b * a⁻¹ ∈ A := A.mul_mem hb (A.inv_mem ha)
    have h3 : t * b * t⁻¹ = b * (a⁻¹ * (t * a * t⁻¹)) := by rw [h]; group
    have h2 : t * (b * a⁻¹) * t⁻¹ = b * a⁻¹ := by
      calc t * (b * a⁻¹) * t⁻¹ = (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ := by group
        _ = b * a⁻¹ := by rw [h3]; group
    exact (mul_inv_eq_one.1 (hfix _ hd h2)).symm
  let f : A → A := fun a => ⟨(a : G)⁻¹ * (t * a * t⁻¹), A.mul_mem (A.inv_mem a.2) (hA a a.2)⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (hinj a b a.2 b.2 (congrArg Subtype.val hab))
  intro a ha
  obtain ⟨⟨c, hcA⟩, hc⟩ := Finite.injective_iff_surjective.1 hf ⟨a, ha⟩
  have hc' : c⁻¹ * (t * c * t⁻¹) = a := congrArg Subtype.val hc
  have h2 : t⁻¹ * t⁻¹ = 1 := by rw [ht']; exact ht
  subst hc'
  calc t * (c⁻¹ * (t * c * t⁻¹)) * t⁻¹ = t * c⁻¹ * t * c * (t⁻¹ * t⁻¹) := by group
    _ = t * c⁻¹ * t * c := by rw [h2, mul_one]
    _ = (c⁻¹ * (t * c * t⁻¹))⁻¹ := by
      rw [show (c⁻¹ * (t * c * t⁻¹))⁻¹ = t * c⁻¹ * t⁻¹ * c by group, ht']

theorem comm_of_fpf {A : Subgroup G} [Finite A] {t : G} (ht : t * t = 1)
    (hA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (hfix : ∀ a ∈ A, t * a * t⁻¹ = a → a = 1) :
    ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro a ha b hb
  have h := inv_of_fpf ht hA hfix
  have hab : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
    rw [← h (a * b) (A.mul_mem ha hb), ← h a ha, ← h b hb]; group
  rw [mul_inv_rev] at hab
  calc a * b = (b⁻¹ * a⁻¹)⁻¹ := by group
    _ = (a⁻¹ * b⁻¹)⁻¹ := by rw [hab]
    _ = b * a := by group

theorem exists_pPow_lift {H : Type*} [Group H] [Finite G] (ψ : G →* H) (p : ℕ) [Fact p.Prime]
    (g : G) (a : H) (hψ : ψ g = a) (ha : a ^ p = 1) :
    ∃ k : ℕ, IsPGroup p (zpowers (g ^ k)) ∧ ψ (g ^ k) = a := by
  have hp : p.Prime := Fact.out
  obtain ⟨e, m, hm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  obtain ⟨j, -, hj⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime (hp.coprime_iff_not_dvd.2 hm).symm hp.one_lt
  refine ⟨m * j, ?_, ?_⟩
  · have hpow : (g ^ (m * j)) ^ (p ^ e) = 1 := by
      rw [← pow_mul, show m * j * p ^ e = orderOf g * j by rw [hn]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hpow)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  · obtain ⟨q, hq⟩ : ∃ q, m * j = p * q + 1 :=
      ⟨m * j / p, by have := Nat.div_add_mod (m * j) p; omega⟩
    rw [map_pow, hψ, hq, pow_succ, pow_mul, ha, one_pow, one_mul]

end CFSG.EvenSporadicStandard.RuStd.S2.Close
