module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.B68Basic

public section

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68

open Subgroup

section Defs

variable {G : Type} [Group G] (N sz : Fin 4 → ℕ)

@[expose] def Inv (k : Fin 4) (t : G) : Prop :=
  orderOf t = 2 ∧ Nat.card (centralizer ({t} : Set G)) = N k

@[expose] def Orb (k : Fin 4) (r s : G) : Prop :=
  match k with
  | 0 => Inv N 1 (r * s)
  | 1 => Inv N 3 (r * s)
  | 2 => orderOf (r * s) = 3
  | 3 => orderOf (r * s) = 4 ∧ Inv N 1 ((r * s) ^ 2)

@[expose] def TableIII : Prop :=
  (∀ t : G, orderOf t = 2 → ∃ k, Inv N k t) ∧
    ∀ (k : Fin 4) (s t : G), Inv N k s → Inv N k t → IsConj s t

@[expose] def TableIV : Prop :=
  ∀ r : G, Inv N 0 r →
    (∀ s : G, Inv N 0 s → s ≠ r → ∃ k, Orb N k r s) ∧
    (∀ (k : Fin 4) (s s' : G), Inv N 0 s → Inv N 0 s' → Orb N k r s → Orb N k r s' →
      ∃ g ∈ centralizer ({r} : Set G), g * s * g⁻¹ = s') ∧
    ∀ k : Fin 4, {s : G | Inv N 0 s ∧ Orb N k r s}.ncard = sz k

@[expose] def Del (x : G) : Set G := {u | Inv N 0 u ∧ u * x = x * u}

@[expose] def Cap : Prop :=
  ∀ {u x : G}, Inv N 0 u → orderOf x = 17 → u * x = x * u →
    Nat.card (centralizer ({u} : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 68

end Defs

structure Arith (N sz : Fin 4 → ℕ) : Prop where
  inj : Function.Injective N
  dvd17 : ∀ k, 17 ∣ N k → k = 0 ∨ k = 3
  dvd0 : 17 ∣ N 0
  nsq : ¬ 17 ^ 2 ∣ N 0
  dvd_sz2 : 17 ∣ sz 2
  cop_sz1 : Nat.Coprime 17 (sz 1)
  ne_sz1 : sz 1 ≠ 0
  idx : N 3 * sz 1 = 2 * N 0

section Basic

variable {G : Type} [Group G] {N sz : Fin 4 → ℕ}

theorem Inv.mul_self {k : Fin 4} {t : G} (h : Inv N k t) : t * t = 1 := by
  have := pow_orderOf_eq_one t
  rwa [h.1, pow_two] at this

theorem Inv.ne_one {k : Fin 4} {t : G} (h : Inv N k t) : t ≠ 1 := by
  rintro rfl
  have := h.1
  simp at this

theorem pow_four_eq_mul (t : G) : t ^ 4 = (t * t) * (t * t) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]

theorem pow_four_of_mul_self_eq_one {t : G} (h : t * t = 1) : t ^ 4 = 1 := by
  rw [pow_four_eq_mul, h, one_mul]

theorem Inv.pow_four {k : Fin 4} {t : G} (h : Inv N k t) : t ^ 4 = 1 :=
  pow_four_of_mul_self_eq_one h.mul_self

theorem Inv.unique (hN : Function.Injective N) {k l : Fin 4} {t : G} (hk : Inv N k t)
    (hl : Inv N l t) : k = l :=
  hN (hk.2.symm.trans hl.2)

theorem Inv.of_isConj [Finite G] {k : Fin 4} {s t : G} (h : Inv N k s) (hst : IsConj s t) :
    Inv N k t := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hst
  refine ⟨?_, ?_⟩
  · rw [← hc, orderOf_conj_eq]
    exact h.1
  · rw [CFSG.Monster.Existence.StdOdd.Cert.card_centralizer_eq_of_isConj hst]
    exact h.2

theorem comm_of_mul_self_eq_one {r s : G} (hr : r * r = 1) (hs : s * s = 1)
    (h : r * s * (r * s) = 1) : r * s = s * r := by
  have h1 : r * s = (r * s)⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hr, inv_eq_of_mul_eq_one_right hs]

theorem Orb.conj [Finite G] {k : Fin 4} {r s h : G} (hh : h * r = r * h) (ho : Orb N k r s) :
    Orb N k r (h * s * h⁻¹) := by
  have e : r * (h * s * h⁻¹) = h * (r * s) * h⁻¹ := by
    calc r * (h * s * h⁻¹) = (h * r * h⁻¹) * (h * s * h⁻¹) := by rw [hh]; group
      _ = h * (r * s) * h⁻¹ := by group
  have hc : ∀ t : G, IsConj t (h * t * h⁻¹) := fun t => isConj_iff.2 ⟨h, rfl⟩
  fin_cases k
  · show Inv N 1 (r * (h * s * h⁻¹))
    rw [e]
    exact Inv.of_isConj ho (hc _)
  · show Inv N 3 (r * (h * s * h⁻¹))
    rw [e]
    exact Inv.of_isConj ho (hc _)
  · show orderOf (r * (h * s * h⁻¹)) = 3
    rw [e, orderOf_conj_eq]
    exact ho
  · show orderOf (r * (h * s * h⁻¹)) = 4 ∧ Inv N 1 ((r * (h * s * h⁻¹)) ^ 2)
    rw [e, orderOf_conj_eq, conj_pow]
    exact ⟨ho.1, Inv.of_isConj ho.2 (hc _)⟩

theorem commute_conj_of_commute {n c x : G} (hn : n * x = x * n) (hc : c * x = x * c) :
    n * c * n⁻¹ * x = x * (n * c * n⁻¹) := by
  have hn' : n⁻¹ * x = x * n⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hn, mul_inv_cancel_right]
  calc n * c * n⁻¹ * x = n * c * (n⁻¹ * x) := by rw [mul_assoc]
    _ = n * c * (x * n⁻¹) := by rw [hn']
    _ = n * (c * x) * n⁻¹ := by group
    _ = n * (x * c) * n⁻¹ := by rw [hc]
    _ = (n * x) * c * n⁻¹ := by group
    _ = (x * n) * c * n⁻¹ := by rw [hn]
    _ = x * (n * c * n⁻¹) := by group

theorem commute_mul_of_commute {a b x : G} (ha : a * x = x * a) (hb : b * x = x * b) :
    a * b * x = x * (a * b) := by
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

theorem exists_five_of_order_four {n v : G} (hn : orderOf n = 4) (hv : v * v = 1) (hv1 : v ≠ 1)
    (hva : v ≠ n * n) :
    ∃ S : Set G, S.ncard = 5 ∧ (∀ g ∈ S, g ^ 4 = 1) ∧ ∀ g ∈ S, g ∈ zpowers n ∨ g = v := by
  classical
  let S₁ : Finset G := (Finset.range 4).image (fun i => n ^ i)
  have hS₁ : S₁.card = 4 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    refine pow_injOn_Iio_orderOf ?_ ?_ hij
    · simpa [hn] using hi
    · simpa [hn] using hj
  have hn4 : n ^ 4 = 1 := hn ▸ pow_orderOf_eq_one n
  have hvS : v ∉ S₁ := by
    simp only [S₁, Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro i hi hvi
    interval_cases i
    · exact hv1 (by simpa using hvi.symm)
    · have hvn : v = n := by simpa using hvi.symm
      have h2 : orderOf n = 2 := by
        rw [← hvn]
        exact (orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hv) hv1)
      rw [hn] at h2
      omega
    · exact hva (by rw [← pow_two]; exact hvi.symm)
    · have hvi' : n ^ 3 = v := hvi
      have h3 : v * n = 1 := by rw [← hvi', ← pow_succ]; exact hn4
      have hvn : n = v := mul_left_cancel (h3.trans hv.symm)
      have h2 : orderOf n = 2 := by
        rw [hvn]
        exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hv) hv1
      rw [hn] at h2
      omega
  refine ⟨↑(insert v S₁), ?_, ?_, ?_⟩
  · rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem hvS, hS₁]
  · intro g hg
    rw [Finset.mem_coe, Finset.mem_insert] at hg
    rcases hg with rfl | hg
    · exact pow_four_of_mul_self_eq_one hv
    · simp only [S₁, Finset.mem_image] at hg
      obtain ⟨i, -, rfl⟩ := hg
      rw [← pow_mul, mul_comm, pow_mul, hn4, one_pow]
  · intro g hg
    rw [Finset.mem_coe, Finset.mem_insert] at hg
    rcases hg with rfl | hg
    · exact Or.inr rfl
    · simp only [S₁, Finset.mem_image] at hg
      obtain ⟨i, -, rfl⟩ := hg
      exact Or.inl (Subgroup.pow_mem _ (Subgroup.mem_zpowers n) i)

end Basic

end CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68
