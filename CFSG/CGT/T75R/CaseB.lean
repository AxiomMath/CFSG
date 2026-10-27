module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB8
public import CFSG.CGT.T75R.Indep

public section

namespace CFSG.CGT.T75R

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem exists_two_ne_one [Finite G] {K : Subgroup G} (h : 3 ≤ Nat.card K) :
    ∃ u v : G, u ∈ K ∧ v ∈ K ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  have h2 : 2 < (K : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact lt_of_lt_of_le (by norm_num) h
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 h2
  by_cases hp1 : p = 1
  · exact ⟨q, r, hq, hr, fun h => hpq (hp1.trans h.symm), fun h => hpr (hp1.trans h.symm), hqr⟩
  by_cases hq1 : q = 1
  · exact ⟨p, r, hp, hr, hp1, fun h => hqr (hq1.trans h.symm), hpr⟩
  · exact ⟨p, q, hp, hq, hp1, hq1, hpq⟩

theorem mem_sup_iff_of_comm {P Q : Subgroup G} (hc : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) {z : G} :
    z ∈ P ⊔ Q ↔ ∃ p ∈ P, ∃ q ∈ Q, z = p * q := by
  have hle : P ≤ Subgroup.normalizer (Q : Set G) := fun p hp => mem_normalizer_of_commute (hc p hp)
  have h := Subgroup.coe_mul_of_left_le_normalizer_right P Q hle
  have : z ∈ ((P ⊔ Q : Subgroup G) : Set G) ↔ z ∈ ((P : Set G) * (Q : Set G)) := by rw [h]
  simp only [SetLike.mem_coe, Set.mem_mul] at this
  rw [this]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩

theorem false_of_pair_swap [Finite G] {T T₁ : Subgroup G} (hP : MaxPair T T₁)
    (hTc : Nat.card T = 8) (hLc : Nat.card (normIn T T₁) ≤ 4) {Tx : Subgroup G}
    (hTx : ∃ g : G, Tx = conjSubgroup g T) {x : G} (hx : x ∈ Tx) (hx1 : x ≠ 1)
    (hxD : x ∈ classD T) (hx2 : x * x = 1) {L A B N : Subgroup G} (hN : IsElemAbelian 2 N)
    (hLN : L ≤ N) (hAN : A ≤ N) (hxN : x ∈ Subgroup.normalizer (N : Set G))
    (hLnot : ¬ L ≤ Subgroup.normalizer (Tx : Set G)) (hxL : conjSubgroup x L = L)
    (hxA : conjSubgroup x A = B) (hAB : A ⊓ B = ⊥) (hLAB : L ⊓ (A ⊔ B) = ⊥)
    (hxl : ∃ l ∈ L, x * l ≠ l * x) (hA3 : 3 ≤ Nat.card A) : False := by
  obtain ⟨e, e', he, he', he1, he'1, hee'⟩ := exists_two_ne_one hA3
  obtain ⟨l, hl, hxl⟩ := hxl
  have hbmem : ∀ n ∈ A, x * n * x⁻¹ ∈ B := fun n hn => by
    rw [← hxA]; exact conj_mem_conjSubgroup x hn
  have hcA : ∀ n ∈ A, ⁅x, n⁆ ∈ A ⊔ B := fun n hn => by
    have e1 : ⁅x, n⁆ = (x * n * x⁻¹) * n⁻¹ := by simp only [commutatorElement_def]
    rw [e1]
    exact (A ⊔ B).mul_mem (Subgroup.mem_sup_right (hbmem n hn))
      (Subgroup.mem_sup_left (A.inv_mem hn))
  have hcL : ⁅x, l⁆ ∈ L := by
    have e1 : ⁅x, l⁆ = (x * l * x⁻¹) * l⁻¹ := by simp only [commutatorElement_def]
    rw [e1]
    refine L.mul_mem ?_ (L.inv_mem hl)
    have := conj_mem_conjSubgroup x hl
    rwa [hxL] at this
  have hker : ∀ u ∈ A, ⁅x, u⁆ = 1 → u = 1 := by
    intro u hu h1
    have hu' : x * u * x⁻¹ = u := by
      simp only [commutatorElement_def] at h1
      rw [mul_inv_eq_one] at h1
      exact h1
    have : u ∈ A ⊓ B := ⟨hu, by rw [← hu']; exact hbmem u hu⟩
    rw [hAB, Subgroup.mem_bot] at this
    exact this
  have hcne : ∀ n ∈ A, n ≠ 1 → ⁅x, n⁆ ≠ 1 := fun n hn hn1 h1 => hn1 (hker n hn h1)
  have hcinj : ∀ n ∈ A, ∀ m ∈ A, ⁅x, n⁆ = ⁅x, m⁆ → n = m := by
    intro n hn m hm hnm
    have hnN : n ∈ N := hAN hn
    have hmN : m ∈ N := hAN hm
    have h1 : ⁅x, m * m⁻¹⁆ = ⁅x, m⁆ * ⁅x, m⁻¹⁆ := comm_mul_comm hN hxN hmN (N.inv_mem hmN)
    have hinv : ⁅x, m⁻¹⁆ = (⁅x, m⁆)⁻¹ := by
      have h0 : ⁅x, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
      rw [mul_inv_cancel, h0] at h1
      exact eq_inv_of_mul_eq_one_right h1.symm
    have h2 : ⁅x, n * m⁻¹⁆ = ⁅x, n⁆ * ⁅x, m⁻¹⁆ := comm_mul_comm hN hxN hnN (N.inv_mem hmN)
    rw [hinv, hnm, mul_inv_cancel] at h2
    have h3 := hker (n * m⁻¹) (A.mul_mem hn (A.inv_mem hm)) h2
    exact mul_inv_eq_one.1 h3
  have hdisj : ∀ z, z ∈ L → z ∈ A ⊔ B → z = 1 := fun z hz hzAB => by
    have : z ∈ L ⊓ (A ⊔ B) := ⟨hz, hzAB⟩
    rw [hLAB, Subgroup.mem_bot] at this
    exact this
  have i1 : ⁅x, l⁆ ≠ 1 := by
    intro h1
    apply hxl
    simp only [commutatorElement_def] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have i13 : ⁅x, e⁆ ≠ ⁅x, l⁆ := fun h =>
    i1 (hdisj _ hcL (h ▸ hcA e he))
  have i23 : ⁅x, e'⁆ ≠ ⁅x, l⁆ := fun h =>
    i1 (hdisj _ hcL (h ▸ hcA e' he'))
  have i123 : ⁅x, l⁆ ≠ ⁅x, e⁆ * ⁅x, e'⁆ := fun h =>
    i1 (hdisj _ hcL (h ▸ (A ⊔ B).mul_mem (hcA e he) (hcA e' he')))
  exact false_of_three_commutators hP hTc hLc hTx hx hx1 hxD hx2 hN hLN hxN hLnot (hAN he)
    (hAN he') (hLN hl) (hcne e he he1) (hcne e' he' he'1) i1
    (fun h => hee' (hcinj e he e' he' h)) i13 i23 i123

end CFSG.CGT.T75R
