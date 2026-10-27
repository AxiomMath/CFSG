module

public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableSwap

public section

namespace CFSG.QuasithinUnique.A5.Insp

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.Uniqueness.SU.SU1

section Index

variable {G : Type} [Group G]

theorem le_normalizer_of_relIndex_le_two [Finite G] {N X : Subgroup G} (hNX : N ≤ X)
    (h : N.relIndex X ≤ 2) : X ≤ Subgroup.normalizer (N : Set G) := by
  have hne : N.relIndex X ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h1 : N.relIndex X = 1 ∨ N.relIndex X = 2 := by omega
  rcases h1 with h1 | h2
  · have hXN : X ≤ N := Subgroup.relIndex_eq_one.mp h1
    have : N = X := le_antisymm hNX hXN
    rw [this]
    exact Subgroup.le_normalizer
  · exact DoubleA3.k32_le_normalizer_of_index_two hNX h2

theorem sq_mem_of_relIndex_le_two [Finite G] {N X : Subgroup G} (hNX : N ≤ X)
    (h : N.relIndex X ≤ 2) {g : G} (hg : g ∈ X) : g * g ∈ N := by
  have hnorm : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr (le_normalizer_of_relIndex_le_two hNX h)
  have hmem := Subgroup.pow_index_mem (N.subgroupOf X) (⟨g, hg⟩ : ↥X)
  have hidx : (N.subgroupOf X).index = 1 ∨ (N.subgroupOf X).index = 2 := by
    have hne : (N.subgroupOf X).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have : (N.subgroupOf X).index ≤ 2 := h
    omega
  have h2 : (⟨g, hg⟩ : ↥X) ^ 2 ∈ N.subgroupOf X := by
    rcases hidx with h1 | h2
    · rw [h1, pow_one] at hmem
      rw [pow_two]
      exact (N.subgroupOf X).mul_mem hmem hmem
    · rwa [h2] at hmem
  have := Subgroup.mem_subgroupOf.mp h2
  simpa [pow_two] using this

theorem mem_of_pow_three [Finite G] {N X : Subgroup G} (hNX : N ≤ X) (h : N.relIndex X ≤ 2) {c : G}
    (hc : c ∈ X) (hc3 : c ^ 3 = 1) : c ∈ N := by
  have h1 : c * c ∈ N := sq_mem_of_relIndex_le_two hNX h hc
  have e : c = (c * c) * (c * c) := by
    have h3 : c * c * c = 1 := by rw [← pow_three']; exact hc3
    calc c = c * (c * c * c) := by rw [h3, mul_one]
      _ = (c * c) * (c * c) := by group
  rw [e]
  exact N.mul_mem h1 h1

end Index

section Klein

variable {G : Type} [Group G]

theorem klein_cases [Finite G] {V : Subgroup G} (hV4 : Nat.card V = 4) {v₁ v₂ : G} (h₁ : v₁ ∈ V)
    (h₂ : v₂ ∈ V) (hsq₁ : v₁ * v₁ = 1) (h11 : v₁ ≠ 1) (h21 : v₂ ≠ 1) (h12 : v₁ ≠ v₂) :
    ∀ v ∈ V, v = 1 ∨ v = v₁ ∨ v = v₂ ∨ v = v₁ * v₂ := by
  classical
  have hfin : Fintype ↥V := Fintype.ofFinite _
  have hv₁ : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right hsq₁
  set a : ↥V := ⟨v₁, h₁⟩ with ha
  set b : ↥V := ⟨v₂, h₂⟩ with hb
  set S : Finset ↥V := {1, a, b, a * b} with hS
  have h1a : (1 : ↥V) ≠ a := fun h => h11 (congrArg Subtype.val h).symm
  have h1b : (1 : ↥V) ≠ b := fun h => h21 (congrArg Subtype.val h).symm
  have h1ab : (1 : ↥V) ≠ a * b := by
    intro h
    have h' : v₁ * v₂ = 1 := congrArg Subtype.val h.symm
    have : v₂ = v₁⁻¹ := eq_inv_of_mul_eq_one_right h'
    exact h12 (by rw [this, hv₁])
  have hab : a ≠ b := fun h => h12 (congrArg Subtype.val h)
  have haab : a ≠ a * b := by
    intro h
    have h' : v₁ = v₁ * v₂ := congrArg Subtype.val h
    exact h21 (by simpa using h'.symm)
  have hbab : b ≠ a * b := by
    intro h
    have h' : v₂ = v₁ * v₂ := congrArg Subtype.val h
    exact h11 (by simpa using h'.symm)
  have hcard : S.card = 4 := by
    rw [hS, Finset.card_insert_of_notMem (by simp [h1a, h1b, h1ab]),
      Finset.card_insert_of_notMem (by simp [hab, haab]),
      Finset.card_insert_of_notMem (by simpa using hbab), Finset.card_singleton]
  have huniv : S = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard, ← Nat.card_eq_fintype_card, hV4]
  intro v hv
  have hmem : (⟨v, hv⟩ : ↥V) ∈ S := by rw [huniv]; exact Finset.mem_univ _
  rw [hS] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

end Klein

section Adjoin

variable {G : Type} [Group G]

theorem adjoin_involution [Finite G] {W : Subgroup G} {g : G} (hW : IsElemAbelian 2 W)
    (hg : g * g = 1) (hcomm : ∀ w ∈ W, w * g = g * w) (hgW : g ∉ W) :
    IsElemAbelian 2 (W ⊔ Subgroup.zpowers g) ∧
      Nat.card ↥(W ⊔ Subgroup.zpowers g) = 2 * Nat.card ↥W := by
  have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact hg
  have hz : IsElemAbelian 2 (Subgroup.zpowers g) := CFSG.Open.isElemAbelian_zpowers hg2
  have hcz : ∀ a ∈ W, ∀ b ∈ Subgroup.zpowers g, a * b = b * a := by
    rintro a ha _ ⟨n, rfl⟩
    exact ((Commute.zpow_right (hcomm a ha) n)).eq
  refine ⟨IsElemAbelian.sup hW hz hcz, ?_⟩
  have hg1 : g ≠ 1 := fun h => hgW (h ▸ W.one_mem)
  have hinf : W ⊓ Subgroup.zpowers g = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxW, hxz⟩
    rcases (Subgroup.mem_zpowers_iff.mp hxz) with ⟨k, rfl⟩
    have hx : g ^ k = 1 ∨ g ^ k = g := by
      have h2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg
      obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
      · left
        rw [zpow_mul, h2, one_zpow]
      · right
        rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
    rcases hx with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exact absurd (h ▸ hxW) hgW
  have hnorm : W ≤ Subgroup.normalizer (Subgroup.zpowers g : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro w hw
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hcz w hw y hy).symm
  have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hinf, Subgroup.card_bot, mul_one] at hmul
  have hz2 : Nat.card (Subgroup.zpowers g) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hg2 hg1
  rw [hmul, hz2, mul_comm]

end Adjoin

section Alt

open Equiv

theorem perm_exists_three_cent {n : ℕ} (hn : 7 ≤ n) (σ : Perm (Fin n)) (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) : ∃ g : Perm (Fin n), g ≠ 1 ∧ g ^ 3 = 1 ∧ g * σ = σ * g := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rwa [pow_two]) hσ1
  have hcyc : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 := by
    apply Multiset.eq_replicate_card.mpr
    intro x hx
    have h1 : x ∣ 2 := hord ▸ Equiv.Perm.dvd_of_mem_cycleType hx
    have h2' : 2 ≤ x := Equiv.Perm.two_le_of_mem_cycleType hx
    exact Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h1) h2'
  set m := Multiset.card σ.cycleType with hm
  have hm1 : 1 ≤ m := by
    have : σ.cycleType ≠ 0 := fun h => hσ1 (Equiv.Perm.cycleType_eq_zero.mp h)
    exact Multiset.card_pos.mpr this
  have hsum : σ.cycleType.sum = 2 * m := by
    rw [hcyc, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : 2 * m ≤ n := by
    have := Equiv.Perm.sum_cycleType_le σ
    rw [hsum, Fintype.card_fin] at this
    exact this
  have hcard := Equiv.Perm.nat_card_centralizer σ
  rw [Fintype.card_fin, hsum] at hcard
  have hprod : σ.cycleType.prod = 2 ^ m := by
    rw [hcyc, Multiset.prod_replicate]
  have hfin : ∏ k ∈ σ.cycleType.toFinset, (σ.cycleType.count k).factorial = m.factorial := by
    have : σ.cycleType.toFinset = {2} := by
      rw [hcyc]
      ext x
      simp only [Multiset.mem_toFinset, Multiset.mem_replicate, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · intro h
        exact ⟨by omega, h⟩
    rw [this, Finset.prod_singleton, hcyc, Multiset.count_replicate_self]
  rw [hprod, hfin] at hcard
  have h3 : 3 ∣ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) := by
    rw [hcard]
    by_cases hm3 : 3 ≤ m
    · exact Dvd.dvd.mul_left (Nat.dvd_factorial (by norm_num) hm3) _
    · have : 3 ≤ n - 2 * m := by omega
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Nat.dvd_factorial (by norm_num) this) _) _
  have h3p : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) 3 h3
  have hg3 : (g : Perm (Fin n)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  have hg1 : (g : Perm (Fin n)) ≠ 1 := by
    intro h
    have : g = 1 := Subtype.ext h
    rw [this, orderOf_one] at hg
    omega
  refine ⟨g, hg1, hg3, ?_⟩
  have := Subgroup.mem_centralizer_iff.mp g.2 σ (Set.mem_singleton σ)
  exact this.symm

theorem alt_exists_three_cent {n : ℕ} (hn : 7 ≤ n) (k : alternatingGroup (Fin n)) (hk2 : k * k = 1)
    (hk1 : k ≠ 1) :
    ∃ g : alternatingGroup (Fin n), g ≠ 1 ∧ g ^ 3 = 1 ∧ g * k = k * g := by
  obtain ⟨g, hg1, hg3, hgc⟩ := perm_exists_three_cent hn (k : Perm (Fin n))
    (congrArg Subtype.val hk2) (fun h => hk1 (Subtype.ext h))
  have hsign : Equiv.Perm.sign g = 1 := by
    have h : (Equiv.Perm.sign g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (by decide)
  refine ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, ?_, ?_, ?_⟩
  · intro h
    exact hg1 (congrArg Subtype.val h)
  · apply Subtype.ext
    simpa using hg3
  · apply Subtype.ext
    simpa using hgc

end Alt

end CFSG.QuasithinUnique.A5.Insp
