module

public import CFSG.ClassicalInvolution.Q3.Q3SBasic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

section Subnormal

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem mem_of_normal_of_not_dvd_relIndex {N M : Subgroup Y}
    (hN : (N.subgroupOf M).Normal) {p : ℕ} (hp : p.Prime) (hidx : ¬ p ∣ N.relIndex M) {x : Y}
    (hx : x ∈ M) {k : ℕ} (hk : x ^ (p ^ k) = 1) : x ∈ N := by
  have := hN
  let x' : M := ⟨x, hx⟩
  let q : M ⧸ N.subgroupOf M := QuotientGroup.mk x'
  have h1 : q ^ (p ^ k) = 1 := by
    change QuotientGroup.mk (x' ^ (p ^ k)) = 1
    have : x' ^ (p ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this]
    rfl
  have h2 : orderOf q ∣ N.relIndex M := orderOf_dvd_natCard q
  have h3 : orderOf q ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (p ^ k) (N.relIndex M) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hidx)
  have h4 : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes hcop h3 h2
  have h5 : q = 1 := orderOf_eq_one_iff.mp h4
  exact (QuotientGroup.eq_one_iff x').1 h5

omit [Finite Y] in
theorem isSubnormal_mem_of_pow_eq_one {H K : Subgroup Y} (h : IsSubnormal H K) {p : ℕ}
    (hp : p.Prime) (hidx : ¬ p ∣ H.relIndex K) {x : Y} (hxK : x ∈ K) {k : ℕ}
    (hk : x ^ (p ^ k) = 1) : x ∈ H := by
  induction h with
  | refl => exact hxK
  | @step H M K hHM hN hMK ih =>
    have hmul := Subgroup.relIndex_mul_relIndex H M K hHM (isSubnormal_le hMK)
    have hHM' : ¬ p ∣ H.relIndex M := fun hd => hidx (hmul ▸ Dvd.dvd.mul_right hd _)
    have hMK' : ¬ p ∣ M.relIndex K := fun hd => hidx (hmul ▸ Dvd.dvd.mul_left hd _)
    exact mem_of_normal_of_not_dvd_relIndex hN hp hHM' (ih hMK' hxK) hk

end Subnormal

section Witness

variable {F : Type} [Group F] [Finite F] {z : F} {L : Subgroup F}

theorem IsClassicalMember3.relIndex_centralizer_not_dvd (h : IsClassicalMember3 L z)
    (h9 : ¬ 9 ∣ Nat.card (Subgroup.centralizer ({z} : Set F))) :
    ¬ 3 ∣ L.relIndex (Subgroup.centralizer ({z} : Set F)) := by
  intro hd
  apply h9
  have hLC := h.le_centralizer
  have h1 := Subgroup.card_mul_index (L.subgroupOf (Subgroup.centralizer ({z} : Set F)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLC).toEquiv] at h1
  rw [← h1]
  obtain ⟨a, ha⟩ := h.three_dvd_card
  obtain ⟨b, hb⟩ := hd
  change 9 ∣ Nat.card L * L.relIndex (Subgroup.centralizer ({z} : Set F))
  rw [ha, hb]
  exact ⟨a * b, by ring⟩

theorem IsClassicalMember3.mem_of_pow_three_eq_one (h : IsClassicalMember3 L z)
    (h9 : ¬ 9 ∣ Nat.card (Subgroup.centralizer ({z} : Set F))) {x : F}
    (hx : x ∈ Subgroup.centralizer ({z} : Set F)) (hx3 : x ^ 3 = 1) : x ∈ L :=
  isSubnormal_mem_of_pow_eq_one h.subnormal Nat.prime_three
    (h.relIndex_centralizer_not_dvd h9) hx (k := 1) (by simpa using hx3)

@[expose] def NoWeakClassical3At {F : Type} [Group F] (z : F) : Prop :=
  ∀ L : Subgroup F, ¬ IsClassicalMember3 L z

theorem NoWeakClassical3At.of_witness
    (h9 : ¬ 9 ∣ Nat.card (Subgroup.centralizer ({z} : Set F)))
    {g₁ g₂ : F} (h₁ : g₁ ∈ Subgroup.centralizer ({z} : Set F))
    (h₂ : g₂ ∈ Subgroup.centralizer ({z} : Set F)) (hg₁ : g₁ ^ 3 = 1) (hg₂ : g₂ ^ 3 = 1)
    (ht : (g₁ * g₂) ^ 2 = 1) (ht1 : g₁ * g₂ ≠ 1) (htz : g₁ * g₂ ≠ z) :
    NoWeakClassical3At z := by
  intro L hL
  have hg₁L := hL.mem_of_pow_three_eq_one h9 h₁ hg₁
  have hg₂L := hL.mem_of_pow_three_eq_one h9 h₂ hg₂
  have ho : orderOf (g₁ * g₂) = 2 := orderOf_eq_prime ht ht1
  exact htz (hL.eq_of_orderOf_eq_two (L.mul_mem hg₁L hg₂L) ho)

end Witness

end CFSG.ClassicalInvolution.Q3
