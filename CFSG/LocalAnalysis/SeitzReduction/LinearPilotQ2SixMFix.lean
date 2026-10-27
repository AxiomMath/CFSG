module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveMFix
public import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G : Type*} [Group G]

section Involution

variable {W X : Subgroup G}

theorem card_inf_centralizer_eq_of_mul_self [Finite G] {y : G} {b : ℕ}
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ w ∈ W, w * w = 1)
    (hWc : Nat.card W = b * b) (hXW : X ≤ normalizer (W : Set G))
    (hbig : ∀ U : Subgroup G, U ≤ W → X ≤ normalizer (U : Set G) → U ≠ ⊥ → b ≤ Nat.card U)
    (hy : y ∈ normalizer (W : Set G)) (hy2 : y * y ∈ centralizer (W : Set G))
    (hXy : ∀ x ∈ X, x * y * x⁻¹ * y⁻¹ ∈ centralizer (W : Set G))
    (hyW : ¬ W ≤ centralizer ({y} : Set G)) :
    Nat.card (W ⊓ centralizer ({y} : Set G) : Subgroup G) = b := by
  have hcard := card_inf_centralizer_mul_card_range hW hW2 hy
  have hRle := map_range_commConjHom_le hW hy hy2
  have hRne : (commConjHom hW hy).range.map W.subtype ≠ ⊥ := by
    intro h
    apply hyW
    intro w hw
    have hmem : (commConjHom hW hy ⟨w, hw⟩ : G) ∈ (commConjHom hW hy).range.map W.subtype :=
      ⟨_, ⟨⟨w, hw⟩, rfl⟩, rfl⟩
    rw [h, mem_bot] at hmem
    exact (commConjHom_eq_one_iff hW hW2 hy ⟨w, hw⟩).1 (Subtype.ext hmem)
  have hRb := hbig _ (hRle.trans inf_le_left) (le_normalizer_map_range_commConjHom hW hy hXW hXy)
    hRne
  have hCR : Nat.card ((commConjHom hW hy).range.map W.subtype) ≤
      Nat.card (W ⊓ centralizer ({y} : Set G) : Subgroup G) := Subgroup.card_le_of_le hRle
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, zero_mul] at hWc
      exact absurd hWc Nat.card_pos.ne'
    · exact h
  rw [hWc] at hcard
  have h1 := Nat.mul_le_mul_left (Nat.card (W ⊓ centralizer ({y} : Set G) : Subgroup G)) hRb
  rw [hcard] at h1
  have h2 : Nat.card (W ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ b :=
    Nat.le_of_mul_le_mul_right h1 hb0
  omega

theorem inf_centralizer_le_of_commute_of_mul_self [Finite G] {y y' : G} {b : ℕ}
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ w ∈ W, w * w = 1)
    (hWc : Nat.card W = b * b) (hb1 : b ≠ 1) (hXW : X ≤ normalizer (W : Set G))
    (hbig : ∀ U : Subgroup G, U ≤ W → X ≤ normalizer (U : Set G) → U ≠ ⊥ → b ≤ Nat.card U)
    (hy : y ∈ normalizer (W : Set G)) (hy2 : y * y ∈ centralizer (W : Set G))
    (hXy : ∀ x ∈ X, x * y * x⁻¹ * y⁻¹ ∈ centralizer (W : Set G))
    (hyW : ¬ W ≤ centralizer ({y} : Set G))
    (hy' : y' ∈ normalizer (W : Set G)) (hy'2 : y' * y' ∈ centralizer (W : Set G))
    (hXy' : ∀ x ∈ X, x * y' * x⁻¹ * y'⁻¹ ∈ centralizer (W : Set G))
    (hyy' : y * y' * y⁻¹ * y'⁻¹ ∈ centralizer (W : Set G)) :
    W ⊓ centralizer ({y} : Set G) ≤ W ⊓ centralizer ({y'} : Set G) := by
  set U := W ⊓ centralizer ({y} : Set G) with hU
  have hUb : Nat.card U = b :=
    card_inf_centralizer_eq_of_mul_self hW hW2 hWc hXW hbig hy hy2 hXy hyW
  have hy'U : y' ∈ normalizer (U : Set G) := by
    apply mem_normalizer_of_conj_mem_finite
    intro u hu
    obtain ⟨huW, huy⟩ := mem_inf.1 hu
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 hy' u).1 huW, ?_⟩
    rw [mem_centralizer_singleton_iff] at huy ⊢
    have hu' : y' * u * y'⁻¹ ∈ W := (mem_normalizer_iff.1 hy' u).1 huW
    have hc : (y' * u * y'⁻¹) * (y * y' * y⁻¹ * y'⁻¹) =
        (y * y' * y⁻¹ * y'⁻¹) * (y' * u * y'⁻¹) := mem_centralizer_iff.1 hyy' _ hu'
    have hyuy : y⁻¹ * u * y = u := by
      calc y⁻¹ * u * y = y⁻¹ * (u * y) := by group
        _ = y⁻¹ * (y * u) := by rw [huy]
        _ = u := by group
    calc y' * u * y'⁻¹ * y
        = (y' * u * y'⁻¹) * (y * y' * y⁻¹ * y'⁻¹) * (y' * y * y'⁻¹) := by group
      _ = (y * y' * y⁻¹ * y'⁻¹) * (y' * u * y'⁻¹) * (y' * y * y'⁻¹) := by rw [hc]
      _ = y * y' * (y⁻¹ * u * y) * y'⁻¹ := by group
      _ = y * y' * u * y'⁻¹ := by rw [hyuy]
      _ = y * (y' * u * y'⁻¹) := by group
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    hW a (mem_inf.1 ha).1 b (mem_inf.1 hb).1
  have hU2 : ∀ u ∈ U, u * u = 1 := fun u hu => hW2 u (mem_inf.1 hu).1
  have hy'2U : y' * y' ∈ centralizer (U : Set G) :=
    centralizer_le (fun x hx => (mem_inf.1 hx).1) hy'2
  have hcardU := card_inf_centralizer_mul_card_range hUc hU2 hy'U
  have hRle := map_range_commConjHom_le hUc hy'U hy'2U
  have hne : U ⊓ centralizer ({y'} : Set G) ≠ ⊥ := by
    intro h
    rw [h] at hRle hcardU
    rw [le_bot_iff.1 hRle, card_bot, hUb] at hcardU
    exact hb1 (by omega)
  have hXU' : X ≤ normalizer ((U ⊓ centralizer ({y'} : Set G) : Subgroup G) : Set G) := by
    have heq : U ⊓ centralizer ({y'} : Set G) =
        (W ⊓ centralizer ({y} : Set G)) ⊓ (W ⊓ centralizer ({y'} : Set G)) := by
      rw [hU]
      ext g
      simp only [mem_inf]
      tauto
    rw [heq]
    exact le_normalizer_inf_of_le_normalizer_both
      (le_normalizer_inf_centralizer_singleton_of_comm hXW hXy)
      (le_normalizer_inf_centralizer_singleton_of_comm hXW hXy')
  have hb := hbig _ (inf_le_left.trans inf_le_left) hXU' hne
  have heq : U ⊓ centralizer ({y'} : Set G) = U :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hUb]; exact hb)
  intro g hg
  have hg' : g ∈ U ⊓ centralizer ({y'} : Set G) := heq.symm ▸ hg
  exact mem_inf.2 ⟨(mem_inf.1 hg).1, (mem_inf.1 hg').2⟩

theorem exists_le_centralizer_of_chain_of_mul_self [Finite G] {ι : Type*} {b : ℕ}
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ w ∈ W, w * w = 1)
    (hWc : Nat.card W = b * b) (hb1 : b ≠ 1) (hXW : X ≤ normalizer (W : Set G))
    (hbig : ∀ U : Subgroup G, U ≤ W → X ≤ normalizer (U : Set G) → U ≠ ⊥ → b ≤ Nat.card U)
    (y : ι → G) (hy : ∀ i, y i ∈ normalizer (W : Set G))
    (hy2 : ∀ i, y i * y i ∈ centralizer (W : Set G))
    (hXy : ∀ i, ∀ x ∈ X, x * y i * x⁻¹ * (y i)⁻¹ ∈ centralizer (W : Set G))
    (hyW : ∀ i, ¬ W ≤ centralizer ({y i} : Set G)) (R : ι → ι → Prop)
    (hR : ∀ i j, R i j → y i * y j * (y i)⁻¹ * (y j)⁻¹ ∈ centralizer (W : Set G))
    (hconn : ∀ i j, ∃ k, R i k ∧ R k j) (i₀ : ι) :
    ∃ U : Subgroup G, U ≤ W ∧ Nat.card U = b ∧ ∀ i, U ≤ centralizer ({y i} : Set G) := by
  refine ⟨W ⊓ centralizer ({y i₀} : Set G), inf_le_left,
    card_inf_centralizer_eq_of_mul_self hW hW2 hWc hXW hbig (hy i₀) (hy2 i₀) (hXy i₀) (hyW i₀),
    fun j => ?_⟩
  obtain ⟨k, hik, hkj⟩ := hconn i₀ j
  have h1 := inf_centralizer_le_of_commute_of_mul_self hW hW2 hWc hb1 hXW hbig (hy i₀) (hy2 i₀)
    (hXy i₀) (hyW i₀) (hy k) (hy2 k) (hXy k) (hR i₀ k hik)
  have h2 := inf_centralizer_le_of_commute_of_mul_self hW hW2 hWc hb1 hXW hbig (hy k) (hy2 k)
    (hXy k) (hyW k) (hy j) (hy2 j) (hXy j) (hR k j hkj)
  exact (h1.trans h2).trans inf_le_right

end Involution

section Bound

variable {U X M : Subgroup G}

theorem dvd_factorial_of_card_eq_mul [Finite G] (hXU : X ≤ normalizer (U : Set G))
    (hM : X ⊓ centralizer (U : Set G) ≤ M) {a : ℕ} (hcard : Nat.card X = a * Nat.card M) :
    a ∣ (Nat.card U - 1).factorial := by
  have hker : (conjPermNeOne hXU).ker.map X.subtype = X ⊓ centralizer (U : Set G) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine mem_inf.2 ⟨x.2, mem_centralizer_iff.2 fun u hu => ?_⟩
      by_cases hu1 : (⟨u, hu⟩ : U) = 1
      · have hu1' : u = 1 := congrArg Subtype.val hu1
        rw [hu1', one_mul, mul_one]
      · have h1 := congrArg (fun σ : Equiv.Perm {u : U // u ≠ 1} =>
          (((σ ⟨⟨u, hu⟩, hu1⟩ : {u : U // u ≠ 1}) : U) : G)) (MonoidHom.mem_ker.1 hx)
        have h2 : (x : G) * u * (x : G)⁻¹ = u := h1
        calc u * x = (x : G) * u * (x : G)⁻¹ * x := by rw [h2]
          _ = x * u := by group
    · intro hg
      obtain ⟨hgX, hgC⟩ := mem_inf.1 hg
      refine ⟨⟨g, hgX⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
      ext u
      show g * u * g⁻¹ = u
      rw [← mem_centralizer_iff.1 hgC u u.1.2, mul_inv_cancel_right]
  have h1 := Subgroup.card_ker_mul_card_range (conjPermNeOne hXU)
  have h2 : Nat.card (conjPermNeOne hXU).range ∣ (Nat.card U - 1).factorial := by
    have h := Subgroup.card_subgroup_dvd_card (conjPermNeOne hXU).range
    rwa [Nat.card_perm, natCard_subtype_ne_one] at h
  have h3 : Nat.card (conjPermNeOne hXU).ker ∣ Nat.card M := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, hker]
    exact Subgroup.card_dvd_of_le hM
  obtain ⟨d, hd⟩ := h3
  have hkpos : 0 < Nat.card (conjPermNeOne hXU).ker := Nat.card_pos
  have h4 : Nat.card (conjPermNeOne hXU).range = a * d := by
    apply Nat.eq_of_mul_eq_mul_left hkpos
    rw [h1, hcard, hd]
    ring
  exact (Dvd.intro d h4.symm).trans h2

theorem succ_le_of_prime_dvd_of_dvd_factorial {p a k : ℕ} (hp : p.Prime) (hpa : p ∣ a)
    (h : a ∣ (k - 1).factorial) : p + 1 ≤ k := by
  have h1 := (Nat.Prime.dvd_factorial hp).1 (hpa.trans h)
  have h2 := hp.two_le
  omega

theorem thirty_two_le_of_dvd_factorial {k : ℕ} (h : 9999360 ∣ (k - 1).factorial) : 32 ≤ k :=
  succ_le_of_prime_dvd_of_dvd_factorial (by norm_num) (by norm_num) h

theorem sixteen_le_of_dvd_factorial {k : ℕ} (hk : k ∣ 2 ^ 8) (h : 20160 ∣ (k - 1).factorial) :
    16 ≤ k := by
  have h1 : 20160 ≤ (k - 1).factorial := Nat.le_of_dvd (Nat.factorial_pos _) h
  have h9 : 9 ≤ k := nine_le_of_le_factorial h1
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk
  rcases Nat.lt_or_ge j 4 with hj4 | hj4
  · have h8 : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h8
    omega
  · calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj4

end Bound

end CFSG.SeitzReduction.LinearPilot
