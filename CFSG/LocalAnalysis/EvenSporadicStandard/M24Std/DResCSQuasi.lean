module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSA6

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup
open scoped commutatorElement

theorem central_of_card_three {Q : Type} [Group Q] (hP : commutator Q = ⊤) {Z : Subgroup Q}
    [Z.Normal] (hZ : Nat.card Z = 3) : ∀ g : Q, ∀ x ∈ Z, g * x = x * g := by
  classical
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  intro g0 x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  have hxo : orderOf x = 3 := by
    have hd : orderOf x ∣ 3 := hZ ▸ Subgroup.orderOf_dvd_natCard Z hx
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hz : zpowers x = Z := by
    refine eq_of_le_of_card_ge (zpowers_le.2 hx) ?_
    rw [Nat.card_zpowers, hxo, hZ]
  have hmem : ∀ y ∈ Z, y = 1 ∨ y = x ∨ y = x⁻¹ := by
    intro y hy
    rw [← hz] at hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← zpow_mod_orderOf, hxo]
    have : (k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) := by omega
    rcases this with h | h | h
    · left; simp [h]
    · right; left; simp [h]
    · right; right
      simp only [Nat.cast_ofNat, h]
      have : x ^ (3 : ℕ) = 1 := hxo ▸ pow_orderOf_eq_one x
      calc x ^ (2 : ℤ) = x ^ (2 : ℕ) := by norm_cast
        _ = x⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact this
  have hx3 : x ≠ x⁻¹ := by
    intro h
    have h2 : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel x
    have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
    rw [hxo] at this
    omega
  have hconj : ∀ g : Q, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹ := by
    intro g
    have hmem' : g * x * g⁻¹ ∈ Z := Normal.conj_mem inferInstance x hx g
    rcases hmem _ hmem' with h | h | h
    · have h' : g * x = g := mul_inv_eq_one.1 h
      exact absurd (mul_left_cancel (h'.trans (mul_one g).symm)) hx1
    · exact Or.inl h
    · exact Or.inr h
  let ε : Q →* ℤˣ :=
    { toFun := fun g => if g * x * g⁻¹ = x then 1 else -1
      map_one' := by simp
      map_mul' := by
        intro g h
        have hgh : (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group
        show (if (g * h) * x * (g * h)⁻¹ = x then (1 : ℤˣ) else -1) =
          (if g * x * g⁻¹ = x then 1 else -1) * (if h * x * h⁻¹ = x then 1 else -1)
        rcases hconj g with hg | hg <;> rcases hconj h with hh | hh
        · have e : (g * h) * x * (g * h)⁻¹ = x := by rw [hgh, hh, hg]
          simp only [e, hg, hh, ite_true, mul_one]
        · have e : (g * h) * x * (g * h)⁻¹ = x⁻¹ := by
            rw [hgh, hh]
            calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
              _ = x⁻¹ := by rw [hg]
          simp only [e, hg, hh, eq_false hx3.symm, ite_true, ite_false, one_mul]
        · have e : (g * h) * x * (g * h)⁻¹ = x⁻¹ := by rw [hgh, hh, hg]
          simp only [e, hg, hh, eq_false hx3.symm, ite_true, ite_false, mul_one]
        · have e : (g * h) * x * (g * h)⁻¹ = x := by
            rw [hgh, hh]
            calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
              _ = x := by rw [hg, inv_inv]
          simp only [e, hg, hh, eq_false hx3.symm, ite_true, ite_false, mul_neg, neg_neg, mul_one] }
  have hker : commutator Q ≤ ε.ker := Abelianization.commutator_subset_ker ε
  rw [hP] at hker
  have h1 : ε g0 = 1 := hker (mem_top g0)
  have h2 : g0 * x * g0⁻¹ = x := by
    by_contra hne
    have : ε g0 = -1 := by simp [ε, hne]
    rw [this] at h1
    exact absurd h1 (by decide)
  calc g0 * x = g0 * x * g0⁻¹ * g0 := by group
    _ = x * g0 := by rw [h2]

section Quasi

variable {Y : Type} [Group Y]

structure QuasiData (K0 Z : Subgroup Y) (π : K0 →* alternatingGroup (Fin 6)) : Prop where
  perfect : ⁅K0, K0⁆ = K0
  Z_le : Z ≤ K0
  card_Z : Nat.card Z = 3
  surj : Function.Surjective π
  ker : ∀ g : K0, π g = 1 ↔ (g : Y) ∈ Z

namespace QuasiData

variable {K0 Z : Subgroup Y} {π : K0 →* alternatingGroup (Fin 6)} (h : QuasiData K0 Z π)
include h

theorem commutator_eq_top : commutator K0 = ⊤ :=
  Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 h.perfect)

theorem subgroupOf_eq_ker : Z.subgroupOf K0 = π.ker := by
  ext g
  rw [mem_subgroupOf, MonoidHom.mem_ker, h.ker]

theorem central : ∀ g ∈ K0, ∀ x ∈ Z, g * x = x * g := by
  have hn : (Z.subgroupOf K0).Normal := h.subgroupOf_eq_ker ▸ MonoidHom.normal_ker π
  have hcard : Nat.card (Z.subgroupOf K0) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Z_le).toEquiv, h.card_Z]
  intro g hg x hx
  have := central_of_card_three h.commutator_eq_top hcard ⟨g, hg⟩ ⟨x, h.Z_le hx⟩
    (mem_subgroupOf.2 hx)
  exact congrArg Subtype.val this

theorem dichotomy {N : Subgroup Y} (hNK : N ≤ K0) (hN : ∀ g ∈ K0, ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    N ≤ Z ∨ N = K0 := by
  have hnorm : (N.subgroupOf K0).Normal := ⟨fun n hn g => mem_subgroupOf.2 (hN g g.2 n
    (mem_subgroupOf.1 hn))⟩
  have hmap : (N.subgroupOf K0).map π = ⊥ ∨ (N.subgroupOf K0).map π = ⊤ := by
    have : ((N.subgroupOf K0).map π).Normal := hnorm.map π h.surj
    exact alt6_hsimple _ this
  rcases hmap with h0 | h1
  · left
    intro n hn
    have hmem : π ⟨n, hNK hn⟩ ∈ (N.subgroupOf K0).map π :=
      ⟨⟨n, hNK hn⟩, mem_subgroupOf.2 hn, rfl⟩
    rw [h0, mem_bot] at hmem
    exact (h.ker _).1 hmem
  · right
    refine le_antisymm hNK ?_
    have hprod : ∀ g ∈ K0, ∃ n ∈ N, ∃ x ∈ Z, g = n * x := by
      intro g hg
      have hmem : π ⟨g, hg⟩ ∈ (N.subgroupOf K0).map π := by rw [h1]; trivial
      obtain ⟨m, hm, hmg⟩ := hmem
      refine ⟨m, mem_subgroupOf.1 hm, (m : Y)⁻¹ * g, ?_, by group⟩
      have : π (m⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hmg, inv_mul_cancel]
      exact (h.ker _).1 this
    rw [← h.perfect]
    refine commutator_le.2 fun g hg g' hg' => ?_
    obtain ⟨n, hn, x, hx, rfl⟩ := hprod g hg
    obtain ⟨n', hn', x', hx', rfl⟩ := hprod g' hg'
    have h1 : x * n' = n' * x := (h.central n' (hNK hn') x hx).symm
    have h4 : x' * n⁻¹ = n⁻¹ * x' := (h.central _ (K0.inv_mem (hNK hn)) x' hx').symm
    have h5 : x * x' * x⁻¹ = x' := by
      have := h.central x' (h.Z_le hx') x hx
      calc x * x' * x⁻¹ = x' * x * x⁻¹ := by rw [← this]
        _ = x' := by group
    have e : ⁅n * x, n' * x'⁆ = ⁅n, n'⁆ := by
      simp only [commutatorElement_def]
      calc n * x * (n' * x') * (n * x)⁻¹ * (n' * x')⁻¹
          = n * (x * n') * x' * x⁻¹ * n⁻¹ * x'⁻¹ * n'⁻¹ := by group
        _ = n * (n' * x) * x' * x⁻¹ * n⁻¹ * x'⁻¹ * n'⁻¹ := by rw [h1]
        _ = n * n' * (x * x' * x⁻¹) * n⁻¹ * x'⁻¹ * n'⁻¹ := by group
        _ = n * n' * x' * n⁻¹ * x'⁻¹ * n'⁻¹ := by rw [h5]
        _ = n * n' * (x' * n⁻¹) * x'⁻¹ * n'⁻¹ := by group
        _ = n * n' * (n⁻¹ * x') * x'⁻¹ * n'⁻¹ := by rw [h4]
        _ = n * n' * n⁻¹ * n'⁻¹ := by group
    rw [e]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn hn') (N.inv_mem hn)) (N.inv_mem hn')

end QuasiData

end Quasi

end CFSG.EvenSporadicStandard.M24Std.DRes
