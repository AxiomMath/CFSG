module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover

public section

namespace CFSG.GH74.Generic.S45.LAlt

open Equiv Equiv.Perm Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {P : Type*} [Group P]

theorem ker_eq_bot_of_sq_eq_one [Finite P] [Group.IsPerfect P] {m : ℕ} (hm : 3 ≤ m)
    (η : P →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center P) (hK2 : IsPGroup 2 η.ker) {x : Fin m → P}
    (hxη : ∀ i, η (x i) = altThreeCycle i) (hx3 : ∀ i, x i ^ 3 = 1)
    (hz : (x ⟨0, by omega⟩ * x ⟨1, by omega⟩) ^ 2 = 1) : η.ker = ⊥ := by
  classical
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hL : Subgroup.closure (Set.range x) = ⊤ := by
    have hmap : (Subgroup.closure (Set.range x)).map η = ⊤ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      have : η ∘ x = altThreeCycle := funext hxη
      rw [this, closure_altThreeCycle]
    have hsup : Subgroup.closure (Set.range x) ⊔ η.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central
      (Subgroup.closure (Set.range x)) η.ker hK
    rw [hsup, ← commutator_def, Group.IsPerfect.commutator_eq_top] at h
    exact eq_top_iff.mpr (h.le.trans (Subgroup.commutator_le_self _))
  have hzij : ∀ i j, i ≠ j → (x i * x j) ^ 2 = 1 := fun i j hij =>
    (lift_sq_eq η hη hK hK2 hxη hx3 hij h01).trans hz
  have hbound := card_closure_le_of_carmichael m x hx3 hzij
  rw [hL, Subgroup.card_top] at hbound
  have hP2 : Nat.card P = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup η.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
  have hA : Nat.card (alternatingGroup (Fin (m + 2))) = (m + 2).factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hApos : 0 < (m + 2).factorial / 2 := by
    rw [← hA]
    exact Nat.card_pos
  have hle : Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker ≤
      Nat.card (alternatingGroup (Fin (m + 2))) * 1 := by
    rw [← hP2, hA, mul_one]
    exact hbound
  have hk1 : Nat.card η.ker ≤ 1 := Nat.le_of_mul_le_mul_left hle (hA ▸ hApos)
  exact Subgroup.card_eq_one.1 (le_antisymm hk1 Nat.card_pos)

theorem sq_ne_one_of_lift_swap_mul_swap [Finite P] [Group.IsPerfect P] {n : ℕ} (hn : 6 ≤ n)
    (η : P →* alternatingGroup (Fin n)) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center P) (hK2 : IsPGroup 2 η.ker) (hne : η.ker ≠ ⊥)
    {x : P} {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d)
    (hx : ((η x : alternatingGroup (Fin n)) : Perm (Fin n)) = swap a b * swap c d) :
    x ^ 2 ≠ 1 := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 4 ≤ m := by omega
  intro hx2
  have hker2 : Nat.card η.ker ≤ 2 :=
    alternating_perfect_central_two_kernel_order_at_most_two (by omega) η hη hK hK2
  have hlift : ∀ i : Fin m, ∃ x : P, η x = altThreeCycle i ∧ x ^ 3 = 1 := fun i => by
    obtain ⟨y, hy⟩ := hη (altThreeCycle i)
    obtain ⟨x, hx, hx3⟩ := exists_lift_pow_three_eq_one hK hK2
      (by rw [hy]; exact altThreeCycle_pow_three i)
    exact ⟨x, hx.trans hy, hx3⟩
  choose xs hxsη hxs3 using hlift
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have hnd1 : [(0 : Fin (m + 2)), i₀.addNat 2, 1, i₁.addNat 2].Nodup := by
    simp [i₀, i₁, Fin.ext_iff, Fin.addNat]
  have hnd2 : [a, b, c, d].Nodup := by
    simp [hab, hac, had, hbc, hbd, hcd]
  have hct1 : ((altThreeCycle i₀ * altThreeCycle i₁ : alternatingGroup (Fin (m + 2))) :
      Perm (Fin (m + 2))).cycleType = {2, 2} := by
    rw [coe_altThreeCycle_mul h01]
    exact cycleType_swap_mul_swap_of_nodup hnd1
  have hct2 : ((η x : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2))).cycleType = {2, 2} := by
    rw [hx]
    exact cycleType_swap_mul_swap_of_nodup hnd2
  have hconj : IsConj (altThreeCycle i₀ * altThreeCycle i₁) (η x) :=
    alternatingGroup.isConj_of (isConj_iff_cycleType_eq.2 (hct1.trans hct2.symm)) (by
      rw [← sum_cycleType, hct1, Fintype.card_fin]
      simp
      omega)
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  obtain ⟨h, rfl⟩ := hη g
  have hw : η (h * (xs i₀ * xs i₁) * h⁻¹) = η x := by
    rw [map_mul, map_mul, map_inv, map_mul, hxsη, hxsη]
    exact hg
  have hζ : x⁻¹ * (h * (xs i₀ * xs i₁) * h⁻¹) ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hw, inv_mul_cancel]
  have hζ2 : (x⁻¹ * (h * (xs i₀ * xs i₁) * h⁻¹)) ^ 2 = 1 := by
    have hcard := pow_card_eq_one' (G := η.ker) (x := ⟨_, hζ⟩)
    have hpos : 0 < Nat.card η.ker := Nat.card_pos
    interval_cases hc : Nat.card η.ker
    · have := congrArg Subtype.val hcard
      simp only [pow_one] at this
      change (x⁻¹ * (h * (xs i₀ * xs i₁) * h⁻¹)) = 1 at this
      rw [this, one_pow]
    · exact congrArg Subtype.val hcard
  set w : P := h * (xs i₀ * xs i₁) * h⁻¹ with hwdef
  have hwx : w = x * (x⁻¹ * w) := by group
  have hcomm : Commute x (x⁻¹ * w) := Subgroup.mem_center_iff.mp (hK hζ) x
  have hw2 : w ^ 2 = 1 := by
    rw [hwx, hcomm.mul_pow, hx2, hζ2, one_mul]
  have hz : (xs i₀ * xs i₁) ^ 2 = 1 := by
    have : w ^ 2 = h * (xs i₀ * xs i₁) ^ 2 * h⁻¹ := by
      rw [hwdef]
      simp only [pow_two]
      group
    rw [this] at hw2
    have h3 : (xs i₀ * xs i₁) ^ 2 = h⁻¹ * (h * (xs i₀ * xs i₁) ^ 2 * h⁻¹) * h := by group
    rw [h3, hw2]
    group
  exact hne (ker_eq_bot_of_sq_eq_one (by omega) η hη hK hK2 hxsη hxs3 hz)

end CFSG.GH74.Generic.S45.LAlt
