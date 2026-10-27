module

public import CFSG.CharacterTheory.Wreathed.InvertedOddCyclingLiftSupport

public section

namespace CFSG.Wreathed

variable {M : Type*} [Group M] [Finite M]

theorem full_base_four_group_action_has_inverted_odd_cycling_lift (n : ℕ) (hn : 2 ≤ n)
    (m : ℕ) (hm : m = 2 ^ n) (s t : M) (hs : orderOf s = m) (ht : orderOf t = m)
    (hst : Commute s t) (hdisj : Disjoint (Subgroup.zpowers s) (Subgroup.zpowers t))
    (U : Subgroup M) (_hU : U = Subgroup.zpowers s ⊔ Subgroup.zpowers t)
    (V : Subgroup M) (hV : V = Subgroup.closure {s ^ (m / 2), t ^ (m / 2)}) [V.Normal]
    (K : Subgroup M) [K.Normal] (_hK : Odd (Nat.card K))
    (_hCV : Subgroup.centralizer (V : Set M) = K ⊔ U)
    (hsurj : Function.Surjective (MulAut.conjNormal : M →* MulAut V))
    (w : M) (hw : orderOf w = 2) (hws : w⁻¹ * s * w = t) (_hwt : w⁻¹ * t * w = s) :
    ∃ b : ℕ, 1 ≤ b ∧ ∃ a : M, orderOf a = 3 ^ b ∧
      (∀ v ∈ V, v ≠ 1 → a * v * a⁻¹ ≠ v) ∧ (∀ v ∈ V, a ^ 3 * v * (a ^ 3)⁻¹ = v) ∧
      w⁻¹ * a * w = a⁻¹ ∧
      Subgroup.closure ((Subgroup.centralizer (V : Set M) : Set M) ∪ {w, a}) = ⊤ := by
  have hm4 : 4 ≤ m := by
    rw [hm]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2m : 2 ∣ m := by
    rw [hm]
    exact dvd_pow_self 2 (by omega)
  have hm2 : m / 2 ∣ m := Nat.div_dvd_of_dvd h2m
  have hm20 : m / 2 ≠ 0 := by omega
  have hxo : orderOf (s ^ (m / 2)) = 2 := by
    rw [orderOf_pow_of_dvd hm20 (hs ▸ hm2), hs, Nat.div_div_self h2m (by omega)]
  have hyo : orderOf (t ^ (m / 2)) = 2 := by
    rw [orderOf_pow_of_dvd hm20 (ht ▸ hm2), ht, Nat.div_div_self h2m (by omega)]
  have hxy : s ^ (m / 2) ≠ t ^ (m / 2) := by
    intro h
    have h1 : s ^ (m / 2) = 1 := Subgroup.disjoint_def.mp hdisj
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers s) _)
      (h ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers t) _)
    rw [h1, orderOf_one] at hxo
    omega
  have hVK : IsKleinFour V := by
    rw [hV]
    exact isKleinFour_closure_pair hxo hyo (hst.pow_pow _ _)
      (hdisj.mono (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers s) _))
        (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers t) _)))
  have hw2 : w * w = 1 := by
    rw [← sq, ← hw]
    exact pow_orderOf_eq_one w
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwx : w * s ^ (m / 2) * w⁻¹ = t ^ (m / 2) := by
    rw [← hws, ← conj_pow, hwinv]
  have hxV : s ^ (m / 2) ∈ V := by
    rw [hV]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  obtain ⟨b, hb, a, ha, hfix, hcube, hinv, hgen⟩ :=
    exists_inverted_odd_cycling_of_surjective V hsurj w hw
      ⟨s ^ (m / 2), hxV, by rw [hwx]; exact Ne.symm hxy⟩
  refine ⟨b, hb, a, ha, hfix, hcube, ?_, hgen⟩
  rw [hwinv] at hinv ⊢
  exact hinv

end CFSG.Wreathed
