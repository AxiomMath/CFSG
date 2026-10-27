module

import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.Sec85a
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.StrongClosure

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem conjSub_le_and_le_normalizer [Finite G] {D K : Subgroup G} {g : G} (hKD : K ≤ D)
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    conjSub g K ≤ D ∧ D ≤ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
  refine ⟨fun z hz => ?_, fun y hy => mem_normalizer_of_conj_le fun z hz => ?_⟩
  · have h1 := hKD (mem_conjSub.mp hz)
    simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp h1
  · rw [mem_conjSub] at hz ⊢
    have hgy : g * y * g⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hDK hgy)) _).mp hz
    have e : g * (y⁻¹ * z * y) * g⁻¹ =
        (g * y * g⁻¹)⁻¹ * (g * z * g⁻¹) * (g * y * g⁻¹)⁻¹⁻¹ := by group
    rw [e]
    exact h1

omit [Finite G] in
theorem inf_eq_bot_of_involutions [Finite G] {K K' : Subgroup G} (hK : IsPGroup 2 K) {c c' : G}
    (hc : ∀ k ∈ K, k ^ 2 = 1 → k = 1 ∨ k = c) (hc' : ∀ k ∈ K', k ^ 2 = 1 → k = 1 ∨ k = c')
    (hcc : c ≠ c') : K ⊓ K' = ⊥ := by
  by_contra hne
  obtain ⟨t, ⟨htK, htK'⟩, ht1, ht2⟩ := exists_involution (hK.to_le inf_le_left) hne
  exact hcc (((hc t htK ht2).resolve_left ht1).symm.trans ((hc' t htK' ht2).resolve_left ht1))

omit [Finite G] in
theorem commute_of_inf_eq_bot {D K K' : Subgroup G} (hKD : K ≤ D) (hK'D : K' ≤ D)
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hDK' : D ≤ Subgroup.normalizer (K' : Set G))
    (hKK' : K ⊓ K' = ⊥) {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K') : k * k' = k' * k := by
  have h1 : k * k' * k⁻¹ * k'⁻¹ ∈ K ⊓ K' := by
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hDK (hK'D hk')) k⁻¹).mp (K.inv_mem hk)
      simpa [mul_assoc] using K.mul_mem hk this
    · exact K'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hDK' (hKD hk)) k').mp hk')
        (K'.inv_mem hk')
  rw [hKK', Subgroup.mem_bot] at h1
  calc k * k' = (k * k' * k⁻¹ * k'⁻¹) * (k' * k) := by group
    _ = k' * k := by rw [h1, one_mul]

omit [Finite G] in
theorem card_mul_card_le [Finite G] {D K K' : Subgroup G} (hKD : K ≤ D) (hK'D : K' ≤ D)
    (hKK' : K ⊓ K' = ⊥) : Nat.card K * Nat.card K' ≤ Nat.card D := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun k => ⟨(k.1 : G) * k.2, D.mul_mem (hKD k.1.2)
    (hK'D k.2.2)⟩) fun k k' hkk' => ?_
  have h : (k.1 : G) * k.2 = k'.1 * k'.2 := congrArg Subtype.val hkk'
  have hm : (k'.1 : G)⁻¹ * k.1 = k'.2 * (k.2 : G)⁻¹ := by
    calc (k'.1 : G)⁻¹ * k.1 = (k'.1 : G)⁻¹ * (k.1 * k.2) * (k.2 : G)⁻¹ := by group
      _ = (k'.1 : G)⁻¹ * (k'.1 * k'.2) * (k.2 : G)⁻¹ := by rw [h]
      _ = k'.2 * (k.2 : G)⁻¹ := by group
  have h1 : (k'.1 : G)⁻¹ * k.1 ∈ K ⊓ K' :=
    ⟨K.mul_mem (K.inv_mem k'.1.2) k.1.2, hm ▸ K'.mul_mem k'.2.2 (K'.inv_mem k.2.2)⟩
  rw [hKK', Subgroup.mem_bot] at h1
  have e1 : (k.1 : G) = k'.1 := by
    calc (k.1 : G) = k'.1 * ((k'.1 : G)⁻¹ * k.1) := by group
      _ = k'.1 := by rw [h1, mul_one]
  have e2 : (k.2 : G) = k'.2 := by
    rw [e1] at h
    exact mul_left_cancel h
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

end CFSG.Goldschmidt.Sec8
