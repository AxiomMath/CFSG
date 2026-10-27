module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveModelFacts

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.EvenSporadicStandard.RuStd

namespace FiveData

variable {G : Type} [Group G] [Finite G] (d : FiveData G)

include d

omit [Finite G] in
theorem card_zpowers_y_ne_one :
    Nat.card {z : G // z ∈ zpowers d.y ∧ z ≠ 1} = 4 := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hy1 : d.y ≠ 1 := fun h => d.y_not_mem (h ▸ one_mem _)
  have hord : orderOf d.y = 5 := orderOf_eq_prime (d.Q_exp _ d.y_mem) hy1
  have hset : {z : G | z ∈ zpowers d.y ∧ z ≠ 1} = (zpowers d.y : Set G) \ {1} := by
    ext z
    simp
  have h1 : Nat.card {z : G // z ∈ zpowers d.y ∧ z ≠ 1} =
      ((zpowers d.y : Set G) \ {1}).ncard := by
    rw [← hset, ← Nat.card_coe_set_eq]
    rfl
  rw [h1, Set.ncard_sdiff_singleton_of_mem (one_mem (zpowers d.y)), ← Nat.card_coe_set_eq]
  change Nat.card (zpowers d.y) - 1 = 4
  rw [Nat.card_zpowers, hord]

theorem count (f : G) (hf : orderOf f = 5) (hc : Nat.card (centralizer ({f} : Set G)) = 300)
    (F : Subgroup G) (hF : F ≤ centralizer ({f} : Set G)) (hcard : Nat.card F = 25) :
    Nat.card {x : G // x ∈ F ∧ x ≠ 1 ∧ Nat.card (centralizer ({x} : Set G)) = 1000} ≤ 4 := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases d.exists_conj hf with ⟨c, hz⟩ | ⟨c, hz⟩
  · exfalso
    rw [card_centralizer_eq hz, d.card_C₀] at hc
    omega
  · set φ : G →* G := (MulAut.conj c).toMonoidHom with hφ
    have hinj : Function.Injective φ := (MulAut.conj c).injective
    have hC : centralizer ({f} : Set G) = (centralizer ({d.x₁} : Set G)).map φ :=
      centralizer_eq_map hz
    set H : Subgroup G := centralizer ({f} : Set G) with hH
    set Sf : Subgroup G := d.S₁.map φ with hSf
    have hSfH : Sf ≤ H := by
      rw [hC]
      exact Subgroup.map_mono d.S₁_le_centralizer
    have hSf25 : Nat.card Sf = 25 := by
      rw [hSf, Subgroup.card_map_of_injective hinj, d.card_S₁]
    have hfac : (Nat.card H).factorization 5 = 2 := by
      rw [hc, show (300 : ℕ) = 5 ^ 2 * 12 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    let PS : Sylow 5 H := Sylow.ofCard (Sf.subgroupOf H) (by
      rw [hfac, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSfH).toEquiv, hSf25]
      norm_num)
    have hPF : IsPGroup 5 (F.subgroupOf H) := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv, hcard]
      norm_num
    obtain ⟨w, hw⟩ := exists_conj_mem_sylow PS hPF
    have key : ∀ x : G, x ∈ F → x ≠ 1 → Nat.card (centralizer ({x} : Set G)) = 1000 →
        (c⁻¹ * (w : G)) * x * (c⁻¹ * (w : G))⁻¹ ∈ zpowers d.y := by
      intro x hxF hx1 hx1000
      have h1 := hw ⟨x, hF hxF⟩ (Subgroup.mem_subgroupOf.2 hxF)
      have h2 : (w : G) * x * (w : G)⁻¹ ∈ Sf := h1
      obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 h2
      have hs' : s = (c⁻¹ * (w : G)) * x * (c⁻¹ * (w : G))⁻¹ := by
        have h3 : c * s * c⁻¹ = (w : G) * x * (w : G)⁻¹ := hsx
        calc s = c⁻¹ * (c * s * c⁻¹) * c := by group
          _ = c⁻¹ * ((w : G) * x * (w : G)⁻¹) * c := by rw [h3]
          _ = (c⁻¹ * (w : G)) * x * (c⁻¹ * (w : G))⁻¹ := by group
      rw [← hs']
      refine d.mem_zpowers_y_of_mem_S₁ hs ?_ ?_
      · intro h
        apply hx1
        rw [hs'] at h
        exact (conj_eq_one_iff).1 h
      · rw [hs', centralizer_conj, Subgroup.card_map_of_injective (MulAut.conj _).injective]
        exact hx1000
    let Φ : {x : G // x ∈ F ∧ x ≠ 1 ∧ Nat.card (centralizer ({x} : Set G)) = 1000} →
        {z : G // z ∈ zpowers d.y ∧ z ≠ 1} := fun x =>
      ⟨(c⁻¹ * (w : G)) * x.1 * (c⁻¹ * (w : G))⁻¹, key x.1 x.2.1 x.2.2.1 x.2.2.2, fun h =>
        x.2.2.1 ((conj_eq_one_iff).1 h)⟩
    have hΦ : Function.Injective Φ := by
      intro x x' h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (by simpa [Φ] using h')
    calc Nat.card {x : G // x ∈ F ∧ x ≠ 1 ∧ Nat.card (centralizer ({x} : Set G)) = 1000}
        ≤ Nat.card {z : G // z ∈ zpowers d.y ∧ z ≠ 1} := Nat.card_le_card_of_injective Φ hΦ
      _ = 4 := d.card_zpowers_y_ne_one

theorem facts : RuFiveFacts G where
  exp5 := d.exp5
  typeAB := d.typeAB
  typeA := d.typeA
  conjA := d.conjA
  typeB := d.typeB
  count := d.count

end FiveData

end CFSG.EvenSporadicStandard.RuStd.S2
