module

public import CFSG.GH74.GLS.Stage4.T2NegDefs
public import CFSG.GH74.GLS.Stage4.T6Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem t5_transport_neg {G : Type} [Group G] [Finite G] (hIVK : IVK_4_1_R_U3) {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {z y : G} {K₂ J : Subgroup G}
    (hJy : J ≤ centralizer ({y} : Set G)) (hKJ : K₂ ≤ J)
    (hJ : IsSLnEps 3 ↥J (-1) (p ^ n) ∨ IsLnEps 3 ↥J (-1) (p ^ n))
    (hz2 : orderOf z = 2) (hzK : z ∈ K₂) (hzc : ∀ x ∈ K₂, z * x = x * z)
    {X : Subgroup G} (hXK : X ≤ K₂) (hXp : IsPGroup p ↥X) (hXc : Nat.card ↥X = p ^ n) :
    ∃ R : Subgroup G, IsPGroup p ↥R ∧ X ≤ R ∧ R ≤ centralizer (X : Set G) ∧
      Nat.card ↥R = (p ^ n) ^ 3 ∧ (∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ∈ X) ∧ X ≤ ⁅R, R⁆ ∧
      (∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ X) ∧ (∀ r ∈ R, z * r * z⁻¹ * r ∈ X) ∧
      (∀ r ∈ R, y * r = r * y) := by
  have hXJ : X ≤ J := hXK.trans hKJ
  have hzJ : z ∈ J := hKJ hzK
  let z' : ↥J := ⟨z, hzJ⟩
  have hz'2 : orderOf z' = 2 := by
    rw [← hz2]
    exact Subgroup.orderOf_mk z hzJ
  have hX'c : X.subgroupOf J ≤ centralizer ({z'} : Set ↥J) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply Subtype.ext
    exact hzc x (hXK (Subgroup.mem_subgroupOf.1 hx))
  have hX'p : IsPGroup p ↥(X.subgroupOf J) := hXp.comap_subtype (K := J)
  have hX'card : Nat.card ↥(X.subgroupOf J) = p ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXJ).toEquiv, hXc]
  obtain ⟨R', -, hR'p, hXR', hR'c, hR'card, hZ, hcom1, hcom2, hinv⟩ :=
    hIVK ↥J p n hp hp2 hJ z' hz'2 (X.subgroupOf J) hX'c hX'p hX'card
  have hmapX : (X.subgroupOf J).map J.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXJ
  have hinj : Function.Injective J.subtype := J.subtype_injective
  refine ⟨R'.map J.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine IsPGroup.of_card (n := 3 * n) ?_
    rw [Subgroup.card_map_of_injective hinj, hR'card, ← pow_mul, mul_comm]
  · rw [← hmapX]
    exact Subgroup.map_mono hXR'
  · rintro _ ⟨r', hr', rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [← hmapX] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    have := (Subgroup.mem_centralizer_iff.1 (hR'c hr')) x' hx'
    exact congrArg Subtype.val this
  · rw [Subgroup.card_map_of_injective hinj, hR'card]
  · rintro _ ⟨r', hr', rfl⟩ hcomm
    have : r' ∈ X.subgroupOf J := by
      refine hZ r' hr' (fun s' hs' => ?_)
      exact Subtype.ext (hcomm _ ⟨s', hs', rfl⟩)
    exact Subgroup.mem_subgroupOf.1 this
  · rw [← hmapX, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hcom1
  · rintro _ ⟨r', hr', rfl⟩ _ ⟨s', hs', rfl⟩
    have := hcom2 r' hr' s' hs'
    exact Subgroup.mem_subgroupOf.1 this
  · rintro _ ⟨r', hr', rfl⟩
    have := hinv r' hr'
    exact Subgroup.mem_subgroupOf.1 this
  · rintro _ ⟨r', hr', rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hJy r'.2)).symm

theorem t5_tsing_of_J_neg {G : Type} [Group G] [Finite G] (hIVK : IVK_4_1_R_U3) {p q : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ∃ n : ℕ, q = p ^ n) {z y : G} {Ky K J : Subgroup G}
    (hyK : y ∈ Ky) (hyz : y ∉ Subgroup.zpowers z) (hnp : ¬ p ∣ orderOf y)
    (hJy : J ≤ centralizer ({y} : Set G)) (hKJ : K ≤ J)
    (hJ : IsSLnEps 3 ↥J (-1) q ∨ IsLnEps 3 ↥J (-1) q) (hz2 : orderOf z = 2) (hzK : z ∈ K)
    (hzc : ∀ x ∈ K, z * x = x * z) : Ch6TSing p q z Ky K := by
  obtain ⟨n, hn⟩ := hpq
  refine ⟨y, hyK, hyz, hnp, ?_⟩
  intro X hXK hXp hXc
  have hJ' : IsSLnEps 3 ↥J (-1) (p ^ n) ∨ IsLnEps 3 ↥J (-1) (p ^ n) := by rw [← hn]; exact hJ
  have hXc' : Nat.card ↥X = p ^ n := by rw [hXc, hn]
  obtain ⟨R, hRp, hXR, hRc, hRcard, hRZ, hRcom1, hRcom2, hRinv, hRy⟩ :=
    t5_transport_neg hIVK hp hp2 hJy hKJ hJ' hz2 hzK hzc hXK hXp hXc'
  exact ⟨R, hRp, hXR, hRc, by rw [hRcard, hn], hRZ, hRcom1, hRcom2, hRinv, hRy⟩

end CFSG.GH74.GLS.Stage4.Rest
