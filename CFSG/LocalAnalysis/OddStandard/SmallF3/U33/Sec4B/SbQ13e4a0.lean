module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private lemma subgroupOfNormal {P' N' : Subgroup G}
    (hN : ∀ p ∈ P', ∀ n ∈ N', p * n * p⁻¹ ∈ N') : (N'.subgroupOf P').Normal :=
  ⟨fun n hn p => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN p.1 p.2 n.1 hn⟩

private lemma aux_inv_mul_mem {P' N' : Subgroup G}
    (hN : ∀ p ∈ P', ∀ n ∈ N', p * n * p⁻¹ ∈ N')
    {a b : G} (ha : a ∈ P') (hb : b ∈ P') (h : a * b⁻¹ ∈ N') : a⁻¹ * b ∈ N' := by
  have h1 : a⁻¹ * (a * b⁻¹) * a ∈ N' := by
    simpa using hN a⁻¹ (P'.inv_mem ha) (a * b⁻¹) h
  have h2 : b⁻¹ * a ∈ N' := by simpa [mul_assoc] using h1
  have h3 : (b⁻¹ * a)⁻¹ ∈ N' := N'.inv_mem h2
  simpa [mul_inv_rev] using h3

private lemma aux_mul_inv_mem {P' N' : Subgroup G}
    (hN : ∀ p ∈ P', ∀ n ∈ N', p * n * p⁻¹ ∈ N')
    {a b : G} (ha : a ∈ P') (hb : b ∈ P') (h : a⁻¹ * b ∈ N') : a * b⁻¹ ∈ N' := by
  have h1 : b * (a⁻¹ * b) * b⁻¹ ∈ N' := hN b hb (a⁻¹ * b) h
  have h2 : b * a⁻¹ ∈ N' := by simpa [mul_assoc] using h1
  have h3 : (b * a⁻¹)⁻¹ ∈ N' := N'.inv_mem h2
  simpa [mul_inv_rev] using h3

private noncomputable def homMod {K P' N' : Subgroup G} [hNq : (N'.subgroupOf P').Normal]
    {φ : G → G}
    (hφ : ∀ k ∈ K, φ k ∈ P') (hN : ∀ p ∈ P', ∀ n ∈ N', p * n * p⁻¹ ∈ N')
    (hmul : ∀ k ∈ K, ∀ k' ∈ K, φ (k * k') * (φ k * φ k')⁻¹ ∈ N') :
    ↥K →* ↥P' ⧸ N'.subgroupOf P' :=
  MonoidHom.mk' (fun k => (QuotientGroup.mk (⟨φ k.1, hφ k.1 k.2⟩ : ↥P') :
      ↥P' ⧸ N'.subgroupOf P')) (fun k k' => by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact aux_inv_mul_mem hN (hφ (k.1 * k'.1) (K.mul_mem k.2 k'.2))
      (P'.mul_mem (hφ k.1 k.2) (hφ k'.1 k'.2)) (hmul k.1 k.2 k'.1 k'.2))

private lemma homMod_apply {K P' N' : Subgroup G} [hNq : (N'.subgroupOf P').Normal] {φ : G → G}
    (hφ : ∀ k ∈ K, φ k ∈ P') (hN : ∀ p ∈ P', ∀ n ∈ N', p * n * p⁻¹ ∈ N')
    (hmul : ∀ k ∈ K, ∀ k' ∈ K, φ (k * k') * (φ k * φ k')⁻¹ ∈ N') (k : ↥K) :
    homMod hφ hN hmul k
      = (QuotientGroup.mk (⟨φ k.1, hφ k.1 k.2⟩ : ↥P') : ↥P' ⧸ N'.subgroupOf P') := rfl

private lemma homMod_ker_eq {K H P' N' : Subgroup G} [hNq : (N'.subgroupOf P').Normal]
    {φ : G → G}
    (hφ : ∀ k ∈ K, φ k ∈ P') (hN : ∀ p ∈ P', ∀ n ∈ N', p * n * p⁻¹ ∈ N')
    (hmul : ∀ k ∈ K, ∀ k' ∈ K, φ (k * k') * (φ k * φ k')⁻¹ ∈ N')
    (hker : ∀ k ∈ K, φ k ∈ N' ↔ k ∈ H) :
    (homMod hφ hN hmul).ker = H.subgroupOf K := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, homMod_apply]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hker k.1 k.2

private lemma homMod_range_eq_top {K P' N' : Subgroup G} [hNq : (N'.subgroupOf P').Normal]
    {φ : G → G}
    (hφ : ∀ k ∈ K, φ k ∈ P') (hN : ∀ p ∈ P', ∀ n ∈ N', p * n * p⁻¹ ∈ N')
    (hmul : ∀ k ∈ K, ∀ k' ∈ K, φ (k * k') * (φ k * φ k')⁻¹ ∈ N')
    (hsurj : ∀ p ∈ P', ∃ k ∈ K, φ k * p⁻¹ ∈ N') :
    (homMod hφ hN hmul).range = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  rcases QuotientGroup.mk_surjective x with ⟨p, rfl⟩
  rw [MonoidHom.mem_range]
  rcases hsurj p.1 p.2 with ⟨k, hkK, hk⟩
  refine ⟨⟨k, hkK⟩, ?_⟩
  rw [homMod_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact aux_inv_mul_mem hN (hφ k hkK) p.2 hk

private lemma two_mul_card_range_le_of_not_mem {K P' N' : Subgroup G}
    [hNq : (N'.subgroupOf P').Normal]
    {φ : G → G}
    (hφ : ∀ k ∈ K, φ k ∈ P') (hN : ∀ p ∈ P', ∀ n ∈ N', p * n * p⁻¹ ∈ N')
    (hmul : ∀ k ∈ K, ∀ k' ∈ K, φ (k * k') * (φ k * φ k')⁻¹ ∈ N')
    {c : G} (hc : c ∈ P') (hcK : ∀ k ∈ K, φ k * c⁻¹ ∉ N') :
    2 * Nat.card (homMod hφ hN hmul).range ≤ Nat.card (↥P' ⧸ N'.subgroupOf P') := by
  have hcnot : QuotientGroup.mk (⟨c, hc⟩ : ↥P') ∉ (homMod hφ hN hmul).range := by
    rw [MonoidHom.mem_range]
    rintro ⟨k, hk⟩
    have h1 : (⟨φ k.1, hφ k.1 k.2⟩ : ↥P')⁻¹ * ⟨c, hc⟩ ∈ N'.subgroupOf P' := by
      rw [← QuotientGroup.eq, ← homMod_apply]
      exact hk
    rw [Subgroup.mem_subgroupOf] at h1
    exact hcK k.1 k.2 (aux_mul_inv_mem hN (hφ k.1 k.2) hc h1)
  have htop : (homMod hφ hN hmul).range ≠ ⊤ := by
    intro h
    exact hcnot (h ▸ Subgroup.mem_top _)
  have hidx : 1 < (homMod hφ hN hmul).range.index :=
    Subgroup.one_lt_index_of_ne_top htop
  have h2 : 2 ≤ (homMod hφ hN hmul).range.index := hidx
  calc
    2 * Nat.card (homMod hφ hN hmul).range
        = Nat.card (homMod hφ hN hmul).range * 2 := Nat.mul_comm _ _
    _ ≤ Nat.card (homMod hφ hN hmul).range * (homMod hφ hN hmul).range.index :=
          Nat.mul_le_mul_left _ h2
    _ = Nat.card (↥P' ⧸ N'.subgroupOf P') :=
          Subgroup.card_mul_index ((homMod hφ hN hmul).range)

theorem q13e_card_mul_le_of_hom_mod {K H P' N' : Subgroup G} {φ : G → G} (hHK : H ≤ K)
    (hNP : N' ≤ P') (hN : ∀ p ∈ P', ∀ n ∈ N', p * n * p⁻¹ ∈ N') (hφ : ∀ k ∈ K, φ k ∈ P')
    (hmul : ∀ k ∈ K, ∀ k' ∈ K, φ (k * k') * (φ k * φ k')⁻¹ ∈ N')
    (hker : ∀ k ∈ K, φ k ∈ N' ↔ k ∈ H) :
    Nat.card K * Nat.card N' ≤ Nat.card P' * Nat.card H := by
  haveI hNq : (N'.subgroupOf P').Normal := subgroupOfNormal hN
  have hker_eq : (homMod hφ hN hmul).ker = H.subgroupOf K :=
    homMod_ker_eq hφ hN hmul hker
  have hcard_ker : Nat.card (homMod hφ hN hmul).ker = Nat.card H := by
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have hcard_range : Nat.card (homMod hφ hN hmul).range
      ≤ Nat.card (↥P' ⧸ N'.subgroupOf P') :=
    Subgroup.card_le_card_group ((homMod hφ hN hmul).range)
  have hcard_N' : Nat.card (N'.subgroupOf P') = Nat.card N' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  have hK : Nat.card K = Nat.card H * Nat.card (homMod hφ hN hmul).range := by
    rw [← Subgroup.card_ker_mul_card_range (homMod hφ hN hmul), hcard_ker]
  have hP : Nat.card P' = Nat.card (↥P' ⧸ N'.subgroupOf P') * Nat.card N' := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N'.subgroupOf P'), hcard_N']
  rw [hK, hP]
  have h1 : Nat.card (homMod hφ hN hmul).range * Nat.card N'
      ≤ Nat.card (↥P' ⧸ N'.subgroupOf P') * Nat.card N' :=
    Nat.mul_le_mul_right _ hcard_range
  calc
    (Nat.card H * Nat.card (homMod hφ hN hmul).range) * Nat.card N'
        = (Nat.card (homMod hφ hN hmul).range * Nat.card N') * Nat.card H := by ring
    _ ≤ (Nat.card (↥P' ⧸ N'.subgroupOf P') * Nat.card N') * Nat.card H :=
          Nat.mul_le_mul_right _ h1

theorem q13e_card_mul_eq_of_hom_mod {K H P' N' : Subgroup G} {φ : G → G} (hHK : H ≤ K)
    (hNP : N' ≤ P') (hN : ∀ p ∈ P', ∀ n ∈ N', p * n * p⁻¹ ∈ N') (hφ : ∀ k ∈ K, φ k ∈ P')
    (hmul : ∀ k ∈ K, ∀ k' ∈ K, φ (k * k') * (φ k * φ k')⁻¹ ∈ N') (hker : ∀ k ∈ K, φ k ∈ N' ↔ k ∈ H)
    (hsurj : ∀ p ∈ P', ∃ k ∈ K, φ k * p⁻¹ ∈ N') :
    Nat.card K * Nat.card N' = Nat.card P' * Nat.card H := by
  haveI hNq : (N'.subgroupOf P').Normal := subgroupOfNormal hN
  have hker_eq : (homMod hφ hN hmul).ker = H.subgroupOf K :=
    homMod_ker_eq hφ hN hmul hker
  have hcard_ker : Nat.card (homMod hφ hN hmul).ker = Nat.card H := by
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have htop : (homMod hφ hN hmul).range = ⊤ :=
    homMod_range_eq_top hφ hN hmul hsurj
  have hcard_range : Nat.card (homMod hφ hN hmul).range
      = Nat.card (↥P' ⧸ N'.subgroupOf P') := by
    rw [htop, Subgroup.card_top]
  have hcard_N' : Nat.card (N'.subgroupOf P') = Nat.card N' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  have hK : Nat.card K = Nat.card H * Nat.card (homMod hφ hN hmul).range := by
    rw [← Subgroup.card_ker_mul_card_range (homMod hφ hN hmul), hcard_ker]
  have hP : Nat.card P' = Nat.card (↥P' ⧸ N'.subgroupOf P') * Nat.card N' := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N'.subgroupOf P'), hcard_N']
  rw [hK, hP, hcard_range]
  ring

theorem q13e_two_mul_card_mul_le_of_hom_mod {K H P' N' : Subgroup G} {φ : G → G} (hHK : H ≤ K)
    (hNP : N' ≤ P') (hN : ∀ p ∈ P', ∀ n ∈ N', p * n * p⁻¹ ∈ N') (hφ : ∀ k ∈ K, φ k ∈ P')
    (hmul : ∀ k ∈ K, ∀ k' ∈ K, φ (k * k') * (φ k * φ k')⁻¹ ∈ N') (hker : ∀ k ∈ K, φ k ∈ N' ↔ k ∈ H)
    {c : G} (hc : c ∈ P') (hcK : ∀ k ∈ K, φ k * c⁻¹ ∉ N') :
    2 * (Nat.card K * Nat.card N') ≤ Nat.card P' * Nat.card H := by
  haveI hNq : (N'.subgroupOf P').Normal := subgroupOfNormal hN
  have hker_eq : (homMod hφ hN hmul).ker = H.subgroupOf K :=
    homMod_ker_eq hφ hN hmul hker
  have hcard_ker : Nat.card (homMod hφ hN hmul).ker = Nat.card H := by
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have h2range : 2 * Nat.card (homMod hφ hN hmul).range
      ≤ Nat.card (↥P' ⧸ N'.subgroupOf P') :=
    two_mul_card_range_le_of_not_mem hφ hN hmul hc hcK
  have hcard_N' : Nat.card (N'.subgroupOf P') = Nat.card N' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  have hK : Nat.card K = Nat.card H * Nat.card (homMod hφ hN hmul).range := by
    rw [← Subgroup.card_ker_mul_card_range (homMod hφ hN hmul), hcard_ker]
  have hP : Nat.card P' = Nat.card (↥P' ⧸ N'.subgroupOf P') * Nat.card N' := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N'.subgroupOf P'), hcard_N']
  rw [hK, hP]
  have h1 : (2 * Nat.card (homMod hφ hN hmul).range) * Nat.card N'
      ≤ Nat.card (↥P' ⧸ N'.subgroupOf P') * Nat.card N' :=
    Nat.mul_le_mul_right _ h2range
  calc
    2 * ((Nat.card H * Nat.card (homMod hφ hN hmul).range) * Nat.card N')
        = (2 * Nat.card (homMod hφ hN hmul).range) * (Nat.card H * Nat.card N') := by ring
    _ = ((2 * Nat.card (homMod hφ hN hmul).range) * Nat.card N') * Nat.card H := by ring
    _ ≤ (Nat.card (↥P' ⧸ N'.subgroupOf P') * Nat.card N') * Nat.card H :=
          Nat.mul_le_mul_right _ h1

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
