module

public import CFSG.GH74.GLS.Bg.TwoGroups.L27C
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

open scoped Pointwise

private theorem hyp7_of {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T) {t : T}
    (ht : orderOf t = 2) (hC : Nonempty (↥(centralizer ({t} : Set T)) ≃* E2 3))
    {α : MulAut T} (hα1 : α ≠ 1) (hα3 : ∃ n : ℕ, orderOf α = 3 ^ n) (hαt : α t = t) :
    L27.Hyp7 T t α := by
  obtain ⟨e⟩ := hC
  obtain ⟨n, hn⟩ := hα3
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht
    omega
  have hCcard : Nat.card (Subgroup.centralizer ({t} : Set T)) = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hCab : ∀ a b : T, t * a = a * t → t * b = b * t → a * b = b * a := by
    intro a b ha hb
    have ha' : a ∈ Subgroup.centralizer ({t} : Set T) := L27.mem_cent.mpr ha
    have hb' : b ∈ Subgroup.centralizer ({t} : Set T) := L27.mem_cent.mpr hb
    have h1 : e (⟨a, ha'⟩ * ⟨b, hb'⟩) = e (⟨b, hb'⟩ * ⟨a, ha'⟩) := by
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (e.injective h1)
  have hC2 : ∀ c : T, t * c = c * t → c * c = 1 := by
    intro c hc
    have hc' : c ∈ Subgroup.centralizer ({t} : Set T) := L27.mem_cent.mpr hc
    have h1 : (⟨c, hc'⟩ : ↥(Subgroup.centralizer ({t} : Set T))) * ⟨c, hc'⟩ = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      exact (by decide : ∀ x : E2 3, x * x = 1) _
    exact congrArg Subtype.val h1
  have hα3n : α ^ (3 ^ n) = 1 := by
    rw [← hn]
    exact pow_orderOf_eq_one α
  have hα3 : α ^ 3 = 1 :=
    L27.alpha_cube hT t ht2 (le_of_eq hCcard) α n hα3n hαt
  exact ⟨hT, ht2, ht1, hCab, hC2, hCcard, hα3, hα1, hαt⟩

theorem hs27_fixed {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T) {t : T}
    (ht : orderOf t = 2) (hC : Nonempty (↥(centralizer ({t} : Set T)) ≃* E2 3))
    {α : MulAut T} (hα1 : α ≠ 1) (hα3 : ∃ n : ℕ, orderOf α = 3 ^ n) (hαt : α t = t) (g : T) :
    α g = g ↔ g ∈ zpowers t := by
  have hyp := hyp7_of hT ht hC hα1 hα3 hαt
  obtain ⟨E, cfg⟩ := L27.exists_E hyp
  constructor
  · intro hg
    rcases cfg.fixed g hg with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers t
  · intro hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← hk, map_zpow, hαt]

theorem hs27_card_T {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T) {t : T}
    (ht : orderOf t = 2) (hC : Nonempty (↥(centralizer ({t} : Set T)) ≃* E2 3))
    {α : MulAut T} (hα1 : α ≠ 1) (hα3 : ∃ n : ℕ, orderOf α = 3 ^ n) (hαt : α t = t) :
    Nat.card T = 2 * Nat.card ↥(commAut α) := by
  obtain ⟨hN, hinf, hsup, -⟩ := iv2_2_7 T hT t ht hC α hα1 hα3 hαt
  haveI : (commAut α).Normal := hN
  have hdisj : Disjoint (commAut α) (zpowers t) := disjoint_iff.mpr hinf
  have hnorm : zpowers t ≤ Subgroup.normalizer (commAut α : Set T) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (commAut α) (zpowers t) hnorm hdisj
  rw [hsup, Subgroup.card_top, Nat.card_zpowers, ht, mul_comm] at hcard
  exact hcard

theorem hs27_card_cent_inter {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T) {t : T}
    (ht : orderOf t = 2) (hC : Nonempty (↥(centralizer ({t} : Set T)) ≃* E2 3))
    {α : MulAut T} (hα1 : α ≠ 1) (hα3 : ∃ n : ℕ, orderOf α = 3 ^ n) (hαt : α t = t) :
    Nat.card ↥(centralizer ({t} : Set T) ⊓ commAut α) = 4 := by
  obtain ⟨hN, hinf, hsup, -⟩ := iv2_2_7 T hT t ht hC α hα1 hα3 hαt
  have hyp := hyp7_of hT ht hC hα1 hα3 hαt
  obtain ⟨e⟩ := hC
  have hC8 : Nat.card (Subgroup.centralizer ({t} : Set T)) = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  set C := Subgroup.centralizer ({t} : Set T) with hCdef
  have hC8' : Nat.card C = 8 := by rw [hCdef]; exact hC8
  have htC : t ∈ C := by rw [hCdef]; exact L27.mem_cent.mpr rfl
  have hBle : Subgroup.zpowers t ≤ C := Subgroup.zpowers_le.mpr htC
  haveI : (commAut α).Normal := hN
  have hnormA : Subgroup.zpowers t ≤ Subgroup.normalizer (commAut α : Set T) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hset : (commAut α : Set T) * (Subgroup.zpowers t : Set T) = ⊤ := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnormA, hsup]
    rfl
  have hmod : C = (C ⊓ commAut α) ⊔ Subgroup.zpowers t := by
    apply le_antisymm
    · intro c hc
      have hmem : c ∈ (commAut α : Set T) * (Subgroup.zpowers t : Set T) := by
        rw [hset]
        exact Subgroup.mem_top c
      rcases hmem with ⟨h, hh, k, hk, hkc⟩
      have hkC : k ∈ C := hBle hk
      have hhC : h ∈ C := by
        have heq : h = c * k⁻¹ := by rw [← hkc]; group
        rw [heq]
        exact mul_mem hc (inv_mem hkC)
      rw [← hkc]
      exact mul_mem (Subgroup.mem_sup_left ⟨hhC, hh⟩) (Subgroup.mem_sup_right hk)
    · exact sup_le inf_le_left hBle
  set A := C ⊓ commAut α with hAdef
  have hdisj : Disjoint A (Subgroup.zpowers t) := by
    rw [hAdef, disjoint_iff, inf_assoc, hinf, inf_bot_eq]
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (A : Set T) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb a ha
    have hbC : b ∈ C := hBle hb
    have haC : a ∈ C := by
      have := ha
      rw [hAdef] at this
      exact this.1
    have hcomm : b * a = a * b :=
      hyp.Cab b a (L27.mem_cent.mp hbC) (L27.mem_cent.mp haC)
    rw [hcomm]
    simpa using ha
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    A (Subgroup.zpowers t) hnorm hdisj
  rw [← hmod, Nat.card_zpowers, ht, hC8'] at hcard
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
