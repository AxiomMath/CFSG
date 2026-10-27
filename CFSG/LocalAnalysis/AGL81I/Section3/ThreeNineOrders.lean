module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporReduce
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberTits

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem index_dvd_div_of_dvd_card {G : Type*} [Group G] [Finite G] {Y : Subgroup G} {a : ℕ}
    (ha : a ∣ Nat.card Y) : Y.index ∣ Nat.card G / a := by
  obtain ⟨b, hb⟩ := ha
  have ha0 : 0 < a := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hb
    exact (Nat.card_pos (α := Y)).ne' hb
  have h := Y.card_mul_index
  rw [hb, mul_assoc] at h
  rw [← h, Nat.mul_div_cancel_left _ ha0]
  exact Dvd.intro_left b rfl

namespace ThreeNineHyp

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {p d : ℕ}

theorem index_facts (h : ThreeNineHyp K E D X₁ p d) (hZ : Subgroup.center ↥K = ⊥)
    (hp : ¬ p ∣ Nat.card (Outer ↥K)) (hd : ¬ d ∣ Nat.card (Outer ↥K)) :
    X₁.subgroupOf K ≠ ⊤ ∧ (X₁.subgroupOf K).index ≡ 1 [MOD p] ∧
      (X₁.subgroupOf K).index ≡ 1 [MOD d] ∧
      p ^ (Nat.card ↥K).factorization p ∣ Nat.card (X₁.subgroupOf K) ∧
      d ^ (Nat.card ↥K).factorization d ∣ Nat.card (X₁.subgroupOf K) ∧ d ∣ Nat.card ↥K := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  set Y : Subgroup ↥K := X₁.subgroupOf K with hYdef
  have hYtop : Y ≠ ⊤ := by
    intro htop
    apply h.not_K_le
    intro x hx
    have : (⟨x, hx⟩ : ↥K) ∈ Y := htop ▸ Subgroup.mem_top _
    exact this
  obtain ⟨Eb, hEb, -, -, hN⟩ := h.exists_barE hZ hp
  obtain ⟨T, hT⟩ := (CFSG.Open.IsElemAbelian.isPGroup hEb).exists_le_sylow
  have hNT : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ Y := hN T T.isPGroup' hT
  have hmodp := index_modEq_one_of_normalizer_le T hNT
  have hTY : (T : Subgroup ↥K) ≤ Y := Subgroup.le_normalizer.trans hNT
  have hTc : Nat.card (T : Subgroup ↥K) = p ^ (Nat.card ↥K).factorization p :=
    Sylow.card_eq_multiplicity T
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ hd
  have hDsylK : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ K) K :=
    h.sylow.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  rw [inf_eq_left.mpr hDK] at hDsylK
  have hDcard := hDsylK.card_eq
  let SD : Sylow d ↥K := Sylow.ofCard (D.subgroupOf K) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hDcard])
  have hND : Subgroup.normalizer ((SD : Subgroup ↥K) : Set ↥K) ≤ Y := by
    intro n hn
    have hn' : n ∈ Subgroup.normalizer ((D.subgroupOf K : Subgroup ↥K) : Set ↥K) := hn
    rw [← Subgroup.subgroupOf_normalizer_eq hDK] at hn'
    exact h.normalizer_inf_le_of_le_D le_rfl h.D_ne_bot ⟨hn', le_sup_left (a := K) n.2⟩
  have hmodd := index_modEq_one_of_normalizer_le SD hND
  have hDY : (SD : Subgroup ↥K) ≤ Y := Subgroup.le_normalizer.trans hND
  have hSDc : Nat.card (SD : Subgroup ↥K) = d ^ (Nat.card ↥K).factorization d :=
    Sylow.card_eq_multiplicity SD
  refine ⟨hYtop, hmodp, hmodd, ?_, ?_, ?_⟩
  · rw [← hTc]
    exact Subgroup.card_dvd_of_le hTY
  · rw [← hSDc]
    exact Subgroup.card_dvd_of_le hDY
  · by_contra hnd
    rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero] at hDcard
    exact h.D_ne_bot (Subgroup.card_eq_one.mp hDcard)

end ThreeNineHyp

end CFSG.LocalAnalysis.AGL81I.Section3
