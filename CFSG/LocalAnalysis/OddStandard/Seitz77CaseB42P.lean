module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27PAct

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

section P42

variable {G : Type} [Group G] [Finite G] {A R P : Subgroup G}

theorem PStruct27.R_le (hP : PStruct27 A R P) (hRA : R ≤ A) : R ≤ P := by
  have hex : ∃ p ∈ P, ∃ r ∈ R, p * r * p⁻¹ ≠ r := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ p : ↥P, conjAct27 R P hP.le_norm p = 1 := by
      intro p
      ext w
      rw [coe_conjAct27]
      exact hcon p p.2 w w.2
    have hrange : (conjAct27 R P hP.le_norm).range = ⊥ := by
      rw [eq_bot_iff]
      rintro g ⟨p, rfl⟩
      rw [hall p]
      exact Subgroup.one_mem _
    have h60 := hP.card
    rw [hrange] at h60
    simp at h60
  obtain ⟨p, hp, r, hr, hne⟩ := hex
  have hpr : p * r * p⁻¹ ∈ R := (mem_normalizer_iff.mp (hP.le_norm hp) r).mp hr
  have hrc : r ∈ normalizer (A : Set G) ⊓ normalizer (R : Set G) :=
    ⟨le_normalizer (hRA hr), le_normalizer hr⟩
  have hrp : r * p⁻¹ * r⁻¹ ∈ P := hP.char r hrc p⁻¹ (P.inv_mem hp)
  have hxP : p * r * p⁻¹ * r⁻¹ ∈ P := by
    have := P.mul_mem hp hrp
    simpa [mul_assoc] using this
  have hxR : p * r * p⁻¹ * r⁻¹ ∈ R := R.mul_mem hpr (R.inv_mem hr)
  have hx1 : p * r * p⁻¹ * r⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  intro s hs
  by_cases hs1 : s = 1
  · rw [hs1]
    exact P.one_mem
  · obtain ⟨p', hp', hps⟩ := hP.trans _ hxR s hs hx1 hs1
    rw [← hps]
    exact P.mul_mem (P.mul_mem hp' hxP) (P.inv_mem hp')

theorem PStruct27.sixtyFour_dvd_card (hP : PStruct27 A R P) (hRA : R ≤ A)
    (hRab : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r) (hRcard : Nat.card R = 16) :
    64 ∣ Nat.card P := by
  have hRP : R ≤ P := hP.R_le hRA
  have hmul := Subgroup.card_ker_mul_card_range (conjAct27 R P hP.le_norm)
  have hker : R.subgroupOf P ≤ (conjAct27 R P hP.le_norm).ker := by
    intro p hp
    rw [MonoidHom.mem_ker]
    ext w
    rw [coe_conjAct27]
    have hpR : (p : G) ∈ R := hp
    have h1 : (p : G) * (w : G) = (w : G) * (p : G) := hRab _ hpR _ w.2
    calc (p : G) * w * (p : G)⁻¹ = w * p * (p : G)⁻¹ := by rw [h1]
      _ = w := by simp
      _ = ((1 : MulAut ↥R) w : G) := rfl
  have hcardR : Nat.card (R.subgroupOf P) = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRP).toEquiv).trans hRcard
  have h16 : 16 ∣ Nat.card (conjAct27 R P hP.le_norm).ker := by
    rw [← hcardR]
    exact Subgroup.card_dvd_of_le hker
  obtain ⟨k, hk⟩ := h16
  refine ⟨15 * k, ?_⟩
  rw [← hmul, hk, hP.card]
  ring

theorem PStruct27.le_of_sylow (hP : PStruct27 A R P) (hRA : R ≤ A)
    (hRab : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r) (hRcard : Nat.card R = 16) {V : Subgroup G}
    (hV : IsSylowOf 2 V A) (hVcard : Nat.card V = 64) (hVR : V ≤ normalizer (R : Set G)) :
    V ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPQ : P ≤ A ⊓ normalizer (R : Set G) := le_inf hP.le_A hP.le_norm
  have hQP : A ⊓ normalizer (R : Set G) ≤ normalizer (P : Set G) :=
    Subgroup.le_normalizer_iff.mpr fun c hc p hp =>
      hP.char c ⟨le_normalizer hc.1, hc.2⟩ p hp
  have hVQ : IsSylowOf 2 V (A ⊓ normalizer (R : Set G)) :=
    hV.of_le (le_inf hV.le hVR) inf_le_left
  have hVP : IsSylowOf 2 (V ⊓ P) P := hVQ.inf_of_le_normalizer hPQ hQP
  have hcard := hVP.card_eq
  have h64 : 2 ^ 6 ∣ Nat.card P := by
    have := hP.sixtyFour_dvd_card hRA hRab hRcard
    norm_num
    exact this
  have hpos : Nat.card P ≠ 0 := Nat.card_pos.ne'
  have hfac : 6 ≤ (Nat.card P).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hpos).mp h64
  have hge : Nat.card V ≤ Nat.card ↥(V ⊓ P) := by
    rw [hcard, hVcard]
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (Nat.card P).factorization 2 := Nat.pow_le_pow_right (by norm_num) hfac
  have heq : V ⊓ P = V := Subgroup.eq_of_le_of_card_ge inf_le_left hge
  exact inf_eq_left.mp heq

end P42

end CFSG.OddStandard.Seitz77
