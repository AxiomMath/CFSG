module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentDef
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentShape
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentHopf
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentPull
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentCentral
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentCover

public section

namespace CFSG.OddStandard.HigherRank.F3.Ident

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

section Helpers

theorem exists_two_element_lift {P R : Type} [Group P] [Finite P] [Group R] (ρ : P →* R)
    (hρ : Function.Surjective ρ) {r : R} (hr : r ^ 2 = 1) :
    ∃ x : P, (∃ a : ℕ, orderOf x = 2 ^ a) ∧ ρ x = r := by
  obtain ⟨p, hp⟩ := hρ r
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos p).ne'
  have hm_ne : m ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hm
    omega
  refine ⟨p ^ m, ⟨k, ?_⟩, ?_⟩
  · rw [orderOf_pow_of_dvd hm_ne ⟨2 ^ k, by rw [hkm, mul_comm]⟩, hkm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm_ne)]
  · rw [map_pow, hp]
    obtain ⟨j, hj⟩ := hm
    rw [hj, pow_succ, pow_mul, hr, one_pow, one_mul]

theorem two_element_image {P P₁ : Type} [Group P] [Finite P] [Group P₁] (ρ₁ : P →* P₁)
    (hodd : ¬ 2 ∣ Nat.card ρ₁.ker) {x : P} (hx2 : ∃ a : ℕ, orderOf x = 2 ^ a)
    (hx : x ^ 2 ≠ 1) : (∃ a : ℕ, orderOf (ρ₁ x) = 2 ^ a) ∧ ρ₁ x ^ 2 ≠ 1 := by
  obtain ⟨a, ha⟩ := hx2
  have hdvd : orderOf (ρ₁ x) ∣ 2 ^ a := by
    rw [← ha]
    exact orderOf_map_dvd ρ₁ x
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨⟨b, hb⟩, ?_⟩
  intro h
  have hmem : x ^ 2 ∈ ρ₁.ker := by
    rw [MonoidHom.mem_ker, map_pow, h]
  have hdvd' : orderOf (⟨x ^ 2, hmem⟩ : ρ₁.ker) ∣ 2 ^ a := by
    rw [Subgroup.orderOf_mk, ← ha]
    exact orderOf_pow_dvd 2
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  have hdvdker : 2 ^ c ∣ Nat.card ρ₁.ker := by
    rw [← hc]
    exact orderOf_dvd_natCard _
  have hc0 : c = 0 := by
    by_contra hcne
    apply hodd
    have h2c : 2 ∣ 2 ^ c := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hcne
      rw [hd, pow_succ]
      exact dvd_mul_left 2 (2 ^ d)
    exact h2c.trans hdvdker
  have hone : (⟨x ^ 2, hmem⟩ : ρ₁.ker) = 1 := by
    rw [← orderOf_eq_one_iff, hc, hc0, pow_zero]
  exact hx (by simpa using congrArg Subtype.val hone)

theorem even_card_fusionZStar {K : Type} [Group K] [Finite K] {w : K} (hw : orderOf w = 2)
    (hwc : w ∈ center K) : Even (Nat.card ↥(fusionZStar K)) := by
  have hwZ : w ∈ fusionZStar K := by
    show QuotientGroup.mk' (fusionOddCore K) w ∈ center (K ⧸ fusionOddCore K)
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (fusionOddCore K) q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hwc b]
  have h2 : orderOf (⟨w, hwZ⟩ : fusionZStar K) = 2 := by
    rw [Subgroup.orderOf_mk, hw]
  rw [even_iff_two_dvd, ← h2]
  exact orderOf_dvd_natCard _

theorem orderOf_mk_pPrimeCore_two {K : Type} [Group K] [Finite K] {w : K} (hw : orderOf w = 2) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 K) w) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw2 : w ^ 2 = 1 := by
    rw [← hw]
    exact pow_orderOf_eq_one w
  have hy2 : (QuotientGroup.mk' (pPrimeCore 2 K) w) ^ 2 = 1 := by
    rw [← map_pow, hw2, map_one]
  have hyne : QuotientGroup.mk' (pPrimeCore 2 K) w ≠ 1 := by
    intro h
    have hwmem : w ∈ pPrimeCore 2 K := by
      rw [← QuotientGroup.eq_one_iff (N := pPrimeCore 2 K) w]
      simpa [QuotientGroup.mk'_apply] using h
    have hdvd : orderOf (⟨w, hwmem⟩ : pPrimeCore 2 K) ∣ Nat.card (pPrimeCore 2 K) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hw] at hdvd
    exact (Nat.prime_two.coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (p := 2) (G := K))) hdvd
  exact orderOf_eq_prime hy2 hyne

theorem mk_mem_center {A : Type} [Group A] (N : Subgroup A) [N.Normal] {a : A}
    (ha : a ∈ center A) : QuotientGroup.mk' N a ∈ center (A ⧸ N) := by
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N q
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp ha b]

end Helpers

theorem exists_cover_with_lift (hGA : ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Type} [Group K] [Finite K] (hK2 : IsTwoQuasisimple K)
    (hKchev : IsSimpleChevalleyOver 3 (K ⧸ fusionZStar K)) (hnot : ¬ IsMTypeSchur 3 K)
    {w : K} (hw : orderOf w = 2) (hwc : w ∈ center K)
    {J : Subgroup K} (hJ : Group.IsPerfect ↥J) (hwJ : w ∈ J) :
    ∃ (P : Type) (_ : Group P) (_ : Finite P) (f : P →* ↥J ⧸ pPrimeCore 2 ↥J) (x : P),
      Function.Surjective f ∧ Group.IsPerfect P ∧ f.ker ≤ center P ∧
        (∃ a : ℕ, orderOf x = 2 ^ a) ∧ x ^ 2 ≠ 1 ∧
        f x = QuotientGroup.mk' (pPrimeCore 2 ↥J) ⟨w, hwJ⟩ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hstar, hdef⟩ := exists_deficiency hGA hK2 hKchev hnot (even_card_fusionZStar hw hwc)
  obtain ⟨S, _, _, π, hπs, hSp, hπk, hlift⟩ := exists_hopf_cover_data hK2.2
    (mk_mem_center (pPrimeCore 2 K) hwc) (orderOf_mk_pPrimeCore_two hw) hstar hdef
  obtain ⟨P₀, _, _, ρ, σ, hP₀, hρs, hρk, hcomm⟩ := exists_perfect_pullback π
    ((QuotientGroup.mk' (pPrimeCore 2 K)).comp J.subtype) hπs hπk hJ
  have hwJ2 : (⟨w, hwJ⟩ : ↥J) ^ 2 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← orderOf_dvd_iff_pow_eq_one, hw]
  obtain ⟨x₀, hx₀2, hρx₀⟩ := exists_two_element_lift ρ hρs hwJ2
  have hx₀ : x₀ ^ 2 ≠ 1 := by
    have h1 : π (σ x₀) = QuotientGroup.mk' (pPrimeCore 2 K) w := by
      rw [hcomm, hρx₀]
      rfl
    intro h
    apply (hlift (σ x₀) h1).2
    rw [← map_pow, h, map_one]
  have hodd : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥J)).ker := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  obtain ⟨P₁, _, _, ρ₁, f₁, hP₁, hρ₁s, hf₁s, hodd₁, hf₁k, hcomm₁⟩ := exists_central_reduction ρ
    (QuotientGroup.mk' (pPrimeCore 2 ↥J)) hP₀ hρs (QuotientGroup.mk'_surjective _) hρk hodd
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  obtain ⟨hx2, hx⟩ := two_element_image ρ₁ hodd₁ hx₀2 hx₀
  refine ⟨P₁, inferInstance, inferInstance, f₁, ρ₁ x₀, hf₁s, hP₁, hf₁k, hx2, hx, ?_⟩
  rw [hcomm₁, hρx₀]

theorem false_of_pumped (hGA : ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hE7 : E7ThreeRow) {K : Type} [Group K] [Finite K] (hK2 : IsTwoQuasisimple K)
    (hKchev : IsSimpleChevalleyOver 3 (K ⧸ fusionZStar K)) (hnot : ¬ IsMTypeSchur 3 K)
    {w : K} (hw : orderOf w = 2) (hwc : w ∈ center K)
    {J : Subgroup K} (hJ2 : IsTwoQuasisimple ↥J) (hJM : IsMTypeSchur 3 ↥J)
    (hJs : ClassBShape ↥J) (hwJ : w ∈ J) : False := by
  obtain ⟨P, _, _, f, x, hfs, hP, hfk, hx2, hx, hfx⟩ :=
    exists_cover_with_lift hGA hK2 hKchev hnot hw hwc hJ2.1 hwJ
  have hwJc : (⟨w, hwJ⟩ : ↥J) ∈ center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro j
    exact Subtype.ext (Subgroup.mem_center_iff.mp hwc (j : K))
  have hfxc : f x ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := by
    rw [hfx]
    exact mk_mem_center (pPrimeCore 2 ↥J) hwJc
  have hfx2 : f x ^ 2 = 1 := by
    rw [hfx, ← map_pow]
    have : (⟨w, hwJ⟩ : ↥J) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← orderOf_dvd_iff_pow_eq_one, hw]
    rw [this, map_one]
  exact false_of_central_cover f hfs hfk hP hJ2.2 (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    hx2 hx hfxc hfx2 (shape_cover_input hGA hE7 hJ2 hJM hJs)

end CFSG.OddStandard.HigherRank.F3.Ident
