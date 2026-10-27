module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FiveLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GraphLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Counting
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Inversion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Sylow

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma isConj_orderOf_eq {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have h' := MulEquiv.orderOf_eq (MulAut.conj c) x
  simp only [MulAut.conj_apply] at h'
  rw [hc] at h'
  exact h'.symm

private lemma card_of_isShapeCentralizerFiveB {X : Type*} [Group X]
    (h : IsShapeCentralizerFiveB X) : Nat.card X = 100 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, DihedralGroup.nat_card]

private lemma card_of_isShapeSym_seven {X : Type*} [Group X] (h : IsShapeSym 7 X) :
    Nat.card X = 5040 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  norm_num

private lemma card_of_isShapeZ2TimesSym_five {X : Type*} [Group X]
    (h : IsShapeZ2TimesSym 5 X) : Nat.card X = 240 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_perm, Nat.card_fin]
  norm_num

private theorem Gxyz_eq_inf' {G : Type} [Group G] (a t x : G) :
    Gxyz a t x = Gxy a x ⊓ Gx t := by
  ext g
  simp only [mem_Gxyz, mem_Gxy, Subgroup.mem_inf]
  tauto

theorem five_odd_core_prime (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hCent : FiveCentFacts a z) (hS7 : S7Facts a z) (hGam : GammaFacts a z)
    {ρ : G} (hρ : ρ ∈ Gx a) (h5 : orderOf ρ = 5) (hshape : IsShapeCentralizerFiveB ↥(Gxy a ρ))
    {N : Subgroup G} (hNK : N ≤ Gx ρ) (hNn : (N.subgroupOf (Gx ρ)).Normal)
    (hodd : ¬ 2 ∣ Nat.card ↥N) {p : ℕ} (hp : p.Prime) (hpN : p ∣ Nat.card ↥N) : p = 5 := by
  by_contra hp5
  have ha2 : a * a = 1 := by
    have h' := pow_orderOf_eq_one a
    rw [h.orderOf_a] at h'
    simpa [pow_two] using h'
  have haK : a ∈ Gx ρ := mem_Gx.mpr (mem_Gx.mp hρ).symm
  have hp2 : p ≠ 2 := by
    intro hp_eq
    exact hodd (hp_eq ▸ hpN)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hcard100 : Nat.card ↥(Gxy a ρ) = 100 := card_of_isShapeCentralizerFiveB hshape
  have hpnot100 : ¬ p ∣ 100 := by
    intro hdiv
    have h2 : p ∣ 2 ^ 2 * 5 ^ 2 := by
      have h100 : (2 : ℕ) ^ 2 * 5 ^ 2 = 100 := by norm_num
      rwa [h100]
    rcases hp.dvd_mul.mp h2 with hdiv2 | hdiv5
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdiv2))
    · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow hdiv5))
  have hC : ¬ p ∣ Nat.card ↥(Gx ρ ⊓ Gx a) := by
    have heq : (Gx ρ ⊓ Gx a : Subgroup G) = Gxy a ρ := by rw [inf_comm, ← Gxy_eq_inf]
    rw [heq, hcard100]
    exact hpnot100
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσN, hσord, hσinv⟩ :=
    exists_inverted_element (K := Gx ρ) (N := N) hNK hNn hodd haK ha2 hpN hC
  set x : G := σ * a * σ⁻¹ with hx_def
  have hx : IsConj a x := isConj_iff.2 ⟨σ, by rw [hx_def]⟩
  have hax_eq : a * x = σ⁻¹ * σ⁻¹ := by
    rw [hx_def]
    calc a * (σ * a * σ⁻¹) = (a * σ * a) * σ⁻¹ := by simp only [← mul_assoc]
      _ = σ⁻¹ * σ⁻¹ := by rw [hσinv]
  have hcop : (orderOf (σ⁻¹)).Coprime 2 := by
    rw [orderOf_inv, hσord]
    exact hpodd.coprime_two_right
  have haxord : orderOf (a * x) = p := by
    rw [hax_eq, ← pow_two, Nat.Coprime.orderOf_pow hcop, orderOf_inv, hσord]
  have hxmem : x ∈ gammaSet a z a := hGam.eq_gamma a x (IsConj.refl a) hx
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff, or_assoc] at hxmem
  have hx3A : x ∈ orb3A a a := by
    rcases hxmem with hxa | hx2A | hx2B | hx3A | hx4A | hx4B | hx5A | hx5E | hx6A
    · exfalso
      have h1 : orderOf (a * x) = 1 := by rw [hxa, ha2]; exact orderOf_one
      exact hp.ne_one (by rw [← haxord, h1])
    · exfalso
      have h2 : orderOf (a * x) = 2 := by rw [← isConj_orderOf_eq hx2A.2, h.orderOf_a]
      exact hp2 (by rw [← haxord, h2])
    · exfalso
      have h2 : orderOf (a * x) = 2 := by rw [← isConj_orderOf_eq hx2B.2, h.orderOf_z]
      exact hp2 (by rw [← haxord, h2])
    · exact hx3A
    · exfalso
      have h2 : orderOf ((a * x) ^ 2) = 2 := by
        rw [← isConj_orderOf_eq hx4A.2, h.orderOf_z]
      have h4 : (a * x) ^ 4 = 1 := by
        have h' := pow_orderOf_eq_one ((a * x) ^ 2)
        rw [h2] at h'
        rw [← pow_mul] at h'
        norm_num at h'
        exact h'
      have hpd4 : p ∣ 4 := by
        rw [← haxord]
        exact orderOf_dvd_iff_pow_eq_one.mpr h4
      have hpd2pow : p ∣ 2 ^ 2 := by
        have h4' : (2 : ℕ) ^ 2 = 4 := by norm_num
        rwa [h4']
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd2pow))
    · exfalso
      have h2 : orderOf ((a * x) ^ 2) = 2 := by
        rw [← isConj_orderOf_eq hx4B.2, h.orderOf_a]
      have h4 : (a * x) ^ 4 = 1 := by
        have h' := pow_orderOf_eq_one ((a * x) ^ 2)
        rw [h2] at h'
        rw [← pow_mul] at h'
        norm_num at h'
        exact h'
      have hpd4 : p ∣ 4 := by
        rw [← haxord]
        exact orderOf_dvd_iff_pow_eq_one.mpr h4
      have hpd2pow : p ∣ 2 ^ 2 := by
        have h4' : (2 : ℕ) ^ 2 = 4 := by norm_num
        rwa [h4']
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd2pow))
    · exfalso
      exact hp5 (by rw [← haxord, hx5A.2.1])
    · exfalso
      exact hp5 (by rw [← haxord, hx5E.2.1])
    · exfalso
      have h6 : p = 6 := by rw [← haxord, hx6A.2.1]
      exact (by decide : ¬ Nat.Prime 6) (h6 ▸ hp)
  have hp3 : p = 3 := by rw [← haxord, hx3A.2.1]
  have hσc : Commute σ ρ := (mem_Gx.mp (hNK hσN)).symm
  have hac : Commute a ρ := mem_Gx.mp hρ
  have hxρ : Commute x ρ := by
    rw [hx_def]
    exact (hσc.mul_left hac).mul_left hσc.inv_left
  have hρxy : ρ ∈ Gxy a x := mem_Gxy.mpr ⟨hρ, mem_Gx.mpr hxρ.eq⟩
  have hpart := hS7.classes x hx3A
  have hSorbit : IsConjOrbit (Gxy a x) (s7Set a z x 0) := hpart.orbit 0
  have hSsubset : s7Set a z x 0 ⊆ {t | t ∈ Gxy a x ∧ orderOf t = 2} := hpart.subset 0
  have hstab : ∀ t ∈ s7Set a z x 0, Nat.card ↥(Gxy a x ⊓ Gx t) = 240 := by
    intro t ht
    have ht' : t ∈ orb2A a a ∩ orb2A a x := ht
    have h' := hS7.shape_i x hx3A t ht'
    rw [← Gxyz_eq_inf' a t x]
    exact card_of_isShapeZ2TimesSym_five h'
  have hcard5040 : Nat.card ↥(Gxy a x) = 5040 := card_of_isShapeSym_seven (hS7.shape x hx3A)
  obtain ⟨t₀, ht₀⟩ := hSorbit.nonempty
  have hcount : Nat.card ↥(s7Set a z x 0) * 240 = 5040 := by
    have h' := IsConjOrbit.card_mul_card_stab hSorbit ht₀
    rw [hstab t₀ ht₀, hcard5040] at h'
    exact h'
  have hcardS : Nat.card ↥(s7Set a z x 0) = 21 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 240) (by rw [hcount])
  have hnot5 : ¬ 5 ∣ Nat.card ↥(s7Set a z x 0) := by rw [hcardS]; norm_num
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcl : ∀ c ∈ s7Set a z x 0, ρ * c * ρ⁻¹ ∈ s7Set a z x 0 :=
    fun c hc => hSorbit.conj_mem ρ hρxy c hc
  obtain ⟨t, htS, hρt⟩ := exists_commute_of_card_not_dvd (p := 5) h5 hcl hnot5
  have hsub := hSsubset htS
  have htxy : t ∈ Gxy a x := hsub.1
  have ht2A : IsConj a t := (show t ∈ orb2A a a ∩ orb2A a x from htS).1.1
  have htGxρ : t ∈ Gx ρ := mem_Gx.mpr hρt
  have hshape_t : IsShapeCentralizerFiveB ↥(Gxy t ρ) :=
    hCent.cent_five ρ hρ h5 hshape t ht2A htGxρ
  have hcard_t : Nat.card ↥(Gxy t ρ) = 100 := card_of_isShapeCentralizerFiveB hshape_t
  have hcta : Commute t a := (mem_Gx.mp (mem_Gxy.mp htxy).1).symm
  have hctx : Commute t x := (mem_Gx.mp (mem_Gxy.mp htxy).2).symm
  have hctax : Commute t (a * x) := hcta.mul_right hctx
  rw [hax_eq] at hctax
  rw [show σ⁻¹ * σ⁻¹ = (σ⁻¹) ^ 2 from (pow_two (σ⁻¹)).symm] at hctax
  have h2dvd : 2 ∣ p + 1 := by
    obtain ⟨k, hk⟩ := hpodd
    exact ⟨k + 1, by omega⟩
  have hpow : ((σ⁻¹) ^ 2) ^ ((p + 1) / 2) = σ⁻¹ := by
    rw [← pow_mul, Nat.mul_div_cancel' h2dvd, pow_succ]
    have hp1 : (σ⁻¹) ^ p = 1 := by
      rw [← hσord, ← orderOf_inv σ]
      exact pow_orderOf_eq_one σ⁻¹
    rw [hp1, one_mul]
  have hctinv : Commute t σ⁻¹ := by
    have h' := hctax.pow_right ((p + 1) / 2)
    rwa [hpow] at h'
  have hctσ : Commute t σ := by
    have h' := hctinv.inv_right
    simpa using h'
  have hσGxy : σ ∈ Gxy t ρ := mem_Gxy.mpr ⟨mem_Gx.mpr hctσ.eq, hNK hσN⟩
  have horderσ : orderOf (⟨σ, hσGxy⟩ : ↥(Gxy t ρ)) = p := by
    rw [Subgroup.orderOf_mk, hσord]
  have hpdvd100 : p ∣ 100 := by
    have h' := orderOf_dvd_natCard (⟨σ, hσGxy⟩ : ↥(Gxy t ρ))
    rw [horderσ, hcard_t] at h'
    exact h'
  rw [hp3] at hpdvd100
  exact absurd hpdvd100 (by norm_num)

end CFSG.EvenSporadicStandard.HNRecog.Section3
