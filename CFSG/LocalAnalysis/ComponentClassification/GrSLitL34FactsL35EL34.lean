module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35EZ16
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35ELayer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECL34
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35EBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35ETools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylow

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts CFSG.PSL3Four CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open scoped commutatorElement

theorem eq_seven_of_dvd_168 {Q N : ℕ} (hN : N * 2 = Q * (Q ^ 2 - 1)) (hd : N ∣ 168)
    (h5 : 5 ≤ Q) (hodd : Odd Q) : Q = 7 := by
  have hle := Nat.le_of_dvd (by norm_num) hd
  have hQ : Q ≤ 7 := by
    by_contra h8
    have := EvenCover.cube_mono (show 8 ≤ Q by omega)
    norm_num at this
    omega
  interval_cases Q
  · norm_num at hN
    have : N = 60 := by omega
    subst this
    norm_num at hd
  · exact absurd hodd (by decide)
  · rfl

theorem eq_five_of_dvd_60 {Q N : ℕ} (hN : N * 2 = Q * (Q ^ 2 - 1)) (hd : N ∣ 60)
    (h5 : 5 ≤ Q) : Q = 5 := by
  have hle := Nat.le_of_dvd (by norm_num) hd
  by_contra h6
  have := EvenCover.cube_mono (show 6 ≤ Q by omega)
  norm_num at this
  omega

theorem false_of_dvd_72 {Q N : ℕ} (hN : N * 2 = Q * (Q ^ 2 - 1)) (hd : N ∣ 72) (h5 : 5 ≤ Q) :
    False := by
  have hle := Nat.le_of_dvd (by norm_num) hd
  have hQ : Q ≤ 5 := by
    by_contra h6
    have := EvenCover.cube_mono (show 6 ≤ Q by omega)
    norm_num at this
    omega
  obtain rfl : Q = 5 := by omega
  norm_num at hN
  have : N = 60 := by omega
  subst this
  norm_num at hd

theorem tg_mul_self
    {d : ℕ × ℕ × ℕ × ℕ} (hd : d ∈ sqData) (hk : d.1 < 64) :
    wordPerm (tg d.1) * wordPerm (tg d.1) = 1 := by
  have h := congrArg sigma (sq_spec hd)
  rw [map_pow, sigma_tw _ hk, map_mul, map_mul, map_pow, map_pow, map_pow, sigma_z₁, sigma_z₂,
    sigma_z₃, one_pow, one_pow, one_pow, mul_one, mul_one] at h
  rw [← pow_two]
  exact h

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem even_concl_of_L34
    (h : Config G p w v L K)
    (hmS : Blueprint.LieModel ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))
      .PSL 3 2 2)
    (hout : quotAut h.tau ∉ innAut ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))) :
    Concl p v L K := by
  have hq := h.quasisimple_quot
  have : Group.IsPerfect (↥K ⧸ pPrimeCore 2 ↥K) := hq.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ1 : h.tau ≠ 1 := fun h1 => h.quotAut_tau_ne_one (by rw [h1, quotAut_one])
  have hτ2 : orderOf h.tau = 2 := by
    refine orderOf_eq_prime ?_ hτ1
    rw [pow_two]
    ext y
    exact h.tau_tau y
  have hτo : h.tau ∉ innAut (↥K ⧸ pPrimeCore 2 ↥K) := by
    rintro ⟨y, hy⟩
    exact hout ⟨QuotientGroup.mk y, by rw [← hy, quotAut_conj]⟩
  obtain ⟨q, hqS, hqsurj, hqker, ρ, hρ, hτρ⟩ := EvenCover.exists_aut_realization hmS hτ2 hτo
  set Φ := q.comp h.theta with hΦ
  have hΦC : ∀ x, Φ x ∈ centralizer {ρ} ⊓ S := fun x => by
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, hqS _⟩
    have h1 := hτρ (h.theta x)
    rw [h.tau_theta x] at h1
    change q (h.theta x) * ρ = ρ * q (h.theta x)
    calc q (h.theta x) * ρ = ρ * q (h.theta x) * ρ⁻¹ * ρ := by rw [← h1]
      _ = ρ * q (h.theta x) := by group
  set qb := QuotientGroup.lift (center (↥K ⧸ pPrimeCore 2 ↥K)) q hqker.ge with hqb
  have hqb_mk : ∀ y, qb (QuotientGroup.mk y) = q y := fun y => QuotientGroup.lift_mk _ _ _
  have hqb_inj : Function.Injective qb := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    rw [hqb_mk] at ha
    exact (QuotientGroup.eq_one_iff y).mpr (hqker ▸ ha)
  have hrange : Φ.range = (hatOf K L).map qb := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨hatHom h.L_le x, (hatHom h.L_le x).2, hqb_mk _⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx⟩ := hatHom_surjective h.L_le ⟨y, hy⟩
      refine ⟨x, ?_⟩
      have hx' : ((hatHom h.L_le x : ↥(hatOf K L)) : _) = y := congrArg Subtype.val hx
      rw [← hx']
      exact (hqb_mk _).symm
  have hcardΦ : Nat.card Φ.range = Nat.card (hatOf K L) := by
    rw [hrange, Subgroup.card_map_of_injective hqb_inj]
  have hΦle : Φ.range ≤ centralizer {ρ} ⊓ S := by
    rintro _ ⟨x, rfl⟩
    exact hΦC x
  obtain ⟨k, hk, hs5, hLsl, hLm⟩ := h.even_hat_lieModel
  have hN := EvenCover.card_mul_two_of_psl2 h.ne_two hLm
  have hNhat : Nat.card (↥(hatOf K L) ⧸ Open.fusionZStar ↥(hatOf K L)) ∣ Nat.card (hatOf K L) :=
    Subgroup.card_quotient_dvd_card _
  have hNdvd : Nat.card (↥(hatOf K L) ⧸ Open.fusionZStar ↥(hatOf K L)) ∣
      Nat.card ↥(centralizer {ρ} ⊓ S) :=
    hNhat.trans (hcardΦ ▸ Subgroup.card_dvd_of_le hΦle)
  have hNle : Nat.card (↥(hatOf K L) ⧸ Open.fusionZStar ↥(hatOf K L)) ≤ Nat.card (hatOf K L) :=
    Nat.le_of_dvd Nat.card_pos hNhat
  have hodd : Odd (p ^ k) := (h.prime.odd_of_ne_two h.ne_two).pow
  obtain ⟨l, hl, hls⟩ := exists_lam Group.IsPerfect.commutator_eq_top q hqS hqsurj hqker.le
  have hlq : ∀ c, q (l c) = sigma c := fun c => by rw [← MonoidHom.comp_apply, hl]
  have hcommY : ∀ {xL yL : ↥L} {a b : ℕ}, a < 64 → b < 64 → Φ xL = wordPerm (tg a) →
      Φ yL = wordPerm (tg b) → ⁅h.theta xL, h.theta yL⁆ = l ⁅cv (tw a), cv (tw b)⁆ :=
    fun ha hb hx hy => commutatorElement_eq_of_map hqker.le hl
      (by rw [sigma_tw _ ha]; exact hx) (by rw [sigma_tw _ hb]; exact hy)
  have hcommL : ∀ {xL yL : ↥L}, ⁅h.theta xL, h.theta yL⁆ = 1 →
      xL * yL * xL⁻¹ * yL⁻¹ ∈ pPrimeCore 2 ↥L := fun hc => by
    rw [← commutatorElement_def]
    exact h.mem_pPrimeCore_of_theta (by rw [map_commutatorElement]; exact hc)
  have h04 : wordPerm (tg 4) ≠ 1 := fun h1 => by
    rw [← wordPerm_tg_zero] at h1
    exact absurd (tg_injective (by norm_num) (by norm_num) h1) (by norm_num)
  have h48 : wordPerm (tg 4) * wordPerm (tg 4) = 1 :=
    tg_mul_self (d := (4, 1, 1, 1)) (by decide) (by norm_num)
  rcases hρ with rfl | rfl | rfl
  ·
    have hC : Nat.card ↥(centralizer {r₂} ⊓ S) = 168 := card_C₂
    rw [hC] at hNdvd
    have hQ7 : p ^ k = 7 := eq_seven_of_dvd_168 hN hNdvd hs5 hodd
    rw [hQ7] at hN
    norm_num at hN
    have hrangeEq : Φ.range = centralizer {r₂} ⊓ S :=
      Subgroup.eq_of_le_of_card_ge hΦle (by rw [hC, hcardΦ]; omega)
    have hx : wordPerm (tg 1) ∈ centralizer {r₂} ⊓ S :=
      EvenCover.wordPerm_mem_C₂ (w := tg 1) (by decide)
    have hy : wordPerm (tg 4) ∈ centralizer {r₂} ⊓ S :=
      EvenCover.wordPerm_mem_C₂ (w := tg 4) (by decide)
    obtain ⟨xL, hxL⟩ : wordPerm (tg 1) ∈ Φ.range := hrangeEq ▸ hx
    obtain ⟨yL, hyL⟩ : wordPerm (tg 4) ∈ Φ.range := hrangeEq ▸ hy
    have h01 : wordPerm (tg 1) ≠ 1 := fun h1 => by
      rw [← wordPerm_tg_zero] at h1
      exact absurd (tg_injective (by norm_num) (by norm_num) h1) (by norm_num)
    have h14 : wordPerm (tg 1) ≠ wordPerm (tg 4) := fun h1 =>
      absurd (tg_injective (by norm_num) (by norm_num) h1) (by norm_num)
    have h11 : wordPerm (tg 1) * wordPerm (tg 1) = 1 :=
      tg_mul_self (d := (1, 0, 0, 2)) (by decide) (by norm_num)
    have hz : l z₁ ^ 2 ≠ 1 := by
      intro hz1
      have hcY : ⁅h.theta xL, h.theta yL⁆ = 1 := by
        rw [hcommY (by norm_num) (by norm_num) hxL hyL, commutatorElement_def]
        have hcs := comm_spec (d := (1, 4, 2, 0, 0)) (by decide)
        simp only [pow_zero, mul_one] at hcs
        rw [hcs, map_pow, hz1]
      refine h.even_false_of_commute hk hs5 hLsl Φ isSimpleGroup_C₂ (by rw [card_C₂]; norm_num)
        hrangeEq (by rw [card_C₂, hQ7]; norm_num) (xL := xL) (yL := yL) ?_ ?_ ?_ ?_ ?_
        (hcommL hcY)
      · rw [hxL]; exact h11
      · rw [hyL]; exact h48
      · rw [hxL]; exact h01
      · rw [hyL]; exact h04
      · rw [hxL, hyL]; exact h14
    have h3 : ∀ e ∈ q.ker, e ^ 3 = 1 → e = 1 := by
      intro e he he3
      rw [hqker] at he
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp
        (N36.center_isPGroup (pPrimeCore_quotient_pPrimeCore_eq_bot 2))) ⟨e, he⟩
      have hd : orderOf (⟨e, he⟩ : center (↥K ⧸ pPrimeCore 2 ↥K)) ∣ 3 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_dvd_of_pow_eq_one he3
      rw [hj] at hd
      have hj0 : j = 0 := by
        by_contra hj0
        have h23 : 2 ∣ 3 := (dvd_pow_self 2 hj0).trans hd
        omega
      rw [hj0, pow_zero] at hj
      exact congrArg Subtype.val (orderOf_eq_one_iff.mp hj)
    have hZ16 := card_center_eq_sixteen hqker h3 hl hls hτρ hz
    have hlay : L = GSThmB.layerIn (K ⊓ centralizer {v}) := by
      apply h.eq_layerIn_of_hat_le
      intro J hJ
      have hc := h.isTwoComponentIn_hat hJ
      rw [← map_le_map_iff_of_injective hqb_inj, ← hrange, hrangeEq]
      rintro _ ⟨y', hy', rfl⟩
      have hfix : quotAut h.tau y' = y' := mem_fixedPoints.mp (hc.1 hy')
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y'
      rw [quotAut_mk] at hfix
      have h2 : q (h.tau y) = q y := by rw [← hqb_mk, ← hqb_mk, hfix]
      have h1 := hτρ y
      rw [h2] at h1
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, ?_⟩
      · rw [hqb_mk]
        calc q y * r₂ = r₂ * q y * r₂⁻¹ * r₂ := by rw [← h1]
          _ = r₂ * q y := by group
      · rw [hqb_mk]
        exact hqS y
    obtain ⟨rfl, rfl⟩ := (Nat.prime_seven.pow_eq_iff).mp hQ7
    refine ⟨hlay, Or.inl ⟨rfl, ?_, hq, hZ16, hmS⟩⟩
    rw [pow_one] at hLsl
    exact hLsl
  ·
    exfalso
    have hC : Nat.card ↥(centralizer {r₃} ⊓ S) = 60 := card_C₃
    rw [hC] at hNdvd
    have hQ5 : p ^ k = 5 := eq_five_of_dvd_60 hN hNdvd hs5
    rw [hQ5] at hN
    norm_num at hN
    have hrangeEq : Φ.range = centralizer {r₃} ⊓ S :=
      Subgroup.eq_of_le_of_card_ge hΦle (by rw [hC, hcardΦ]; omega)
    have hx : wordPerm (tg 4) ∈ centralizer {r₃} ⊓ S := tg_mem_C₃ (by decide)
    have hy : wordPerm (tg 8) ∈ centralizer {r₃} ⊓ S := tg_mem_C₃ (by decide)
    obtain ⟨xL, hxL⟩ : wordPerm (tg 4) ∈ Φ.range := hrangeEq ▸ hx
    obtain ⟨yL, hyL⟩ : wordPerm (tg 8) ∈ Φ.range := hrangeEq ▸ hy
    have h08 : wordPerm (tg 8) ≠ 1 := fun h1 => by
      rw [← wordPerm_tg_zero] at h1
      exact absurd (tg_injective (by norm_num) (by norm_num) h1) (by norm_num)
    have h48' : wordPerm (tg 4) ≠ wordPerm (tg 8) := fun h1 =>
      absurd (tg_injective (by norm_num) (by norm_num) h1) (by norm_num)
    have h88 : wordPerm (tg 8) * wordPerm (tg 8) = 1 :=
      tg_mul_self (d := (8, 1, 0, 0)) (by decide) (by norm_num)
    have hcY : ⁅h.theta xL, h.theta yL⁆ = 1 := by
      rw [hcommY (by norm_num) (by norm_num) hxL hyL, commutatorElement_def]
      have hcs := comm_spec (d := (4, 8, 0, 0, 0)) (by decide)
      simp only [pow_zero, mul_one] at hcs
      rw [hcs, map_one]
    refine h.even_false_of_commute hk hs5 hLsl Φ isSimpleGroup_C₃ (by rw [card_C₃]; norm_num)
      hrangeEq (by rw [card_C₃, hQ5]; norm_num) (xL := xL) (yL := yL) ?_ ?_ ?_ ?_ ?_
      (hcommL hcY)
    · rw [hxL]; exact h48
    · rw [hyL]; exact h88
    · rw [hxL]; exact h04
    · rw [hyL]; exact h08
    · rw [hxL, hyL]; exact h48'
  ·
    exfalso
    have hC : Nat.card ↥(centralizer {r₄} ⊓ S) = 72 := card_C₄
    rw [hC] at hNdvd
    exact false_of_dvd_72 hN hNdvd hs5

end Config

end CFSG.ComponentClassification.HarrisLit.L35
