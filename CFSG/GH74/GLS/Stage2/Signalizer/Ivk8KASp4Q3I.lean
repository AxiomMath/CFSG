module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Easy

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Field

variable {F : Type} [Field F] [Finite F]

theorem kaQ3I_pow_three (h3 : Nat.card F = 3) (r : F) : r ^ 3 = r := by
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card r
  rwa [← Nat.card_eq_fintype_card, h3] at h

theorem kaQ3I_ringChar_ne_two (h3 : Nat.card F = 3) : ringChar F ≠ 2 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).2 (by rw [h])
  have h2 : (2 : F) = 0 := by exact_mod_cast h'
  have h30 := CFSG.LieType.HighestRoot.three_eq_zero h3
  exact one_ne_zero (show (1 : F) = 0 by linear_combination h30 - h2)

theorem kaQ3I_sq_one (h3 : Nat.card F = 3) {a : F} (ha : a ≠ 0) : a ^ 2 = 1 := by
  have h := kaQ3I_pow_three h3 a
  have h1 : a * (a ^ 2 - 1) = 0 := by linear_combination h
  have h2 := (mul_eq_zero.mp h1).resolve_left ha
  linear_combination h2

theorem kaQ3I_cube_mk (h3 : Nat.card F = 3) (a : F) (x : QuadraticAlgebra F a 0) :
    x ^ 3 = ⟨x.re, a * x.im⟩ := by
  have hu := kaQ3I_pow_three h3 x.re
  have hv := kaQ3I_pow_three h3 x.im
  have h30 := CFSG.LieType.HighestRoot.three_eq_zero h3
  ext
  · simp only [pow_succ, pow_zero, one_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    simp
    linear_combination hu + (a * x.re * x.im ^ 2) * h30
  · simp only [pow_succ, pow_zero, one_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    simp
    linear_combination (x.re ^ 2 * x.im) * h30 + a * hv

theorem kaQ3I_pow_nine (h3 : Nat.card F = 3) {a : F} (ha : a ≠ 0)
    (x : QuadraticAlgebra F a 0) : x ^ 9 = x := by
  have h : x ^ 9 = (x ^ 3) ^ 3 := by rw [← pow_mul]
  rw [h, kaQ3I_cube_mk h3 a x, kaQ3I_cube_mk h3 a ⟨x.re, a * x.im⟩]
  have ha2 := kaQ3I_sq_one h3 ha
  ext
  · rfl
  · show a * (a * x.im) = x.im
    linear_combination x.im * ha2

end Field

theorem kaQ3I_eq_one_of_pow_odd {R : Type*} [CommRing R] {d : R} (h9 : d ^ 9 = d) {m : ℕ}
    (hm : Odd m) (hd : d ^ m = 1) : d = 1 := by
  have hu : IsUnit d := IsUnit.of_pow_eq_one hd hm.pos.ne'
  have h8 : d ^ 8 = 1 := by
    have h : d * d ^ 8 = d * 1 := by rw [mul_one, ← pow_succ']; exact h9
    exact hu.mul_left_cancel h
  have hcop : Nat.Coprime m 8 := Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 hm)
  have h1 := pow_gcd_eq_one.2 ⟨hd, h8⟩
  rwa [hcop, pow_one] at h1

section JI

variable {F : Type} [Field F] {a : F}

theorem kaQ3I_JI_le_closure [Finite F] (h3 : Nat.card F = 3) (ha : a ≠ 0) :
    JI ha ≤ Subgroup.closure {y | y ∈ JI ha ∧ y ^ 3 = 1} := by
  set φ : Matrix.SpecialLinearGroup (Fin 2) F →* StatedProj (StatedSp 2 F) :=
    (proj 2 F).comp (gI ha)
  have hrange : φ.range = JI ha := MonoidHom.range_comp (proj 2 F) (gI ha)
  have hJ : JI ha = (Subgroup.closure
      {x : Matrix.SpecialLinearGroup (Fin 2) F | orderOf x = 3}).map φ := by
    rw [CFSG.LieType.HighestRoot.closure_orderOf_three_eq_top h3, ← MonoidHom.range_eq_map, hrange]
  refine hJ.le.trans ?_
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← hrange]
    exact ⟨y, rfl⟩
  · have hy3 : y ^ 3 = 1 := by
      rw [← (hy : orderOf y = 3)]
      exact pow_orderOf_eq_one y
    rw [← map_pow, hy3, map_one]

theorem kaQ3I_card_JI [Finite F] (h3 : Nat.card F = 3) (ha : a ≠ 0) :
    Nat.card (JI ha) ∣ 24 ∧ 12 ≤ Nat.card (JI ha) := by
  set φ : Matrix.SpecialLinearGroup (Fin 2) F →* StatedProj (StatedSp 2 F) :=
    (proj 2 F).comp (gI ha) with hφ
  have hrange : φ.range = JI ha := MonoidHom.range_comp (proj 2 F) (gI ha)
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 24 :=
    CFSG.LieType.HighestRoot.card_eq_24 h3 (MulEquiv.refl _)
  have hker : Nat.card φ.ker ≤ 2 := by
    rw [hφ, ker_proj_comp_gI ha, Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (i := (0 : Fin 2)) (R := F)).toEquiv]
    exact card_rootsOfUnity F 2
  have hprod : Nat.card φ.range * Nat.card φ.ker = 24 := by
    rw [← hSL, Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hker0 : 0 < Nat.card φ.ker := Nat.card_pos
  rw [← hrange]
  refine ⟨Dvd.intro _ hprod, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.card φ.ker = k := ⟨_, rfl⟩
  rw [hk] at hprod hker hker0
  interval_cases k <;> omega

end JI

theorem kaQ3I_normal_pGroup_eq_bot {G : Type*} [Group G] (J : Subgroup G)
    (hgen : J ≤ Subgroup.closure {y : G | y ∈ J ∧ y ^ 3 = 1})
    (hdvd : Nat.card J ∣ 24) (hge : 12 ≤ Nat.card J) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup G} (hXJ : X ≤ J) (hXp : IsPGroup p ↥X)
    (hXn : ∀ r ∈ J, r ∈ normalizer (X : Set G)) : X = ⊥ := by
  have : Finite J := Nat.finite_of_card_ne_zero (by omega)
  by_contra hX
  have : Fact p.Prime := ⟨hp⟩
  have : Finite X := Finite.of_injective (Subgroup.inclusion hXJ) (Subgroup.inclusion_injective hXJ)
  obtain ⟨k, hk⟩ := hXp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hX
    rw [pow_zero] at hk
    exact Subgroup.card_eq_one.1 hk
  have hX24 : Nat.card X ∣ 24 := (Subgroup.card_dvd_of_le hXJ).trans hdvd
  have hp24 : p ∣ 24 := by
    refine (dvd_pow_self p hk0).trans ?_
    rw [← hk]
    exact hX24
  have hp3 : p = 3 := by
    have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h24] at hp24
    rcases (Nat.Prime.dvd_mul hp).1 hp24 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
  subst hp3
  have hk1 : k = 1 := by
    by_contra hne
    have h2 : 2 ≤ k := by omega
    have h9 : 9 ∣ Nat.card X := by
      rw [hk]
      exact (show 9 = 3 ^ 2 by norm_num) ▸ pow_dvd_pow 3 h2
    have := h9.trans hX24
    omega
  have hX3 : Nat.card X = 3 := by rw [hk, hk1, pow_one]
  let N : Subgroup J := X.subgroupOf J
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXJ).2 hXn
  have hNcard : Nat.card N = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXJ).toEquiv, hX3]
  have hQ : Nat.card (J ⧸ N) * 3 = Nat.card J := by
    rw [← hNcard]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
  have hQ8 : Nat.card (J ⧸ N) ∣ 8 := by
    have h1 : Nat.card (J ⧸ N) * 3 ∣ 8 * 3 := hQ ▸ hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1
  have hcop : Nat.Coprime 3 (Nat.card (J ⧸ N)) :=
    (show Nat.Coprime 3 8 by norm_num).coprime_dvd_right hQ8
  have hS : ∀ y ∈ J, y ^ 3 = 1 → y ∈ X := by
    intro y hy hy3
    have h1 : (QuotientGroup.mk ⟨y, hy⟩ : J ⧸ N) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨y, hy⟩ : J) ^ 3 = 1 := Subtype.ext hy3
      rw [this, QuotientGroup.mk_one]
    have h2 : (QuotientGroup.mk ⟨y, hy⟩ : J ⧸ N) ^ Nat.card (J ⧸ N) = 1 := pow_card_eq_one'
    have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rw [hcop, pow_one] at h3
    have h4 : (⟨y, hy⟩ : J) ∈ N := (QuotientGroup.eq_one_iff _).1 h3
    exact h4
  have hJX : J ≤ X := hgen.trans ((Subgroup.closure_le X).2 fun y hy => hS y hy.1 hy.2)
  have := Subgroup.card_le_of_le hJX
  omega

theorem kaQ3I_scalar_sq {F : Type} [Field F] {z : StatedSp 2 F} (hz : z ∈ spScalars 2 F) :
    z * z = 1 :=
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.ka_easy_scalar_sq hz

theorem kaQ3I_odd_mem_JI {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3) {a : F}
    (ha : a ≠ 0) {x : StatedSp 2 F} (hx : x ∈ fixI a ha) {m : ℕ} (hm : Odd m)
    (hx1 : proj 2 F x ^ m = 1) : proj 2 F x ∈ JI ha := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (kaQ3I_ringChar_ne_two h3)
  set g : fixI a ha := ⟨x, hx⟩
  have hscal : ((g ^ m : fixI a ha) : StatedSp 2 F) ∈ spScalars 2 F := by
    rw [← ker_proj, MonoidHom.mem_ker, Subgroup.coe_pow, map_pow]
    exact hx1
  have hsq : g ^ m * g ^ m = 1 := Subtype.ext (kaQ3I_scalar_sq hscal)
  obtain ⟨k, hk⟩ := hm
  have hgm : (g ^ (m + 1)) ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    have : m + 1 = 2 * (k + 1) := by omega
    rw [this, pow_mul, sq, hsq, one_pow]
  have hd1 : detI ha (g ^ (m + 1)) = 1 :=
    kaQ3I_eq_one_of_pow_odd (kaQ3I_pow_nine h3 ha _) ⟨k, hk⟩ (by rw [← map_pow, hgm, map_one])
  obtain ⟨s, hs⟩ := mem_range_gI_of_detI ha h2 (g ^ (m + 1)) hd1
  refine ⟨gI ha s, ⟨s, rfl⟩, ?_⟩
  rw [hs, Subgroup.coe_pow, map_pow, pow_succ, hx1, one_mul]

theorem kaSp4IThree_thm : KASp4IThree := by
  intro F _ _ h3 a ha
  have hodd : ringChar F ≠ 2 := kaQ3I_ringChar_ne_two h3
  have hθα : ∀ g, alphaI ha (proj 2 F g) = proj 2 F (conjSp 2 F (aIgsp ha) g) :=
    fun g => conjAut_proj (aIgsp ha) g
  refine ka_all_of_oddcore (ka_conj_inj_psp4 hodd) (JI ha) ?_ ?_ ?_ ?_ (ka_outCyc_psp4 hodd)
    (ka_outCentral_psp4 hodd (alphaI ha))
  · exact fun y hy => mem_fixSub.2 (alphaI_JI ha hy)
  · refine le_antisymm ((Subgroup.closure_le _).2 fun y hy => hy.1) ?_
    refine (kaQ3I_JI_le_closure h3 ha).trans (Subgroup.closure_mono ?_)
    rintro y ⟨hy, hy3⟩
    exact ⟨hy, Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hy3)⟩
  · intro c hc ho
    obtain ⟨x, hx, rfl⟩ := ka_odd_mem_map_fixOf (conjSp 2 F (aIgsp ha)) (alphaI ha) hθα
      (mem_fixSub.1 hc) ho
    exact kaQ3I_odd_mem_JI h3 ha hx ho (pow_orderOf_eq_one _)
  · intro p hp hp2 X hX hXle hXn
    obtain ⟨hdvd, hge⟩ := kaQ3I_card_JI h3 ha
    exact kaQ3I_normal_pGroup_eq_bot (JI ha) (kaQ3I_JI_le_closure h3 ha) hdvd hge hp hp2 hXle hX
      hXn

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
