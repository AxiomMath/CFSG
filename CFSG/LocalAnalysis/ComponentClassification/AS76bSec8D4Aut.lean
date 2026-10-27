module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4D0
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.EvenTrialityCanonicalFieldCentralizer
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement Matrix Pointwise

section Inner

theorem conj_eq_one_of_fix_d4 {C : Type*} [Group C] [Finite C] (hZ : center C = ⊥)
    {Z D Q H L : Subgroup C} (hL : Exc.LeviData Z D Q H L) (hHodd : Odd (Nat.card H))
    {c : C} {k : ℕ} (hk : MulAut.conj c ^ 2 ^ k = 1) (hQ : ∀ y ∈ Q, MulAut.conj c y = y)
    (hLf : ∀ y ∈ L, MulAut.conj c y = y) : c = 1 := by
  have hc2 : c ^ 2 ^ k = 1 := by
    have h1 : MulAut.conj (c ^ 2 ^ k) = 1 := by rw [map_pow, hk]
    have h2 : c ^ 2 ^ k ∈ center C := by
      rw [mem_center_iff]
      intro z
      have h3 := congrArg (fun φ : MulAut C => φ z) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc z * c ^ 2 ^ k = c ^ 2 ^ k * z * (c ^ 2 ^ k)⁻¹ * c ^ 2 ^ k := by rw [h3]
        _ = c ^ 2 ^ k * z := by group
    rw [hZ, mem_bot] at h2
    exact h2
  have hcQ : c ∈ centralizer (Q : Set C) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := hQ y hy
    simp only [MulAut.conj_apply] at h1
    calc y * c = c * y * c⁻¹ * c := by rw [h1]
      _ = c * y := by group
  obtain ⟨h, hh, hhL⟩ := hL.cent_eq c hcQ
  have hpow : ∀ n : ℕ, ∃ l' ∈ L, c ^ n = h ^ n * l' := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, mul_one]⟩
    | succ n ih =>
      obtain ⟨l', hl', e⟩ := ih
      refine ⟨(h⁻¹ * l' * h⁻¹⁻¹) * (h⁻¹ * c),
        mul_mem ((mem_normalizer_iff.1 (hL.H_le (inv_mem hh)) l').1 hl') hhL, ?_⟩
      rw [pow_succ, e, pow_succ]
      group
  obtain ⟨l', hl', e⟩ := hpow (2 ^ k)
  rw [hc2] at e
  have hh2 : h ^ 2 ^ k ∈ L := by
    rw [eq_inv_of_mul_eq_one_left e.symm]
    exact inv_mem hl'
  have hord : Odd (orderOf h) := by
    refine Odd.of_dvd_nat hHodd ?_
    rw [← Subgroup.orderOf_mk h hh]
    exact orderOf_dvd_natCard _
  have hco : Nat.Coprime (2 ^ k) (orderOf h) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hord)
  have hhL' : h ∈ L := by
    have hb := Nat.gcd_eq_gcd_ab (2 ^ k) (orderOf h)
    rw [hco.gcd_eq_one, Nat.cast_one] at hb
    have e2 : h = (h ^ 2 ^ k) ^ Nat.gcdA (2 ^ k) (orderOf h) *
        (h ^ orderOf h) ^ Nat.gcdB (2 ^ k) (orderOf h) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hb, zpow_one]
    rw [e2, pow_orderOf_eq_one, one_zpow, mul_one]
    exact zpow_mem hh2 _
  have hcL : c ∈ L := by
    have h1 := mul_mem hhL' hhL
    rwa [mul_inv_cancel_left] at h1
  have hcZ : (⟨c, hcL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro y
    have h1 := hLf y y.2
    simp only [MulAut.conj_apply] at h1
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    calc (y : C) * c = c * y * c⁻¹ * c := by rw [h1]
      _ = c * y := by group
  have hodd : Odd (orderOf (⟨⟨c, hcL⟩, hcZ⟩ : center L)) :=
    Odd.of_dvd_nat hL.odd_center (orderOf_dvd_natCard _)
  have hpow1 : (⟨⟨c, hcL⟩, hcZ⟩ : center L) ^ 2 ^ k = 1 :=
    Subtype.ext (Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one]; exact hc2))
  have h1 : orderOf (⟨⟨c, hcL⟩, hcZ⟩ : center L) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd))
      (orderOf_dvd_of_pow_eq_one hpow1)
  exact congrArg (fun x : center L => ((x : L) : C)) (orderOf_eq_one_iff.1 h1)

end Inner

section Orders

theorem coprime_card_d4 {e : ℕ} (he : 1 ≤ e) :
    Nat.Coprime (2 ^ (2 * e) + 1) ((2 ^ e) ^ 12 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 6 - 1) *
      ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1)) := by
  set A := 2 ^ (2 * e) + 1 with hA
  have h1 : 1 ≤ (2 ^ e) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : 1 ≤ (2 ^ e) ^ 6 := Nat.one_le_pow _ _ (by positivity)
  have hy : ((2 : ZMod A) ^ e) ^ 2 = -1 := by
    have h0 : ((A : ℕ) : ZMod A) = 0 := ZMod.natCast_self A
    rw [hA] at h0
    push_cast at h0
    rw [← pow_mul, mul_comm]
    linear_combination h0
  have hval : (((2 ^ e) ^ 12 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 6 - 1) *
      ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1) : ℕ) : ZMod A) = ((12 : ℕ) : ZMod A) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h2]
    push_cast
    rw [show ((2 : ZMod A) ^ e) ^ 12 = (((2 : ZMod A) ^ e) ^ 2) ^ 6 by ring,
      show ((2 : ZMod A) ^ e) ^ 6 = (((2 : ZMod A) ^ e) ^ 2) ^ 3 by ring,
      show ((2 : ZMod A) ^ e) ^ 8 = (((2 : ZMod A) ^ e) ^ 2) ^ 4 by ring,
      show ((2 : ZMod A) ^ e) ^ 4 = (((2 : ZMod A) ^ e) ^ 2) ^ 2 by ring, hy]
    norm_num
  have hodd : Odd A := by
    rw [hA]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have h3 : ¬ 3 ∣ A := by
    have h4 : 4 ^ e % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [hA, pow_mul]
    norm_num
    omega
  have h12 : Nat.Coprime 12 A := by
    rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num]
    exact Nat.coprime_mul_iff_left.2 ⟨Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd),
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3⟩
  have hu : IsUnit (((2 ^ e) ^ 12 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 6 - 1) *
      ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1) : ℕ) : ZMod A) := by
    rw [hval]
    exact (ZMod.isUnit_iff_coprime 12 A).2 h12
  exact ((ZMod.isUnit_iff_coprime _ A).1 hu).symm

theorem succ_dvd_card_sl2_d4 (q : ℕ) : q + 1 ∣ q * (q ^ 2 - 1) :=
  Dvd.dvd.mul_left ⟨q - 1, by rw [← Nat.sq_sub_sq, one_pow]⟩ q

theorem succ_dvd_card_sl2_cube_d4 (q : ℕ) : q + 1 ∣ q ^ 3 * ((q ^ 3) ^ 2 - 1) := by
  refine Dvd.dvd.mul_left ?_ _
  have h1 : q + 1 ∣ q ^ 2 - 1 := ⟨q - 1, by rw [← Nat.sq_sub_sq, one_pow]⟩
  rw [← pow_mul]
  exact h1.trans (Nat.pow_sub_one_dvd_pow_sub_one q (by norm_num : 2 ∣ 3 * 2))

end Orders

section AutFixSec

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem d4_autFix
    (m : ℕ) (hm : 2 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3)
    (hσq : ∀ c, σ c = c ^ 2 ^ m) {Z D Q H L : Subgroup ↥(d4C K σ)}
    (hL : Exc.LeviData Z D Q H L) (hHodd : Odd (Nat.card H))
    (hqL : 2 ^ m + 1 ∣ Nat.card L) : Exc.AutFix Q L := by
  classical
  have : CharP K 2 := charP_two_of_card_d4 hK
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    even_triality_exact_automorphism_normal_form (by omega : 1 ≤ m) K hK σ hσq
  have hinner : ∀ β : MulAut ↥(d4C K σ), β ∈ inner ↥(d4C K σ) → (∃ j : ℕ, β ^ 2 ^ j = 1) →
      (∀ y ∈ Q, β y = y) → (∀ y ∈ L, β y = y) → β = 1 := by
    rintro β ⟨c, rfl⟩ ⟨j, hj⟩ hβQ hβL
    rw [conj_eq_one_of_fix_d4 hZ hL hHodd hj hβQ hβL, map_one]
  intro α ⟨k, hk⟩ hQ hLf
  have hfix : ∀ (S : Subgroup ↥(d4C K σ)), (∀ y ∈ S, α y = y) →
      ∀ n : ℕ, ∀ y ∈ S, (α ^ n) y = y := by
    intro S hS n
    induction n with
    | zero => intro y _; rfl
    | succ n ih => intro y hy; rw [pow_succ, MulAut.mul_apply, hS y hy, ih y hy]
  have hpow2 : ∀ n : ℕ, ∃ j : ℕ, (α ^ n) ^ 2 ^ j = 1 :=
    fun n => ⟨k, by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]⟩
  have hex : ∃ j, α ^ 2 ^ j ∈ inner ↥(d4C K σ) := ⟨k, by rw [hk]; exact one_mem _⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · have hα := Nat.find_spec hex
    rw [h0, pow_zero, pow_one] at hα
    exact hinner α hα ⟨k, hk⟩ hQ hLf
  · exfalso
    obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hβo : α ^ 2 ^ j ∉ inner ↥(d4C K σ) := Nat.find_min hex (by omega)
    have hβ2' : (α ^ 2 ^ j) ^ 2 ∈ inner ↥(d4C K σ) := by
      rw [← pow_mul, ← pow_succ, ← hj]
      exact Nat.find_spec hex
    have hβ2 : (α ^ 2 ^ j) ^ 2 = 1 := by
      rw [← pow_mul]
      exact hinner _ (by rw [pow_mul]; exact hβ2') (hpow2 _) (hfix Q hQ _) (hfix L hLf _)
    obtain ⟨⟨e, he⟩, δ, hδ, -, ψ, hψ, -⟩ := even_triality_outer_involutions_canonical_field
      (by omega : 1 ≤ m) K hK σ hσq (α ^ 2 ^ j) hβ2 hβo
    have he1 : 1 ≤ e := by omega
    have hme : m = 2 * e := by omega
    have hK6 : Nat.card K = 2 ^ (6 * e) := by
      rw [hK, ← pow_mul, hme]
      ring_nf
    have hσ2e : ∀ c, σ c = c ^ 2 ^ (2 * e) := fun c => by rw [hσq, hme]
    have hδ3e : ∀ c, δ c = c ^ 2 ^ (3 * e) := fun c => by
      rw [hδ, show 3 * m / 2 = 3 * e by omega]
    obtain ⟨-, hk0, hσ0, -, -, hJ, -⟩ :=
      even_triality_canonical_field_full_centralizer he1 K hK6 σ hσ2e δ hδ3e
    have hLmap : L.map ψ.toMonoidHom ≤ (fieldActor σ δ).toMonoidHom.eqLocus (MonoidHom.id _) := by
      rintro _ ⟨y, hy, rfl⟩
      show fieldActor σ δ (ψ y) = ψ y
      rw [← hψ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfix L hLf _ y hy]
    have hcardL : Nat.card L ∣ Nat.card (trialityFieldImage σ δ) := by
      rw [← hJ, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        ← Subgroup.card_map_of_injective (K := L) (f := ψ.toMonoidHom) ψ.injective]
      exact Subgroup.card_dvd_of_le hLmap
    have : Finite (fixSubfield δ) := Subtype.finite
    have hK0 : Nat.card (fixSubfield δ) = (2 ^ e) ^ 3 := by
      rw [hk0, ← pow_mul, mul_comm]
    have hσ0' : ∀ c, (fixSubfieldRestrict σ δ).toRingHom c = c ^ ((2 ^ e) ^ 2) := fun c => by
      refine Subtype.ext ?_
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ0, SubmonoidClass.coe_pow,
        hσ2e, ← pow_mul, mul_comm]
    obtain ⟨hcard, -⟩ := triality_both_orientations_exact_finite_order 2 e Nat.prime_two he1
      (fixSubfield δ) hK0 2 (Or.inr rfl) _ hσ0'
    have hJcard : Nat.card (trialityFieldImage σ δ) = (2 ^ e) ^ 12 * ((2 ^ e) ^ 2 - 1) *
        ((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1) := by
      rw [trialityFieldImage, Subgroup.card_map_of_injective (baseChangeGL_injective _), hcard]
    have hcop := coprime_card_d4 he1
    rw [← hme, ← hJcard] at hcop
    have h1 := Nat.Coprime.eq_one_of_dvd hcop (hqL.trans hcardL)
    have := Nat.two_pow_pos m
    omega

theorem odd_two_pow_sub_one_d4 {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  refine ⟨2 ^ i - 1, ?_⟩
  rw [pow_succ]
  have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  omega

omit [Finite K] in
theorem d4Ma_le_d4Lz :
    d4Ma K σ ≤ d4Lz K σ :=
  (closure_le _).2 (by
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;> dsimp only
    · rw [coe_orbitX_one_d4]
      exact d4x₂_mem_d4Lz σ ((mem_orbitField_D4_one σ).1 c.2)
    · rw [coe_orbitY_one_d4]
      exact d4y₂_mem_d4Lz σ ((mem_orbitField_D4_one σ).1 c.2))

theorem d4_autFix_z
    (m : ℕ) (hm : 2 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3)
    (hσq : ∀ c, σ c = c ^ 2 ^ m) :
    Exc.AutFix ((d4W0 K σ).subgroupOf (d4C K σ)) ((d4Lz K σ).subgroupOf (d4C K σ)) := by
  have : CharP K 2 := charP_two_of_card_d4 hK
  have hσ3' := sigma_cube_of_card_d4 σ hK hσq
  have hσ := ringEquiv_cube_d4 σ hσ3'
  have hk : Nat.card (d4k K σ) = 2 ^ m := card_d4k_of_card σ (by omega) hK hσq
  obtain ⟨-, -, -, hL2, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ
  have hk' : Nat.card (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) = 2 ^ m := by
    rw [hL2]; exact hk
  have : Finite (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) := Subtype.finite
  obtain ⟨hL, -⟩ := d4_leviData_z σ m hm hK hσq
  refine d4_autFix σ m hm hK hσq hL ?_ ?_
  · obtain ⟨-, hH, -⟩ := triality_both_orientations_exact_finite_order 2 m Nat.prime_two
      (by omega) K hK 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσq c)
    rw [Nat.card_congr (subgroupOfEquivOfLe (d4H_le σ)).toEquiv, hH, ← pow_mul]
    exact (odd_two_pow_sub_one_d4 (by omega)).mul (odd_two_pow_sub_one_d4 (by omega))
  · rw [Nat.card_congr (subgroupOfEquivOfLe (d4Lz_le σ)).toEquiv]
    refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le (d4Ma_le_d4Lz σ))
    rw [Nat.card_congr (d4MaEquiv σ hσ).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk']
    exact succ_dvd_card_sl2_d4 _

theorem d4_autFix_t
    (m : ℕ) (hm : 2 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 3)
    (hσq : ∀ c, σ c = c ^ 2 ^ m) :
    Exc.AutFix ((d4Qt K σ).subgroupOf (d4C K σ)) ((d4Lt K σ).subgroupOf (d4C K σ)) := by
  have : CharP K 2 := charP_two_of_card_d4 hK
  have hσ3' := sigma_cube_of_card_d4 σ hK hσq
  have hσ3 := toRingHom_pow_three_d4 σ hσ3'
  have hσ := ringEquiv_cube_d4 σ hσ3'
  obtain ⟨hL, -⟩ := d4_leviData_t σ m hm hK hσq
  refine d4_autFix σ m hm hK hσq hL hL.odd_Q ?_
  rw [Nat.card_congr (subgroupOfEquivOfLe (d4Lt_le σ hσ3)).toEquiv,
    Nat.card_congr (d4LtEquiv σ hσ3 hσ).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
  exact succ_dvd_card_sl2_cube_d4 _

end AutFixSec

end CFSG.ComponentClassification.RankTwoExceptional.D4
