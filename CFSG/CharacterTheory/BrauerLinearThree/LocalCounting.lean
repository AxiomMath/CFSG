module

public import CFSG.CharacterTheory.BrauerLinearThree.LocalFacts
public import CFSG.CharacterTheory.BrauerLinearThree.LocalSetting
public import CFSG.CharacterTheory.BrauerLinearThree.LocalTools

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

section Arith

variable {G : Type} [Group G]

theorem card_dvd_of_isPGroup_of_le {p : ℕ} (hp : p.Prime) {H K : Subgroup G} [Finite K]
    (hH : IsPGroup p H) (hHK : H ≤ K) {e l R : ℕ} (hK : Nat.card K * l = p ^ e * R)
    (hR : Nat.Coprime p R) : Nat.card H ∣ p ^ e := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite H := Finite.of_injective _ (Subgroup.inclusion_injective hHK)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hH
  rw [hn]
  have h1 : p ^ n ∣ p ^ e * R := by
    rw [← hK, ← hn]
    exact (Subgroup.card_dvd_of_le hHK).mul_right l
  exact (Nat.Coprime.pow_left n hR).dvd_of_dvd_mul_right h1

theorem coprime_sub_one_and_add_one {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : 1 ≤ n) :
    Nat.Coprime p (n - 1) ∧ Nat.Coprime p (n + 1) := by
  constructor
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have : p ∣ n - (n - 1) := Nat.dvd_sub hpn h
    rw [Nat.sub_sub_self hn] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have : p ∣ (n + 1) - n := Nat.dvd_sub h hpn
    rw [Nat.add_sub_cancel_left] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)

end Arith

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

section Centralizer

omit [Z.Normal] in
include hZ in
theorem coprime_facts :
    Nat.Coprime (ringChar F) (Nat.card Z) ∧
      Nat.Coprime (ringChar F) ((Nat.card F - 1) ^ 2 * (Nat.card F + 1)) ∧
      Nat.Coprime (ringChar F) ((Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) := by
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  obtain ⟨f, hf, hq⟩ := exists_card_eq_ringChar_pow F
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have hpq : ringChar F ∣ Nat.card F := by rw [hq]; exact dvd_pow_self _ hf.ne'
  have h1 := coprime_sub_one_and_add_one hp hpq hq1
  have h3 := coprime_sub_one_and_add_one hp (hpq.pow (by norm_num : 3 ≠ 0))
    (Nat.one_le_pow _ _ hq1)
  have h2' := coprime_sub_one_and_add_one hp (hpq.pow (by norm_num : 2 ≠ 0))
    (Nat.one_le_pow _ _ hq1)
  refine ⟨coprime_ringChar_card_Z hZ, ?_, ?_⟩
  · exact Nat.Coprime.mul_right (h1.1.pow_right 2) h1.2
  · exact Nat.Coprime.mul_right h3.1 h2'.1

include φ hZ in
theorem card_dvd_of_isPGroup_le_centralizer {H : Subgroup G}
    (hH : IsPGroup (ringChar F) H) (hHC : H ≤ Subgroup.centralizer {J}) :
    Nat.card H ∣ Nat.card F := by
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  obtain ⟨f, hf, hq⟩ := exists_card_eq_ringChar_pow F
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  rw [hq]
  apply card_dvd_of_isPGroup_of_le hp hH hHC (l := Nat.card Z)
    (R := (Nat.card F - 1) ^ 2 * (Nat.card F + 1)) _ (coprime_facts hZ).2.1
  rw [card_centralizer_J φ, hq]
  ring

include φ hZ in
theorem not_sq_dvd_card_centralizer :
    ¬ Nat.card F ^ 2 ∣ Nat.card (Subgroup.centralizer ({J} : Set G)) := by
  intro h
  obtain ⟨f, hf, hq⟩ := exists_card_eq_ringChar_pow F
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have hcop := (coprime_facts hZ).2.1
  have h1 : (ringChar F) ^ (2 * f) ∣ (ringChar F) ^ f *
      ((Nat.card F - 1) ^ 2 * (Nat.card F + 1)) := by
    have := (h.mul_right (Nat.card Z))
    rw [card_centralizer_J φ, hq, ← pow_mul, mul_comm f 2] at this
    rw [← hq]
    convert this using 1
    rw [hq]
    ring
  have h3 := (Nat.Coprime.pow_left (2 * f) hcop).dvd_of_dvd_mul_right h1
  have := Nat.pow_dvd_pow_iff_le_right hp.one_lt |>.mp h3
  omega

include φ hZ in
theorem not_dvd_sq_card_centralizer :
    ¬ Nat.card F ^ 2 * ringChar F ∣ Nat.card (Subgroup.centralizer ({J} : Set G)) ^ 2 := by
  intro h
  obtain ⟨f, hf, hq⟩ := exists_card_eq_ringChar_pow F
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have hcop := (coprime_facts hZ).2.1
  have h1 : (ringChar F) ^ (2 * f + 1) ∣ (ringChar F) ^ (2 * f) *
      ((Nat.card F - 1) ^ 2 * (Nat.card F + 1)) ^ 2 := by
    have := (h.mul_right (Nat.card Z ^ 2))
    have e : Nat.card (Subgroup.centralizer ({J} : Set G)) ^ 2 * Nat.card Z ^ 2 =
        (Nat.card (Subgroup.centralizer ({J} : Set G)) * Nat.card Z) ^ 2 := by ring
    rw [e, card_centralizer_J φ] at this
    have e2 : Nat.card F ^ 2 * ringChar F = ringChar F ^ (2 * f + 1) := by
      rw [hq, ← pow_mul, pow_succ, mul_comm f 2]
    rw [e2] at this
    convert this using 1
    rw [hq]
    ring
  have h3 := (Nat.Coprime.pow_left (2 * f + 1) (hcop.pow_right 2)).dvd_of_dvd_mul_right h1
  have := Nat.pow_dvd_pow_iff_le_right hp.one_lt |>.mp h3
  omega

end Centralizer

section Group

variable (hcard : Nat.card G * Nat.card Z =
  Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))

include φ hcard in
theorem card_eq_card_centralizer_mul :
    Nat.card G = Nat.card (Subgroup.centralizer ({J} : Set G)) *
      (Nat.card F ^ 2 * (Nat.card F ^ 2 + Nat.card F + 1)) := by
  have hl : 0 < Nat.card Z := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hl
  rw [hcard, show Nat.card (Subgroup.centralizer ({J} : Set G)) *
      (Nat.card F ^ 2 * (Nat.card F ^ 2 + Nat.card F + 1)) * Nat.card Z =
      (Nat.card (Subgroup.centralizer ({J} : Set G)) * Nat.card Z) *
      (Nat.card F ^ 2 * (Nat.card F ^ 2 + Nat.card F + 1)) by ring, card_centralizer_J φ]
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have hq2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ hq1
  have hq3 : 1 ≤ Nat.card F ^ 3 := Nat.one_le_pow _ _ hq1
  zify [hq1, hq2, hq3]
  ring

include φ h2 hcard in
theorem exists_sylow_two_le_centralizer [Finite G] :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.centralizer {J} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply exists_sylow_le_of_factorization_eq 2 (Subgroup.centralizer {J})
  have hq : Odd (Nat.card F) := odd_card_F h2
  have hodd : Odd (Nat.card F ^ 2 * (Nat.card F ^ 2 + Nat.card F + 1)) :=
    hq.pow.mul ((hq.pow.add_odd hq).add_one)
  have hnd : ¬ 2 ∣ Nat.card F ^ 2 * (Nat.card F ^ 2 + Nat.card F + 1) := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  rw [card_eq_card_centralizer_mul φ hcard,
    Nat.factorization_mul Nat.card_pos.ne' hodd.pos.ne',
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]

include hZ hZodd h2 hJ hcard in
theorem conj_eq_of_mem_centerSub [Finite G] {z : G} (hz : z ∈ centerSub φ) (g : G)
    (hg : g * z * g⁻¹ ∈ centerSub φ) : g * z * g⁻¹ = z := by
  obtain ⟨S, hS⟩ := exists_sylow_two_le_centralizer φ h2 hcard
  have hN := normalizer_sylow_le_centralizer φ hZ hZodd h2 hJ S hS
  have := eq_of_conj_mem_centerSub φ S hS hN hz g⁻¹ (by rwa [inv_inv])
  rwa [inv_inv] at this

omit [Z.Normal] in
include hZ hcard in
theorem card_dvd_cube_of_isPGroup [Finite G] {H : Subgroup G} (hH : IsPGroup (ringChar F) H) :
    Nat.card H ∣ Nat.card F ^ 3 := by
  obtain ⟨f, hf, hq⟩ := exists_card_eq_ringChar_pow F
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  rw [hq, ← pow_mul]
  apply card_dvd_of_isPGroup_of_le hp hH (le_top : H ≤ ⊤) (l := Nat.card Z)
    (R := (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) _ (coprime_facts hZ).2.2
  rw [Subgroup.card_top, hcard, pow_mul, ← hq]
  ring

omit [Group G] [Z.Normal] in
include hZ hcard in
theorem cube_dvd_card : Nat.card F ^ 3 ∣ Nat.card G := by
  obtain ⟨f, hf, hq⟩ := exists_card_eq_ringChar_pow F
  have hcop : Nat.Coprime (Nat.card F ^ 3) (Nat.card Z) := by
    rw [hq, ← pow_mul]
    exact Nat.Coprime.pow_left _ (coprime_facts hZ).1
  apply hcop.dvd_of_dvd_mul_right
  rw [hcard, mul_assoc]
  exact dvd_mul_right _ _

end Group

end CFSG.BrauerLinearThree
