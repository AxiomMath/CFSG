module

public import CFSG.GroupTheory.PCore.Defs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.CGT.Foote81L6.Normalizer

theorem oddCore_eq_pPrimeCore_two (G : Type*) [Group G] :
    CFSG.oddCore G = pPrimeCore 2 G := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem map_pPrimeCore_le {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal] :
    (pPrimeCore 2 N).map N.subtype ≤ pPrimeCore 2 G := by
  refine le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, ?_⟩
  rw [Subgroup.card_map_of_injective N.subtype_injective]
  exact pPrimeCore_coprime_card

theorem eq_one_of_pow_two_pow_of_odd {G : Type*} [Group G] {y : G} {k : ℕ}
    (hk : y ^ 2 ^ k = 1) (hy : Odd (orderOf y)) : y = 1 := by
  have hdvd := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf y) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hy)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem conj_fix_of_odd {G : Type*} [Group G] {y a b : G} (hy : Odd (orderOf y))
    (hab : a ≠ b) (ha : y * a * y⁻¹ = a ∨ y * a * y⁻¹ = b)
    (hb : y * b * y⁻¹ = a ∨ y * b * y⁻¹ = b) : y * a * y⁻¹ = a := by
  rcases ha with ha | ha
  · exact ha
  · exfalso
    have hb' : y * b * y⁻¹ = a := by
      rcases hb with hb | hb
      · exact hb
      · exfalso
        apply hab
        have := ha.trans hb.symm
        have h2 : y⁻¹ * (y * a * y⁻¹) * y = y⁻¹ * (y * b * y⁻¹) * y := by rw [this]
        simpa [mul_assoc] using h2
    have hsq : (y * y) * a * (y * y)⁻¹ = a := by
      calc (y * y) * a * (y * y)⁻¹ = y * (y * a * y⁻¹) * y⁻¹ := by
            simp only [mul_inv_rev, mul_assoc]
        _ = a := by rw [ha, hb']
    have hpow : ∀ n : ℕ, (y * y) ^ n * a * ((y * y) ^ n)⁻¹ = a := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ]
        calc (y * y) ^ n * (y * y) * a * ((y * y) ^ n * (y * y))⁻¹
            = (y * y) ^ n * ((y * y) * a * (y * y)⁻¹) * ((y * y) ^ n)⁻¹ := by
              simp only [mul_inv_rev, mul_assoc]
          _ = a := by rw [hsq, ih]
    obtain ⟨j, hj⟩ := hy
    have hyj : (y * y) ^ (j + 1) = y := by
      rw [← pow_two, ← pow_mul, show 2 * (j + 1) = orderOf y + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    apply hab
    rw [← ha, ← hyj, hpow]

theorem exists_conj_mem_sylow_two {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    {t : G} (ht : t * t = 1) : ∃ g : G, g * t * g⁻¹ ∈ (P : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers t) := by
    rintro ⟨s, hs⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, ht, one_zpow]
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R P
  refine ⟨g, ?_⟩
  rw [← hg]
  exact ⟨t, hR (Subgroup.mem_zpowers t), by simp [MulAut.conj_apply]⟩

theorem eq_of_mk_eq_of_mem_sylow {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    {a b : G} (ha : a ∈ (P : Subgroup G)) (hb : b ∈ (P : Subgroup G))
    (hab : (QuotientGroup.mk a : G ⧸ pPrimeCore 2 G) = QuotientGroup.mk b) : a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : a⁻¹ * b ∈ pPrimeCore 2 G := QuotientGroup.eq.mp hab
  have h2 : a⁻¹ * b ∈ (P : Subgroup G) := (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem ha) hb
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨a⁻¹ * b, h2⟩
  have hk' : (a⁻¹ * b) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hodd : Odd (orderOf (a⁻¹ * b)) := by
    have hdvd := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 G) h1
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat hdvd
  have := eq_one_of_pow_two_pow_of_odd hk' hodd
  rw [inv_mul_eq_one] at this
  exact this

theorem mem_of_index_two_of_odd_orderOf {G : Type*} [Group G] {Y : Subgroup G}
    (hY : Y.index = 2) {x : G} (hx : Odd (orderOf x)) : x ∈ Y := by
  obtain ⟨k, hk⟩ := hx
  have h1 : x * (x ^ 2) ^ k = 1 := by
    rw [← pow_mul, ← pow_succ', show 2 * k + 1 = orderOf x by omega, pow_orderOf_eq_one]
  rw [eq_inv_of_mul_eq_one_left h1]
  exact Y.inv_mem (Y.pow_mem (Subgroup.sq_mem_of_index_two hY x) k)

theorem odd_orderOf_of_mem_pPrimeCore {G : Type*} [Group G] [Finite G] {x : G}
    (hx : x ∈ pPrimeCore 2 G) : Odd (orderOf x) :=
  (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
    (Subgroup.orderOf_dvd_natCard (pPrimeCore 2 G) hx)

end CFSG.CGT.Foote81L6.Normalizer
