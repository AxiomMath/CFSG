module

public import CFSG.ClassicalInvolution.Q3.TA3FrameBase
public import CFSG.ClassicalInvolution.Q3.Q3T7EndF1

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS

variable {Y : Type} [Group Y] [Finite Y] {z : Y} {L T : Subgroup Y}

theorem exists_cube_element [T.Normal] (hL : IsClassicalMember3 L z) (h3 : memberIndex L T = 3)
    (hP2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer ({z} : Set Y))) :
    ∃ y ∈ L, y ∉ T ∧ y ^ 3 = 1 := by
  classical
  obtain ⟨y, hyL, hyT, k, hk⟩ := exists_three_element hL h3
  have hex : ∃ m, y ^ 3 ^ m ∈ T := ⟨k, by rw [hk]; exact one_mem T⟩
  have hm : y ^ 3 ^ Nat.find hex ∈ T := Nat.find_spec hex
  obtain ⟨m', hm'⟩ : ∃ m', Nat.find hex = m' + 1 := by
    refine ⟨Nat.find hex - 1, ?_⟩
    have h0 : Nat.find hex ≠ 0 := fun h0 => hyT (by rw [h0, pow_zero, pow_one] at hm; exact hm)
    omega
  have hnot : y ^ 3 ^ m' ∉ T := Nat.find_min hex (by omega)
  refine ⟨y ^ 3 ^ m', pow_mem hyL _, hnot, ?_⟩
  have h1 : (y ^ 3 ^ m') ^ 3 = y ^ 3 ^ Nat.find hex := by rw [← pow_mul, ← pow_succ, hm']
  rw [h1]
  have hmem : y ^ 3 ^ Nat.find hex ∈ T ⊓ Subgroup.centralizer ({z} : Set Y) :=
    ⟨hm, pow_mem (hL.le_centralizer hyL) _⟩
  obtain ⟨n, hn⟩ := hP2 ⟨_, hmem⟩
  have h2 : (y ^ 3 ^ Nat.find hex) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have h3' : (y ^ 3 ^ Nat.find hex) ^ 3 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]
  have hcop : Nat.Coprime (2 ^ n) (3 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2)
    (orderOf_dvd_of_pow_eq_one h3'))

theorem card_le_eight_mul_fix [T.Normal] (hL : IsClassicalMember3 L z)
    (hP2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer ({z} : Set Y))) {y : Y} (hyL : y ∈ L)
    (hy3 : y ^ 3 = 1) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({z} : Set Y)) ≤
      8 * Nat.card ↥((T ⊓ Subgroup.centralizer ({z} : Set Y)) ⊓
        Subgroup.centralizer (Subgroup.zpowers y : Set Y)) := by
  set C := Subgroup.centralizer ({z} : Set Y) with hC
  set P := T ⊓ C with hPdef
  set A := Subgroup.zpowers y with hA
  have hA3 : IsPGroup 3 A := by
    rintro ⟨g, hg⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hyz : y ∈ C := hL.le_centralizer hyL
  have hyN : y ∈ Subgroup.normalizer (P : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hxT, hxz⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(inferInstance : T.Normal).conj_mem x hxT y,
        C.mul_mem (C.mul_mem hyz hxz) (C.inv_mem hyz)⟩
    · intro hx
      obtain ⟨hxT, hxz⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have := (inferInstance : T.Normal).conj_mem _ hxT y⁻¹
        simpa [mul_assoc] using this
      · have := C.mul_mem (C.mul_mem (C.inv_mem hyz) hxz) hyz
        simpa [mul_assoc] using this
  have hnorm : A ≤ Subgroup.normalizer (P : Set Y) := Subgroup.zpowers_le.mpr hyN
  have hcop : ¬ 3 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    rw [hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three A P hA3 hcop hnorm
  set N : Subgroup Y := ⁅P, A⁆ with hN
  set D : Subgroup Y := P ⊓ Subgroup.centralizer (A : Set Y) with hD
  have hNP : N ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hnorm
  have hNL : N ≤ L := Q3T.MFS.commutator_zpowers_le_of_isSubnormal Nat.prime_three
    hL.subnormal hyL hA3 inf_le_right hnorm hcop
  have hN8 : Nat.card N ≤ 8 :=
    (Subgroup.card_le_of_le (le_inf hNL hNP)).trans (hL.card_inf_le_eight hP2)
  have hNn : (N.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr
      (Subgroup.normalizer_commutator_ge_left P A)
  let φ : ↥N × ↥D → ↥P := fun nc =>
    ⟨nc.1 * nc.2, P.mul_mem (hNP nc.1.2) nc.2.2.1⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, hab⟩ :=
      CFSG.RankThreeEvenClassification.Helpers.normal_subgroup_sup_factorization P N D hNP
        inf_le_left hNn hfac x hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc Nat.card P ≤ Nat.card (↥N × ↥D) := Nat.card_le_card_of_surjective φ hφ
    _ = Nat.card N * Nat.card D := Nat.card_prod _ _
    _ ≤ 8 * Nat.card D := Nat.mul_le_mul_right _ hN8

theorem false_of_fix_le_four [T.Normal] (hL : IsClassicalMember3 L z) (h3 : memberIndex L T = 3)
    (hP2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer ({z} : Set Y)))
    (hP : 64 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({z} : Set Y)))
    (hfix : ∀ y : Y, y ∉ T → y ^ 3 = 1 → y * z = z * y →
      Nat.card ↥((T ⊓ Subgroup.centralizer ({z} : Set Y)) ⊓
        Subgroup.centralizer (Subgroup.zpowers y : Set Y)) ≤ 4) : False := by
  obtain ⟨y, hyL, hyT, hy3⟩ := exists_cube_element hL h3 hP2
  have h8 := card_le_eight_mul_fix hL hP2 hyL hy3
  have h4 := hfix y hyT hy3 (Subgroup.mem_centralizer_singleton_iff.mp (hL.le_centralizer hyL))
  omega

end CFSG.ClassicalInvolution.Q3.TA3.Frame
