module

public import CFSG.LocalAnalysis.ComponentInitial.CyclicAbelianPrimeCenter
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SquareRoots

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {P : Type*} [Group P]

theorem cyclic_abelian_of_subgroup (K : Subgroup P)
    (hcyc : ∀ B : Subgroup P, IsMulCommutative B → IsCyclic B) :
    ∀ B : Subgroup K, IsMulCommutative B → IsCyclic B := by
  intro B _
  have := hcyc (B.map K.subtype) inferInstance
  exact isCyclic_of_surjective
    (B.equivMapOfInjective K.subtype K.subtype_injective).symm.toMonoidHom
    (B.equivMapOfInjective K.subtype K.subtype_injective).symm.surjective

theorem cyclic_abelian_involution_unique [Finite P] (hP : IsPGroup 2 P)
    (hnab : ∃ x y : P, x * y ≠ y * x) (hcyc : ∀ B : Subgroup P, IsMulCommutative B → IsCyclic B)
    {a b : P} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hZ⟩ := cyclic_abelian_prime_and_center Nat.prime_two hP hnab hcyc
  obtain ⟨-, hinv⟩ := cyclic_abelian_center_comparison Nat.prime_two hP hnab hcyc
  have ha1 : (⟨a, hinv a ha⟩ : center P) ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at ha
    omega
  have htop := zpowers_eq_top_of_prime_card hZ ha1
  have hmem : (⟨b, hinv b hb⟩ : center P) ∈ zpowers (⟨a, hinv a ha⟩ : center P) :=
    htop ▸ mem_top _
  rw [mem_zpowers_iff_mem_range_orderOf, Subgroup.orderOf_mk, ha] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨i, hi, hib⟩ := hmem
  interval_cases i
  · have h1 : (1 : P) = b := by simpa using congrArg Subtype.val hib
    rw [← h1, orderOf_one] at hb
    omega
  · simpa using congrArg Subtype.val hib

theorem cyclic_abelian_index_two_cyclic {p : ℕ} (hp : p.Prime) [Finite P] (hP : IsPGroup p P)
    (hnab : ∃ x y : P, x * y ≠ y * x) (hcyc : ∀ B : Subgroup P, IsMulCommutative B → IsCyclic B) :
    ∃ N : Subgroup P, N.Normal ∧ IsCyclic N ∧ Nat.card N = 4 ∧
      N ≤ centralizer (N : Set P) ∧ IsCyclic (centralizer (N : Set P)) ∧
      (centralizer (N : Set P)).index = 2 ∧
      N.subgroupOf (centralizer (N : Set P)) ≤ center (centralizer (N : Set P)) := by
  classical
  obtain ⟨hp2, hZ⟩ := cyclic_abelian_prime_and_center hp hP hnab hcyc
  subst hp2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    have hdvd : Nat.card (center P) ∣ 2 ^ n := hn ▸ Subgroup.card_subgroup_dvd_card _
    rw [hZ] at hdvd
    interval_cases n
    · norm_num at hdvd
    · have htop : center P = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hZ, hn, pow_one])
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy ((mem_center_iff.1 (htop ▸ mem_top y) x))
  have : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨N, hN4, hNn⟩ := Group.IsNilpotent.exists_normal_card_eq_of_dvd_card (G := P) (n := 4)
    (by rw [hn, show (4 : ℕ) = 2 ^ 2 by norm_num]; exact pow_dvd_pow 2 hn2)
  have hNcomm : IsMulCommutative N :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hN4]; norm_num)
  have hNcyc : IsCyclic N := hcyc N hNcomm
  have hNK : N ≤ centralizer (N : Set P) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hNcomm.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hNZK : N.subgroupOf (centralizer (N : Set P)) ≤ center (centralizer (N : Set P)) := by
    intro a ha
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 g.2 a ha).symm
  have hker : (MulAut.conjNormal (H := N)).ker = centralizer (N : Set P) := by
    ext x
    rw [MonoidHom.mem_ker, mem_centralizer_iff]
    constructor
    · intro h n hn
      have h1 := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : P)) h
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    · intro h
      ext ⟨n, hn⟩
      simp only [MulAut.conjNormal_apply, MulAut.one_apply]
      rw [mul_inv_eq_iff_eq_mul]
      exact (h n hn).symm
  have hcardAut : Nat.card (MulAut N) = 2 := by
    rw [Nat.card_congr (IsCyclic.mulAutMulEquiv N).toEquiv, hN4, Nat.card_eq_fintype_card]
    decide
  have hidx : (centralizer (N : Set P)).index = 2 := by
    have h1 : (centralizer (N : Set P)).index ∣ 2 := by
      rw [← hker, Subgroup.index_ker, ← hcardAut]
      exact Subgroup.card_subgroup_dvd_card _
    have h2 : (centralizer (N : Set P)).index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      intro htop
      have hNZ : N ≤ center P := fun a ha => mem_center_iff.2 fun g =>
        (mem_centralizer_iff.1 (htop ▸ mem_top g) a ha).symm
      have := Subgroup.card_le_of_le hNZ
      rw [hN4, hZ] at this
      omega
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd h h2
    · exact h
  have hKcomm : IsMulCommutative (centralizer (N : Set P)) := by
    by_contra hK
    have hnabK : ∃ x y : centralizer (N : Set P), x * y ≠ y * x := by
      by_contra h
      push Not at h
      exact hK ⟨⟨h⟩⟩
    obtain ⟨-, hZK⟩ := cyclic_abelian_prime_and_center Nat.prime_two (hP.to_subgroup _) hnabK
      (cyclic_abelian_of_subgroup _ hcyc)
    have := Subgroup.card_le_of_le hNZK
    rw [hZK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv, hN4] at this
    omega
  exact ⟨N, hNn, hNcyc, hN4, hNK, hcyc _ hKcomm, hidx, hNZK⟩

theorem order_four_outside_cyclic_index_two [Finite P] (hP : IsPGroup 2 P)
    (hnab : ∃ x y : P, x * y ≠ y * x) (hcyc : ∀ B : Subgroup P, IsMulCommutative B → IsCyclic B)
    {K : Subgroup P} (hKc : IsCyclic K) (hK2 : K.index = 2) : ∃ y : P, y ∉ K ∧ orderOf y = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hZ⟩ := cyclic_abelian_prime_and_center Nat.prime_two hP hnab hcyc
  obtain ⟨-, hinv⟩ := cyclic_abelian_center_comparison Nat.prime_two hP hnab hcyc
  obtain ⟨g, hg⟩ := hKc.exists_generator
  have hKg : K = zpowers (g : P) := by
    apply le_antisymm
    · intro a ha
      obtain ⟨i, hi⟩ := hg ⟨a, ha⟩
      replace hi : g ^ i = ⟨a, ha⟩ := hi
      exact ⟨i, by
        show (g : P) ^ i = a
        rw [← Subgroup.coe_zpow, hi]⟩
    · exact (zpowers_le).2 g.2
  obtain ⟨m, hm⟩ := hP.exists_orderOf_eq_pow (g : P)
  have hcardK : Nat.card K = 2 ^ m := by rw [hKg, Nat.card_zpowers, hm]
  have hcardP : Nat.card P = 2 * 2 ^ m := by
    rw [← K.index_mul_card, hK2, hcardK]
  have hm2 : 2 ≤ m := by
    by_contra h
    push Not at h
    have hle : Nat.card P ∣ 2 ^ 2 := by
      rw [hcardP, ← pow_succ']
      exact pow_dvd_pow 2 (by omega)
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hle
    have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := P) (p := 2)
    interval_cases j
    · obtain ⟨x, y, hxy⟩ := hnab
      have : Subsingleton P := (Nat.card_eq_one_iff_unique.1 (by simpa using hj')).1
      exact hxy (Subsingleton.elim _ _)
    · have : IsCyclic P := isCyclic_of_prime_card (p := 2) (by simpa using hj')
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy ((inferInstance : IsMulCommutative P).is_comm.comm x y)
    · obtain ⟨x, y, hxy⟩ := hnab
      exact hxy ((hcomm hj').is_comm.comm x y)
  have hdvdg : 2 ^ (m - 2) ∣ orderOf (g : P) := by
    rw [hm]
    exact pow_dvd_pow 2 (by omega)
  have hu4 : orderOf ((g : P) ^ (2 ^ (m - 2))) = 4 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvdg, hm, Nat.pow_div (by omega) two_pos,
      show m - (m - 2) = 2 by omega]
    norm_num
  by_contra hall
  push Not at hall
  have hcent : ∀ x : P, x * (g : P) ^ (2 ^ (m - 2)) = (g : P) ^ (2 ^ (m - 2)) * x := by
    intro x
    obtain ⟨j, hj⟩ := hP.exists_orderOf_eq_pow x
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · rw [pow_zero, orderOf_eq_one_iff] at hj
        rw [hj, one_mul, mul_one]
      · exact (mem_center_iff.1 (hinv x (by rw [hj, pow_one])) _).symm
    ·
      have hdvdx : 2 ^ (j - 2) ∣ orderOf x := by
        rw [hj]
        exact pow_dvd_pow 2 (by omega)
      have hw4 : orderOf (x ^ (2 ^ (j - 2))) = 4 := by
        rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvdx, hj,
          Nat.pow_div (by omega) two_pos, show j - (j - 2) = 2 by omega]
        norm_num
      have hwK : x ^ (2 ^ (j - 2)) ∈ K := by
        by_contra hwK
        exact hall _ hwK hw4
      have : IsCyclic K := hKc
      have heq : zpowers (x ^ (2 ^ (j - 2))) = zpowers ((g : P) ^ (2 ^ (m - 2))) :=
        eq_of_le_cyclic_of_card_eq K ((zpowers_le).2 hwK)
          ((zpowers_le).2 (pow_mem g.2 _)) (by rw [Nat.card_zpowers, Nat.card_zpowers, hw4, hu4])
      have hmem : (g : P) ^ (2 ^ (m - 2)) ∈ zpowers (x ^ (2 ^ (j - 2))) := heq ▸ mem_zpowers _
      obtain ⟨i, hi⟩ := hmem
      replace hi : (x ^ (2 ^ (j - 2))) ^ i = (g : P) ^ (2 ^ (m - 2)) := hi
      rw [← hi]
      exact ((Commute.self_pow x _).zpow_right i).eq
  have hUZ : zpowers ((g : P) ^ (2 ^ (m - 2))) ≤ center P :=
    (zpowers_le).2 (mem_center_iff.2 hcent)
  have := Subgroup.card_le_of_le hUZ
  rw [Nat.card_zpowers, hu4, hZ] at this
  omega

theorem quaternion_conjugation_forcing [Finite P] (hP : IsPGroup 2 P)
    (hnab : ∃ x y : P, x * y ≠ y * x) (hcyc : ∀ B : Subgroup P, IsMulCommutative B → IsCyclic B)
    {N : Subgroup P} (_hNn : N.Normal) (hNc : IsCyclic N) (hN4 : Nat.card N = 4) {x : P}
    (hK : centralizer (N : Set P) = zpowers x) (hK2 : (zpowers x).index = 2)
    {y : P} (hy : y ∉ zpowers x) (hy4 : orderOf y = 4) :
    y * x * y⁻¹ = x⁻¹ ∧
      ∀ k : ℕ, Nat.card (zpowers x) = 2 ^ k → 2 ≤ k ∧ y ^ 2 = x ^ (2 ^ (k - 1)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNcomm : IsMulCommutative N := inferInstance
  have hNK : N ≤ zpowers x := by
    rw [← hK]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hNcomm.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow x
  have hcardK : Nat.card (zpowers x) = 2 ^ k := by rw [Nat.card_zpowers, hk]
  have hk2 : 2 ≤ k := by
    have h1 : Nat.card N ∣ 2 ^ k := hcardK ▸ Subgroup.card_dvd_of_le hNK
    rw [hN4, show (4 : ℕ) = 2 ^ 2 by norm_num] at h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  have h4k : (4 : ℤ) ∣ 2 ^ k := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hk2
  have hy2 : orderOf (y ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd two_ne_zero (by rw [hy4]; norm_num), hy4]
  have hx2 : orderOf (x ^ (2 ^ (k - 1))) = 2 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk, Nat.pow_div (by omega) two_pos,
      show k - (k - 1) = 1 by omega, pow_one]
  have hyx : y ^ 2 = x ^ (2 ^ (k - 1)) :=
    cyclic_abelian_involution_unique hP hnab hcyc hy2 hx2
  have hKn : (zpowers x).Normal := Subgroup.normal_of_index_eq_two hK2
  obtain ⟨u, hu⟩ := hKn.conj_mem x (mem_zpowers x) y
  replace hu : x ^ u = y * x * y⁻¹ := hu
  have hconjpow : ∀ n : ℤ, y * x ^ n * y⁻¹ = x ^ (u * n) := by
    intro n
    rw [zpow_mul, hu, conj_zpow]
  have hy2x : y ^ 2 * x = x * y ^ 2 := by
    rw [hyx]
    exact (Commute.self_pow x _).symm.eq
  have huu : x ^ (u * u) = x := by
    have h1 : y ^ 2 * x * (y ^ 2)⁻¹ = x := by rw [hy2x, mul_inv_cancel_right]
    have h2 : y ^ 2 * x * (y ^ 2)⁻¹ = y * (y * x * y⁻¹) * y⁻¹ := by rw [sq]; group
    rw [h2, ← hu, hconjpow] at h1
    exact h1
  have hmod : u ^ 2 ≡ 1 [ZMOD 2 ^ k] := by
    have h := (zpow_eq_zpow_iff_modEq (x := x) (m := u * u) (n := 1)).1 (by rw [huu, zpow_one])
    rw [hk] at h
    push_cast at h
    rwa [sq]
  have hNgen : N = zpowers (x ^ (2 ^ (k - 2))) := by
    refine eq_of_le_cyclic_of_card_eq (zpowers x) hNK
      ((zpowers_le).2 (pow_mem (mem_zpowers x) _)) ?_
    rw [hN4, Nat.card_zpowers, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk, Nat.pow_div (by omega) two_pos,
      show k - (k - 2) = 2 by omega]
    norm_num
  have hu4 : u ≡ -1 [ZMOD 4] := by
    rcases CFSG.RankTwoShapes.sq_eq_one_mod_four (hmod.of_dvd h4k) with h | h
    · exfalso
      apply hy
      rw [← hK, hNgen, mem_centralizer_iff]
      intro w hw
      obtain ⟨i, rfl⟩ := hw
      have hw1 : y * x ^ ((2 ^ (k - 2) : ℕ) : ℤ) * y⁻¹ = x ^ ((2 ^ (k - 2) : ℕ) : ℤ) := by
        rw [hconjpow, zpow_eq_zpow_iff_modEq, hk]
        have h' := h.mul_right' (c := ((2 ^ (k - 2) : ℕ) : ℤ))
        rw [one_mul] at h'
        have e : (4 : ℤ) * ((2 ^ (k - 2) : ℕ) : ℤ) = ((2 ^ k : ℕ) : ℤ) := by
          push_cast
          rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add, show 2 + (k - 2) = k by omega]
        rwa [e] at h'
      have hwi : y * (x ^ (2 ^ (k - 2))) ^ i * y⁻¹ = (x ^ (2 ^ (k - 2))) ^ i := by
        rw [← conj_zpow, ← zpow_natCast, hw1]
      show (x ^ (2 ^ (k - 2))) ^ i * y = y * (x ^ (2 ^ (k - 2))) ^ i
      rw [mul_inv_eq_iff_eq_mul] at hwi
      exact hwi.symm
    · exact h
  have hnotinv : ¬ (x * y⁻¹) ^ 2 = 1 := by
    intro hsq
    have hne : x * y⁻¹ ≠ 1 := fun h => hy ((mul_inv_eq_one.1 h) ▸ mem_zpowers x)
    have hord : orderOf (x * y⁻¹) = 2 := orderOf_eq_prime hsq hne
    have heq := cyclic_abelian_involution_unique hP hnab hcyc hord hy2
    apply hy
    have hyinv : y⁻¹ ∈ zpowers x := by
      have h1 : y⁻¹ = x⁻¹ * y ^ 2 := by rw [← heq]; group
      rw [h1, hyx]
      exact mul_mem (inv_mem (mem_zpowers x)) (pow_mem (mem_zpowers x) _)
    simpa using inv_mem hyinv
  have hmain : y * x * y⁻¹ = x⁻¹ := by
    rw [← hu, ← zpow_neg_one, zpow_eq_zpow_iff_modEq, hk]
    push_cast
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · obtain rfl : k = 2 := by omega
      simpa using hu4
    · have h4k1 : (4 : ℤ) ∣ 2 ^ (k - 1) := by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
        exact pow_dvd_pow 2 (by omega)
      have hbad : ¬ (1 : ℤ) ≡ -1 [ZMOD 4] := by decide
      rcases CFSG.RankTwoShapes.sq_eq_one_mod_two_pow hk3 hmod with h | h | h | h
      · exact absurd ((h.of_dvd h4k).symm.trans hu4) hbad
      · exact h
      · have h1 : u ≡ 1 [ZMOD 4] := by
          have := (h.of_dvd h4k).trans
            (Int.ModEq.add_left 1 ((Int.modEq_zero_iff_dvd).2 h4k1))
          simpa using this
        exact absurd (h1.symm.trans hu4) hbad
      ·
        exfalso
        apply hnotinv
        have hxu : x ^ u = x⁻¹ * y ^ 2 := by
          rw [hyx, ← zpow_natCast, ← zpow_neg_one, ← zpow_add, zpow_eq_zpow_iff_modEq, hk]
          push_cast
          exact h
        have hcomm2 : x⁻¹ * y ^ 2 = y ^ 2 * x⁻¹ := by
          rw [hyx]
          exact ((Commute.self_pow x _).inv_left).eq
        have h3 : x * y⁻¹ = y * x⁻¹ := by
          calc x * y⁻¹ = y⁻¹ * (y * x * y⁻¹) := by group
            _ = y⁻¹ * (x⁻¹ * y ^ 2) := by rw [← hu, hxu]
            _ = y⁻¹ * (y ^ 2 * x⁻¹) := by rw [hcomm2]
            _ = y * x⁻¹ := by group
        calc (x * y⁻¹) ^ 2 = (x * y⁻¹) * (y * x⁻¹) := by rw [sq, ← h3]
          _ = 1 := by group
  refine ⟨hmain, fun k' hk' => ?_⟩
  obtain rfl : k' = k := Nat.pow_right_injective le_rfl (hk'.symm.trans hcardK)
  exact ⟨hk2, hyx⟩

end CFSG.LocalAnalysis.ComponentInitial
