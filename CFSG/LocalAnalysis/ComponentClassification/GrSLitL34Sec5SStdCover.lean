module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanConfig
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.ONAut
public import CFSG.LocalAnalysis.OddStandard.ONanSylowFacts
public import CFSG.LocalAnalysis.OddStandard.ONanSylowCert

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.Blueprint.NativeSporadic (IsSporadic)

private theorem eq_of_quotient_center_eq {J : Type} [Group J] [Finite J]
    (hZ : Odd (Nat.card (center J))) {x y : J} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (h : QuotientGroup.mk' (center J) x = QuotientGroup.mk' (center J) y) : x = y := by
  let π : J →* J ⧸ center J := QuotientGroup.mk' (center J)
  have hxy : y⁻¹ * x ∈ π.ker := (MonoidHom.eq_iff π).mp h
  have hc : y * x ∈ center J := by
    have hyinv : y⁻¹ = y := inv_eq_self_of_orderOf_eq_two hy
    simpa [π, QuotientGroup.ker_mk', hyinv] using hxy
  have hx2 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa [pow_two] using h
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    simpa [pow_two] using h
  have hcomm : x * (y * x) = (y * x) * x := Subgroup.mem_center_iff.mp hc x
  have hc2 : (y * x) ^ 2 = 1 := by
    rw [pow_two]
    calc (y * x) * (y * x) = y * (x * (y * x)) := by rw [mul_assoc]
      _ = y * ((y * x) * x) := by rw [hcomm]
      _ = y * y := by rw [mul_assoc, hx2, mul_one]
      _ = 1 := hy2
  have hc_order : orderOf (y * x) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hc2) with h1 | h2
    · exact h1
    · exact absurd h2 ((Odd.ne_two_of_dvd_nat hZ (Subgroup.orderOf_dvd_natCard (center J) hc)))
  have hyx : y * x = 1 := orderOf_eq_one_iff.mp hc_order
  calc x = (y * x) * x := by rw [hyx, one_mul]
    _ = y * (x * x) := by rw [mul_assoc]
    _ = y * 1 := by rw [hx2]
    _ = y := by rw [mul_one]

private theorem orderOf_mk_center_eq_two {J : Type} [Group J] [Finite J]
    (hZ : Odd (Nat.card (center J))) {a : J} (ha : orderOf a = 2) :
    orderOf (QuotientGroup.mk' (center J) a) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · have ha2 : a ^ 2 = 1 := by
      have h := pow_orderOf_eq_one a
      rwa [ha] at h
    rw [← map_pow, ha2, map_one]
  · intro h
    have hmem : a ∈ center J := by
      have h := MonoidHom.mem_ker.mpr h
      simpa [QuotientGroup.ker_mk'] using h
    exact (Odd.ne_two_of_dvd_nat hZ (Subgroup.orderOf_dvd_natCard (center J) hmem)) ha

private theorem exists_odd_pow_orderOf_eq_sixteen {J : Type} [Group J] [Finite J]
    (hZ : Odd (Nat.card (center J))) {x : J}
    (hx : orderOf (QuotientGroup.mk' (center J) x) = 16) :
    ∃ m : ℕ, Odd m ∧ orderOf (x ^ m) = 16 := by
  let π : J →* J ⧸ center J := QuotientGroup.mk' (center J)
  have h16dvd : 16 ∣ orderOf x := by
    have h := orderOf_map_dvd π x
    rwa [hx] at h
  have hx16 : x ^ 16 ∈ center J := by
    have h1 : π (x ^ 16) = 1 := by
      rw [map_pow, ← hx, pow_orderOf_eq_one]
    have h2 : x ^ 16 ∈ π.ker := MonoidHom.mem_ker.mpr h1
    simpa [π, QuotientGroup.ker_mk'] using h2
  set c := orderOf (x ^ 16) with hc
  have hc_dvd : c ∣ Nat.card (center J) := Subgroup.orderOf_dvd_natCard (center J) hx16
  have hc_odd : Odd c := Odd.of_dvd_nat hZ hc_dvd
  have hn_dvd : orderOf x ∣ 16 * c := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, hc, pow_orderOf_eq_one]
  set m := orderOf x / 16 with hm
  have hn_eq : orderOf x = 16 * m := by
    rw [hm]
    exact (Nat.mul_div_cancel' h16dvd).symm
  have hm_dvd_c : m ∣ c := by
    refine Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 16) ?_
    rw [← hn_eq]
    exact hn_dvd
  have hm_odd : Odd m := Odd.of_dvd_nat hc_odd hm_dvd_c
  have hm_ne : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hn_eq
    exact (orderOf_pos x).ne' hn_eq
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne
  have hm_dvd_n : m ∣ orderOf x := by
    rw [hn_eq]
    exact dvd_mul_left m 16
  refine ⟨m, hm_odd, ?_⟩
  rw [orderOf_pow_of_dvd hm_ne hm_dvd_n]
  exact Nat.div_eq_of_eq_mul_left hm_pos hn_eq

private theorem exists_orderOf_eq_sixteen_of_isSporadic_on
    {Y : Type} [Group Y] (h : IsSporadic Y .ONan) : ∃ y : Y, orderOf y = 16 := by
  classical
  obtain ⟨e⟩ := h
  let T : Sylow 2 CFSG.Blueprint.NativeSporadic.ON := default
  obtain ⟨θ⟩ := CFSG.OddStandard.ONanRec.exists_mulEquiv_alpE
    (CFSG.OddStandard.ONanRec.alpBound_cert) T T (MulEquiv.refl _)
  have hgen : orderOf (CFSG.OddStandard.ONanRec.F2.AlpE.gen 3) = 16 :=
    CFSG.OddStandard.ONanRec.Model.orderOf_of_d_odd
      CFSG.OddStandard.ONanRec.f2Check_cert (Or.inl rfl)
  have hθ : orderOf (θ (CFSG.OddStandard.ONanRec.F2.AlpE.gen 3)) = 16 := by
    rw [MulEquiv.orderOf_eq]
    exact hgen
  have hx0 : orderOf ((θ (CFSG.OddStandard.ONanRec.F2.AlpE.gen 3) :
      (T : Subgroup CFSG.Blueprint.NativeSporadic.ON)) :
      CFSG.Blueprint.NativeSporadic.ON) = 16 := by
    rw [Subgroup.orderOf_coe]
    exact hθ
  exact ⟨e.symm _, by rw [MulEquiv.orderOf_eq]; exact hx0⟩

theorem isSporadic_center_onan_of_isStandardSubgroup
    {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hst : IsStandardSubgroup J) (hτ : IsSporadic (↥J ⧸ Open.fusionZStar ↥J) .ONan)
    (hO : oddIn J ≤ (center ↥J).map J.subtype) :
    IsSporadic (↥J ⧸ center ↥J) .ONan ∧ Odd (Nat.card (center ↥J)) ∧
      pPrimeCore 2 ↥J = center ↥J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥J := hst.1.1
  have hON : IsSporadic (↥J ⧸ pPrimeCore 2 ↥J) .ONan :=
    isSporadic_pPrimeCore_of_fusionZStar_on hperf hτ
  have hO' : pPrimeCore 2 ↥J ≤ center ↥J := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ :=
      Subgroup.mem_map.mp (hO (Subgroup.mem_map_of_mem J.subtype hy))
    have hzy' : z = y := Subtype.ext hzy
    rwa [← hzy']
  have hcenterbot : center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ :=
    CFSG.EvenSporadicStandard.Solomon78.center_eq_bot_of_isSporadic_on hON
  have hZle : center ↥J ≤ pPrimeCore 2 ↥J := by
    intro z hz
    let π : ↥J →* (↥J ⧸ pPrimeCore 2 ↥J) := QuotientGroup.mk' (pPrimeCore 2 ↥J)
    have hzc : π z ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) y
      show π x * π z = π z * π x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    rw [hcenterbot] at hzc
    have hker : z ∈ π.ker := MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hzc)
    have hπker : π.ker = pPrimeCore 2 ↥J := QuotientGroup.ker_mk' _
    rwa [hπker] at hker
  have hEq : pPrimeCore 2 ↥J = center ↥J := le_antisymm hO' hZle
  refine ⟨?_, ?_, hEq⟩
  · obtain ⟨e⟩ := hON
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hEq).symm.trans e⟩
  · rw [← hEq]
    exact Nat.Coprime.odd_of_left (pPrimeCore_coprime_card (p := 2) (G := ↥J))

theorem exists_conj_of_orderOf_eq_two_onan
    {J : Type} [Group J] [Finite J]
    (hJ : IsSporadic (J ⧸ center J) .ONan) (hZ : Odd (Nat.card (center J))) {a b : J}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : ∃ j : J, b = j⁻¹ * a * j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpa : orderOf (QuotientGroup.mk' (center J) a) = 2 :=
    orderOf_mk_center_eq_two hZ ha
  have hpb : orderOf (QuotientGroup.mk' (center J) b) = 2 :=
    orderOf_mk_center_eq_two hZ hb
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (CFSG.EvenSporadicStandard.Solomon78.on_forall_isConj hJ _ _ hpa hpb)
  obtain ⟨j, hj⟩ := QuotientGroup.mk'_surjective (center J) c
  rw [← hj] at hc
  have hc' : QuotientGroup.mk' (center J) (j * a * j⁻¹) =
      QuotientGroup.mk' (center J) b := by
    rw [map_mul, map_mul, map_inv]
    exact hc
  have hconj_ord : orderOf (j * a * j⁻¹) = 2 := by
    have hconj : IsConj a (j * a * j⁻¹) := isConj_iff.mpr ⟨j, rfl⟩
    rw [← IsConj.orderOf_eq hconj, ha]
  have hEq : j * a * j⁻¹ = b := eq_of_quotient_center_eq hZ hconj_ord hb hc'
  exact ⟨j⁻¹, by simpa using hEq.symm⟩

theorem exists_pow_eight_eq_of_orderOf_eq_two_onan
    {J : Type} [Group J] [Finite J]
    (hJ : IsSporadic (J ⧸ center J) .ONan) (hZ : Odd (Nat.card (center J))) {a : J}
    (ha : orderOf a = 2) : ∃ y : J, y ^ 8 = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ybar, hybar⟩ := exists_orderOf_eq_sixteen_of_isSporadic_on hJ
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center J) ybar
  have hx16 : orderOf (QuotientGroup.mk' (center J) x) = 16 := by
    rw [hx]
    exact hybar
  obtain ⟨m, -, hm_ord⟩ := exists_odd_pow_orderOf_eq_sixteen hZ hx16
  let y : J := x ^ m
  have hy16 : orderOf y = 16 := hm_ord
  have hy8 : orderOf (y ^ 8) = 2 := by
    rw [orderOf_pow, hy16]
    norm_num
  obtain ⟨j, hj⟩ := exists_conj_of_orderOf_eq_two_onan hJ hZ (a := y ^ 8) (b := a) hy8 ha
  have hpow : (j⁻¹ * y * j) ^ 8 = j⁻¹ * y ^ 8 * j := by
    simpa using conj_pow (a := j⁻¹) (b := y) (i := 8)
  exact ⟨j⁻¹ * y * j, by rw [hpow, hj]⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
