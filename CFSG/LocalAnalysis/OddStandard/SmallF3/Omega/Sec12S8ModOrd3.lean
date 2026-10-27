module

public import CFSG.RankThree.PartTwo.KFacts.L34Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.RankThree.PartTwo.KFacts.L34 CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem sec12S8Mod_trans {k : Type*} [Field k] (hk : Nat.card k = 4) {a b : projectiveSL 3 k}
    (ha : a ∈ eZero k) (hb : b ∈ eZero k) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (eZero k : Set (projectiveSL 3 k)), n * a * n⁻¹ = b := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have hA3 : aP u ^ 3 = 1 := pow_three_of_mem_eZero hk aP_mem_eZero
  have hB3 : (bP : projectiveSL 3 k) ^ 3 = 1 := pow_three_of_mem_eZero hk bP_mem_eZero
  have hAB : Commute (aP u) bP := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  have hF := fP_mem_normalizer hk hu
  have hJ := jP_mem_normalizer hk hu
  have hFA := fP_conj_aP hk hu
  have hFB := fP_conj_bP hk hu
  have hJA := jP_conj_aP hk hu
  have mul_conj : ∀ n y z : projectiveSL 3 k, n * (y * z) * n⁻¹ = (n * y * n⁻¹) * (n * z * n⁻¹) :=
    fun n y z => by group
  have inv_conj : ∀ n y : projectiveSL 3 k, n * y⁻¹ * n⁻¹ = (n * y * n⁻¹)⁻¹ :=
    fun n y => by group
  have hy2 : fP hk hu * (bP * (aP u)⁻¹) * (fP hk hu)⁻¹ = (aP u)⁻¹ * bP⁻¹ := by
    rw [mul_conj, inv_conj, hFA, hFB]
  have hy3 : fP hk hu * ((aP u)⁻¹ * bP⁻¹) * (fP hk hu)⁻¹ = bP⁻¹ * aP u := by
    rw [mul_conj, inv_conj, inv_conj, hFA, hFB, inv_inv]
  have hy4 : fP hk hu * (bP⁻¹ * aP u) * (fP hk hu)⁻¹ = aP u * bP := by
    rw [mul_conj, inv_conj, hFA, hFB, inv_inv]
  have key : ∀ x ∈ eZero k, x ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (eZero k : Set (projectiveSL 3 k)), n * aP u * n⁻¹ = x := by
    intro x hx hx1
    obtain ⟨i, j, hi, hj, rfl⟩ := exists_eq_aP_pow_mul_bP_pow hk hu hx
    set f := fP hk hu with hf
    set g := jP hk hu with hg
    interval_cases i <;> interval_cases j
    · simp at hx1
    · exact ⟨f, hF, by simpa using hFA⟩
    · refine ⟨f * f * f, mul_mem (mul_mem hF hF) hF, ?_⟩
      have e : f * f * f * aP u * (f * f * f)⁻¹ = f * (f * (f * aP u * f⁻¹) * f⁻¹) * f⁻¹ := by
        group
      rw [e, hFA, hFB, inv_conj, hFA, sq_eq_inv_of_pow_three hB3]
      simp
    · exact ⟨1, one_mem _, by simp⟩
    · refine ⟨f * f * f * g, mul_mem (mul_mem (mul_mem hF hF) hF) hJ, ?_⟩
      have e : f * f * f * g * aP u * (f * f * f * g)⁻¹ =
          f * (f * (f * (g * aP u * g⁻¹) * f⁻¹) * f⁻¹) * f⁻¹ := by group
      rw [e, hJA, hy2, hy3, hy4]
      simp
    · refine ⟨f * f * g, mul_mem (mul_mem hF hF) hJ, ?_⟩
      have e : f * f * g * aP u * (f * f * g)⁻¹ = f * (f * (g * aP u * g⁻¹) * f⁻¹) * f⁻¹ := by
        group
      rw [e, hJA, hy2, hy3, sq_eq_inv_of_pow_three hB3, pow_one, (hAB.inv_right).eq]
    · refine ⟨f * f, mul_mem hF hF, ?_⟩
      have e : f * f * aP u * (f * f)⁻¹ = f * (f * aP u * f⁻¹) * f⁻¹ := by group
      rw [e, hFA, hFB, sq_eq_inv_of_pow_three hA3]
      simp
    · refine ⟨g, hJ, ?_⟩
      rw [hJA, sq_eq_inv_of_pow_three hA3, pow_one, (hAB.inv_left).eq]
    · refine ⟨f * g, mul_mem hF hJ, ?_⟩
      have e : f * g * aP u * (f * g)⁻¹ = f * (g * aP u * g⁻¹) * f⁻¹ := by group
      rw [e, hJA, hy2, sq_eq_inv_of_pow_three hA3, sq_eq_inv_of_pow_three hB3]
  obtain ⟨na, hna, hna'⟩ := key a ha ha1
  obtain ⟨nb, hnb, hnb'⟩ := key b hb hb1
  refine ⟨nb * na⁻¹, mul_mem hnb (inv_mem hna), ?_⟩
  rw [← hna', ← hnb']
  group

theorem sec12S8Mod_conj3 {k : Type*} [Field k] (hk : Nat.card k = 4) {a b : projectiveSL 3 k}
    (ha : orderOf a = 3) (hb : orderOf b = 3) : IsConj a b := by
  haveI := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha1 : a ≠ 1 := by rintro rfl; simp at ha
  have hb1 : b ≠ 1 := by rintro rfl; simp at hb
  have hpa : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha]; rfl)
  have hpb : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb]; rfl)
  obtain ⟨Pa, hPa⟩ := hpa.exists_le_sylow
  obtain ⟨Pb, hPb⟩ := hpb.exists_le_sylow
  have hPa9 : Nat.card (Pa : Subgroup (projectiveSL 3 k)) = 9 := by
    rw [Sylow.card_eq_multiplicity, factorization_card hk]
    norm_num
  have hPb9 : Nat.card (Pb : Subgroup (projectiveSL 3 k)) = 9 := by
    rw [Sylow.card_eq_multiplicity, factorization_card hk]
    norm_num
  obtain ⟨ga, hga⟩ := exists_eq_map_conj_eZero hk hPa9
  obtain ⟨gb, hgb⟩ := exists_eq_map_conj_eZero hk hPb9
  have hya : ga⁻¹ * a * ga ∈ eZero k := by
    have hmem : a ∈ (Pa : Subgroup (projectiveSL 3 k)) := hPa (Subgroup.mem_zpowers a)
    rw [hga] at hmem
    obtain ⟨y, hy, hyeq⟩ := hmem
    have hyeq' : ga * y * ga⁻¹ = a := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hyeq
    have : ga⁻¹ * a * ga = y := by rw [← hyeq']; group
    rw [this]
    exact hy
  have hyb : gb⁻¹ * b * gb ∈ eZero k := by
    have hmem : b ∈ (Pb : Subgroup (projectiveSL 3 k)) := hPb (Subgroup.mem_zpowers b)
    rw [hgb] at hmem
    obtain ⟨y, hy, hyeq⟩ := hmem
    have hyeq' : gb * y * gb⁻¹ = b := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hyeq
    have : gb⁻¹ * b * gb = y := by rw [← hyeq']; group
    rw [this]
    exact hy
  have hya1 : ga⁻¹ * a * ga ≠ 1 := by
    intro h
    apply ha1
    calc a = ga * (ga⁻¹ * a * ga) * ga⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hyb1 : gb⁻¹ * b * gb ≠ 1 := by
    intro h
    apply hb1
    calc b = gb * (gb⁻¹ * b * gb) * gb⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨n, -, hn⟩ := sec12S8Mod_trans hk hya hyb hya1 hyb1
  rw [isConj_iff]
  refine ⟨gb * n * ga⁻¹, ?_⟩
  calc gb * n * ga⁻¹ * a * (gb * n * ga⁻¹)⁻¹
      = gb * (n * (ga⁻¹ * a * ga) * n⁻¹) * gb⁻¹ := by group
    _ = gb * (gb⁻¹ * b * gb) * gb⁻¹ := by rw [hn]
    _ = b := by group

end CFSG.OddStandard.SmallF3.Omega
