module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Sl2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx63

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups

theorem exists_prime_five_le_dvd_card_sl2 {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ Nat.card SL(2, F) := by
  classical
  have hfin : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hq : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  rw [CFSG.RankThree.SubgroupLists.card_sl2_field, hq]
  rw [hq] at hodd h5
  have hn0 : (n : ℕ) ≠ 0 := by
    rintro h0
    rw [h0, pow_zero] at h5
    omega
  have hp2 : ringChar F ≠ 2 := by
    intro h2
    rw [h2] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' hn0).2 even_two)
  have hp3 : 3 ≤ ringChar F := by
    have := hp.two_le
    omega
  by_cases hp5 : 5 ≤ ringChar F
  · refine ⟨ringChar F, hp, hp5, ?_⟩
    exact (dvd_pow_self _ hn0).mul_right _
  · have hp4 : ringChar F ≠ 4 := by
      intro h4
      rw [h4] at hp
      norm_num at hp
    have hp33 : ringChar F = 3 := by omega
    set q : ℕ := ringChar F ^ (n : ℕ) with hqdef
    have hq3 : 3 ∣ q := by
      rw [hqdef, hp33]
      exact dvd_pow_self 3 hn0
    by_contra hno
    have hno' : ∀ r : ℕ, r.Prime → r ∣ q * (q ^ 2 - 1) → r < 5 := by
      intro r hr hdvd
      by_contra hr5
      exact hno ⟨r, hr, not_lt.1 hr5, hdvd⟩
    have hq1 : q ≥ 1 := by omega
    have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have : q ^ 2 = (q - 1) * (q + 1) + 1 := by
        obtain ⟨u, hu⟩ : ∃ u, q = u + 1 := ⟨q - 1, by omega⟩
        rw [hu]
        simp only [Nat.add_sub_cancel]
        ring
      omega
    have hpow2 : ∀ m : ℕ, m ∣ q ^ 2 - 1 → ¬ 3 ∣ m → m ≠ 0 → ∃ a, m = 2 ^ a := by
      intro m hm h3m hm0
      refine ⟨m.primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hm0 ?_⟩
      intro d hd hdm
      have hdq : d ∣ q * (q ^ 2 - 1) := (hdm.trans hm).mul_left _
      have hlt := hno' d hd hdq
      have hd4 : d ≠ 4 := by
        rintro rfl
        norm_num at hd
      have hd2 : d = 2 ∨ d = 3 := by
        have := hd.two_le
        omega
      rcases hd2 with h | h
      · exact h
      · exact absurd (h ▸ hdm) h3m
    have hd3 : ¬ 3 ∣ q - 1 := by omega
    have hd3' : ¬ 3 ∣ q + 1 := by omega
    obtain ⟨a, ha⟩ := hpow2 (q - 1) (hfac ▸ dvd_mul_right _ _) hd3 (by omega)
    obtain ⟨b, hb⟩ := hpow2 (q + 1) (hfac ▸ dvd_mul_left _ _) hd3' (by omega)
    have hab : 2 ^ b = 2 ^ a + 2 := by omega
    have ha1 : a = 1 := by
      rcases Nat.lt_or_ge a 2 with h | h
      · interval_cases a
        · omega
        · rfl
      · exfalso
        have h4 : 4 ∣ 2 ^ a := by
          have : 2 ^ 2 ∣ 2 ^ a := pow_dvd_pow 2 h
          simpa using this
        have hb2 : 2 ≤ b := by
          by_contra hb2
          have : b ≤ 1 := by omega
          interval_cases b <;> omega
        have h4b : 4 ∣ 2 ^ b := by
          have : 2 ^ 2 ∣ 2 ^ b := pow_dvd_pow 2 hb2
          simpa using this
        omega
    subst ha1
    omega

theorem false_of_four {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}
    (hfr : AFrame A zb Sb Vb) {P : Type} [Group P] (ι : P →* A) (hι : Function.Injective ι)
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    {x y : P} (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x)
    (hxy : x * y = y * x) (c : SL(2, F) →* P)
    (hc : ∀ g, c g = 1 → g ∈ Subgroup.center SL(2, F))
    (hcx : ∀ g, c g * x = x * c g) (hcy : ∀ g, c g * y = y * c g) : False := by
  classical
  have hx2' : ι x * ι x = 1 := by rw [← map_mul, hx2, map_one]
  have hy2' : ι y * ι y = 1 := by rw [← map_mul, hy2, map_one]
  have hx1' : ι x ≠ 1 := fun h => hx1 (hι (by rw [h, map_one]))
  have hy1' : ι y ≠ 1 := fun h => hy1 (hι (by rw [h, map_one]))
  have hyx' : ι y ≠ ι x := fun h => hyx (hι h)
  have hxy' : ι x * ι y = ι y * ι x := by rw [← map_mul, ← map_mul, hxy]
  obtain ⟨hUcard, hUelems⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.four_of_comm_invol hx2' hy2' hx1' hy1' hyx' hxy'
  set U : Subgroup A := zpowers (ι x) ⊔ zpowers (ι y) with hU
  have hUsq : ∀ w ∈ U, w * w = 1 := by
    intro w hw
    rcases hUelems w hw with h | h | h | h
    · rw [h, one_mul]
    · rw [h]; exact hx2'
    · rw [h]; exact hy2'
    · rw [h]
      calc ι y * ι x * (ι y * ι x) = ι y * (ι x * ι y) * ι x := by group
        _ = ι y * (ι y * ι x) * ι x := by rw [hxy']
        _ = (ι y * ι y) * (ι x * ι x) := by group
        _ = 1 := by rw [hy2', hx2', one_mul]
  have hU4 : IVK.IsFourSubgroup U :=
    ⟨CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.isElemAbelian2_of_sq_one hUsq, hUcard⟩
  have hcent : ∀ g : SL(2, F), ι (c g) ∈ centralizer (U : Set A) := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hU' : U ≤ centralizer ({ι (c g)} : Set A) := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcx]
      · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcy]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hU' hw)
  obtain ⟨r, hr, hr5, hrdvd⟩ := exists_prime_five_le_dvd_card_sl2 hodd h5
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hrdvd
  have hcen2 : ∀ z ∈ Subgroup.center SL(2, F), z * z = 1 := by
    intro z hz
    rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff z).1 hz with rfl | rfl
    · simp
    · simp
  have hcg : ι (c g) ^ r = 1 := by rw [← map_pow, ← map_pow, ← hg, pow_orderOf_eq_one, map_one,
    map_one]
  have hcg1 : ι (c g) ≠ 1 := by
    intro h1
    have : c g = 1 := hι (by rw [h1, map_one])
    have hz := hc g this
    have hz2 := hcen2 g hz
    have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
    rw [hg] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hord : orderOf (ι (c g)) = r := orderOf_eq_prime hcg hcg1
  have hmem := hfr.four U hU4 r hr hr5 (ι (c g)) (hcent g) hord
  set C : Subgroup A := centralizer (U : Set A) with hC
  set N : Subgroup A := pPrimeCoreOf 2 C with hN
  have hNnorm : ∀ z ∈ C, ∀ n ∈ N, z * n * z⁻¹ ∈ N := by
    intro z hz n hn
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hn
    exact Subgroup.mem_map.2 ⟨⟨z, hz⟩ * m * ⟨z, hz⟩⁻¹,
      (pPrimeCore_normal (p := 2) (G := ↥C)).conj_mem m hm _, by simp⟩
  have hNodd : Odd (Nat.card N) := by
    have h1 : Nat.card N = Nat.card (pPrimeCore 2 ↥C) :=
      Nat.card_congr ((pPrimeCore 2 ↥C).equivMapOfInjective C.subtype
        (Subgroup.subtype_injective _)).toEquiv.symm
    rw [h1]
    exact Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥C))
  let M : Subgroup SL(2, F) := N.comap (ι.comp c)
  have hMnorm : M.Normal := by
    refine ⟨fun m hm z => ?_⟩
    show (ι.comp c) (z * m * z⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNnorm _ (hcent z) _ hm
  have hq4 : 4 ≤ Nat.card F := by omega
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_sl2 hq4) hMnorm with
    htop | hle
  ·
    have hrange : (ι.comp c).range ≤ N := by
      rintro _ ⟨z, rfl⟩
      have : z ∈ M := htop ▸ Subgroup.mem_top z
      exact this
    have hdvd1 : Nat.card (ι.comp c).range ∣ Nat.card N := Subgroup.card_dvd_of_le hrange
    have hodd1 : Odd (Nat.card (ι.comp c).range) := Odd.of_dvd_nat hNodd hdvd1
    have hker : (ι.comp c).ker ≤ Subgroup.center SL(2, F) := by
      intro z hz
      have h1 : ι (c z) = 1 := hz
      exact hc z (hι (by rw [h1, map_one]))
    have hkercard : Nat.card (ι.comp c).ker ∣ 2 := by
      have h2c : Nat.card (center SL(2, F)) = 2 := CFSG.ClassicalInvolution.sl2_natCard_center hodd
      have h1 := Subgroup.card_dvd_of_le hker
      rwa [h2c] at h1
    have hmul := Subgroup.card_ker_mul_card_range (ι.comp c)
    have h8 : 8 ∣ Nat.card SL(2, F) := by
      rw [CFSG.RankThree.SubgroupLists.card_sl2_field]
      obtain ⟨k, hk⟩ := hodd
      refine Dvd.dvd.mul_left ?_ _
      rw [hk]
      have : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
        have h1 : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
        omega
      rw [this]
      have h2 : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
      obtain ⟨m, hm⟩ := h2
      exact ⟨m, by rw [hm]; ring⟩
    rw [← hmul] at h8
    rcases (Nat.dvd_prime Nat.prime_two).1 hkercard with hk1 | hk2
    · rw [hk1, one_mul] at h8
      exact (Nat.not_even_iff_odd.2 hodd1) (even_iff_two_dvd.2 ((by norm_num : 2 ∣ 8).trans h8))
    · rw [hk2] at h8
      have h4 : 4 ∣ Nat.card (ι.comp c).range := by
        have : 2 * 4 ∣ 2 * Nat.card (ι.comp c).range := by simpa using h8
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
      exact (Nat.not_even_iff_odd.2 hodd1) (even_iff_two_dvd.2 ((by norm_num : 2 ∣ 4).trans h4))
  ·
    have hgM : g ∈ M := hmem
    have hz := hcen2 g (hle hgM)
    have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz)
    rw [hg] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
