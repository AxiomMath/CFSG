module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassical

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin

section Arith

theorem fermat_mersenne_shape {p : ℕ} (hp : Ch1.IsFermatOrMersennePrime p) (hp7 : 7 < p) :
    ∃ b o : ℕ, 3 ≤ b ∧ Odd o ∧ Odd p ∧
      ((p = 2 * 2 ^ b + 1 ∧ o = 2 ^ b + 1) ∨ (p + 1 = 2 * 2 ^ b ∧ o = 2 ^ b - 1)) := by
  obtain ⟨-, hF | ⟨k, -, hk⟩⟩ := hp
  · obtain ⟨k, hk⟩ := hF
    have hk2' : 2 ≤ k := by
      by_contra hlt
      have hk1 : k ≤ 1 := by omega
      have h1 : 2 ^ k ≤ 2 := by
        calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
          _ = 2 := by norm_num
      have h2 : 2 ^ 2 ^ k ≤ 4 := by
        calc 2 ^ 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h1
          _ = 4 := by norm_num
      omega
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2'
    have hb : 2 ^ 2 ^ k = 2 * 2 ^ (2 ^ k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hev : Even (2 ^ (2 ^ k - 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hpodd : Odd p := by
      rw [hk, hb]
      exact (even_two_mul _).add_one
    exact ⟨2 ^ k - 1, 2 ^ (2 ^ k - 1) + 1, by omega, hev.add_one, hpodd,
      Or.inl ⟨by rw [hk, hb], rfl⟩⟩
  · have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hk' : p + 1 = 2 ^ k := by omega
    have h4 : 4 ≤ k := by
      by_contra hlt
      have h1 : 2 ^ k ≤ 8 := by
        calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 8 := by norm_num
      omega
    have hb : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hev : Even (2 ^ (k - 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hpos' : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
    obtain ⟨j, hj⟩ := hev
    exact ⟨k - 1, 2 ^ (k - 1) - 1, by omega, ⟨j - 1, by omega⟩, ⟨2 * j - 1, by omega⟩,
      Or.inr ⟨by omega, rfl⟩⟩

theorem eq_of_two_pow_mul_odd {s a u v : ℕ} (hu : Odd u) (hv : Odd v) (h : 2 ^ s * u = 2 ^ a * v) :
    s = a := by
  have key : ∀ {s a u v : ℕ}, Odd v → 2 ^ s * u = 2 ^ a * v → ¬ a < s := by
    intro s a u v hv h hlt
    obtain ⟨d, rfl⟩ : ∃ d, s = a + d + 1 := ⟨s - a - 1, by omega⟩
    have h2 : v = 2 ^ (d + 1) * u := by
      have : 2 ^ a * v = 2 ^ a * (2 ^ (d + 1) * u) := by
        rw [← h]
        ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    have hev : Even (2 ^ (d + 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have : Even v := by
      rw [h2]
      exact hev.mul_right u
    exact (Nat.not_even_iff_odd.mpr hv) this
  exact le_antisymm (not_lt.mp (key hv h)) (not_lt.mp (key hu h.symm))

theorem not_dvd_of_dvd_or_dvd_odd {t o x : ℕ} (ht : 0 < t) (ho : Odd o)
    (hx : x ∣ t ∨ x ∣ o) (h : 2 * t ∣ x) : False := by
  rcases hx with hx | hx
  · have h1 := Nat.le_of_dvd ht (h.trans hx)
    omega
  · have h2 : 2 ∣ o := (dvd_mul_right 2 t).trans (h.trans hx)
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h2)

end Arith

section Main

open CFSG.Glauberman.Dickson CFSG.BenderSuzuki.MatrixGroups in
theorem l239Sylow2PSL2 : L239Sylow2PSL2 := by
  intro G _ _ L P p hp hp7 hmodel hP Y hPY hYL
  have hpp : Fact p.Prime := ⟨hp.1⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨b, o, hb3, ho, hpodd, hshape⟩ := fermat_mersenne_shape hp hp7
  obtain ⟨K, _, _, _, e, hcard, -, -⟩ := K1.psl2_model_data (X := ↥L) hp2 hmodel
  have hF : Nat.card K = p ^ 1 := by rw [Nat.card_eq_fintype_card, hcard]
  have ht8 : 8 ≤ 2 ^ b := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb3
  have h16 : 16 ∣ 2 * 2 ^ b := by
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 3 := ⟨b - 3, by omega⟩
    exact ⟨2 ^ c, by ring⟩
  have hN : Nat.card ↥L = p * (2 * 2 ^ b) * o := by
    have h1 : Nat.card ↥L = Nat.card (PSL2MatrixGroup K) := Nat.card_congr e.toEquiv
    rw [h1, MaxUp.card_psl2_odd hF hp2, pow_one]
    apply Nat.div_eq_of_eq_mul_left (by norm_num)
    rcases hshape with ⟨hpF, hoF⟩ | ⟨hpM, hoM⟩
    · have hsq : p ^ 2 - 1 = 4 * 2 ^ b * (2 ^ b + 1) := by
        have : p ^ 2 = 4 * 2 ^ b * (2 ^ b + 1) + 1 := by rw [hpF]; ring
        exact Nat.sub_eq_of_eq_add this
      rw [hsq, hoF]
      ring
    · obtain ⟨s, hs⟩ : ∃ s, 2 ^ b = s + 1 := ⟨2 ^ b - 1, by omega⟩
      have hps : p = 2 * s + 1 := by omega
      have hos : o = s := by omega
      have hsq : p ^ 2 - 1 = 4 * (s + 1) * s := by
        have : p ^ 2 = 4 * (s + 1) * s + 1 := by rw [hps]; ring
        exact Nat.sub_eq_of_eq_add this
      rw [hsq, hos, hs]
      ring
  have hPcard : Nat.card P = 2 * 2 ^ b := by
    obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp hP.isPGroup
    have hidx : Odd (P.subgroupOf L).index := by
      have := hP.2.2
      exact Nat.odd_iff.mpr (by omega)
    have h1 : Nat.card P * (P.subgroupOf L).index = Nat.card ↥L := by
      rw [← Subgroup.card_mul_index (P.subgroupOf L)]
      congr 1
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv.symm
    have h2 : 2 ^ s * (P.subgroupOf L).index = 2 ^ (b + 1) * (p * o) := by
      rw [← hs, h1, hN, pow_succ]
      ring
    have hs' : s = b + 1 := eq_of_two_pow_mul_odd hidx (hpodd.mul ho) h2
    rw [hs, hs', pow_succ]
    ring
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup (PSL2MatrixGroup K),
      H = (Y.subgroupOf L).map e.toMonoidHom := ⟨_, rfl⟩
  have hHcard : Nat.card H = Nat.card Y := by
    rw [hHdef, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv
  have hdvd : 2 * 2 ^ b ∣ Nat.card H := by
    rw [hHcard, ← hPcard]
    exact Subgroup.card_dvd_of_le hPY
  have hYP : Nat.card H = 2 * 2 ^ b → Y = P := fun h =>
    (Subgroup.eq_of_le_of_card_ge hPY (by rw [hPcard, ← hHcard, h])).symm
  have hgcd : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
    rw [pow_one]
    apply Nat.gcd_eq_left
    obtain ⟨j, hj⟩ := hpodd
    exact ⟨j, by omega⟩
  have hplus : ∀ z, z ∣ (p ^ 1 + 1) / Nat.gcd 2 (p ^ 1 - 1) → z ∣ 2 ^ b ∨ z ∣ o := by
    intro z hz
    rw [hgcd, pow_one] at hz
    rcases hshape with ⟨hpF, hoF⟩ | ⟨hpM, hoM⟩
    · right
      have : (p + 1) / 2 = o := by omega
      rwa [this] at hz
    · left
      have : (p + 1) / 2 = 2 ^ b := by omega
      rwa [this] at hz
  have hminus : ∀ z, z ∣ (p ^ 1 - 1) / Nat.gcd 2 (p ^ 1 - 1) → z ∣ 2 ^ b ∨ z ∣ o := by
    intro z hz
    rw [hgcd, pow_one] at hz
    rcases hshape with ⟨hpF, hoF⟩ | ⟨hpM, hoM⟩
    · left
      have : (p - 1) / 2 = 2 ^ b := by omega
      rwa [this] at hz
    · right
      have : (p - 1) / 2 = o := by omega
      rwa [this] at hz
  have hdiv : ∀ z, (z ∣ (p ^ 1 + 1) / Nat.gcd 2 (p ^ 1 - 1) ∨
      z ∣ (p ^ 1 - 1) / Nat.gcd 2 (p ^ 1 - 1)) → z ∣ 2 ^ b ∨ z ∣ o := fun z hz =>
    hz.elim (hplus z) (hminus z)
  rcases dickson_psl2_subgroup_list (F := K) (p := p) (f := 1) hF H with
    ⟨m, -, hcardH, -⟩ | ⟨z, hz, hcardH, -⟩ | ⟨z, hz2', hz, ⟨ed⟩⟩ | ⟨-, ⟨e4⟩⟩ | ⟨-, ⟨eS⟩⟩ |
      ⟨-, ⟨eA⟩⟩ | ⟨m, t', hm1, hmf, -, ht'2, E, C, -, -, hEcard, -, hCcard, -, -, -, φ, -, ⟨esd⟩⟩ |
      ⟨m, hmf, ⟨eL⟩⟩ | ⟨m, hmf, -⟩
  · exfalso
    rw [hcardH] at hdvd
    exact (Nat.not_even_iff_odd.mpr hpodd.pow) (even_iff_two_dvd.mpr
      ((dvd_mul_right 2 _).trans hdvd))
  · exfalso
    rw [hcardH] at hdvd
    exact not_dvd_of_dvd_or_dvd_odd (by positivity) ho (hdiv z hz) hdvd
  · have : NeZero z := ⟨by omega⟩
    have hcz : Nat.card H = 2 * z := by
      rw [Nat.card_congr ed.toEquiv, DihedralGroup.nat_card]
    rw [hcz] at hdvd
    rcases hdiv z hz with hzt | hzo
    · left
      apply hYP
      rw [hcz]
      exact Nat.dvd_antisymm (mul_dvd_mul_left 2 hzt) hdvd
    · exfalso
      have h2 : 2 ^ b ∣ z := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
      have h3 : 2 ∣ o := (dvd_pow_self 2 (by omega : b ≠ 0)).trans (h2.trans hzo)
      exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h3)
  · exfalso
    have : Nat.card H = 12 := by rw [Nat.card_congr e4.toEquiv]; exact MaxUp.card_alternatingFour'
    rw [this] at hdvd
    have := h16.trans hdvd
    omega
  · exfalso
    have : Nat.card H = 24 := by rw [Nat.card_congr eS.toEquiv]; exact MaxUp.card_permFour
    rw [this] at hdvd
    have := h16.trans hdvd
    omega
  · exfalso
    have : Nat.card H = 60 := by rw [Nat.card_congr eA.toEquiv]; exact MaxUp.card_alternatingFive'
    rw [this] at hdvd
    have := h16.trans hdvd
    omega
  · exfalso
    have hm : m = 1 := by omega
    subst hm
    have hcs : Nat.card H = p ^ 1 * Nat.card C := by
      rw [Nat.card_congr esd.toEquiv, SemidirectProduct.card, hEcard]
    rw [hcs, hCcard] at hdvd
    have hcop : Nat.Coprime (2 * 2 ^ b) (p ^ 1) := by
      refine Nat.Coprime.pow_right 1 ?_
      refine Nat.Coprime.mul_left (Nat.coprime_two_left.mpr hpodd) ?_
      exact Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hpodd)
    exact not_dvd_of_dvd_or_dvd_odd (by positivity) ho (hminus t' ht'2)
      (hcop.dvd_of_dvd_mul_left hdvd)
  · right
    have hm : m = 1 := Nat.dvd_one.mp hmf
    subst hm
    have hF' : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 (by norm_num)
    have hcL : Nat.card ↥L = Nat.card H := by
      rw [Nat.card_congr eL.toEquiv, MaxUp.card_psl2_odd hF' hp2, Nat.card_congr e.toEquiv,
        MaxUp.card_psl2_odd hF hp2]
    exact Subgroup.eq_of_le_of_card_ge hYL (by rw [← hHcard, ← hcL])
  · exfalso
    have : 2 * m = 1 := Nat.dvd_one.mp hmf
    omega

end Main

end CFSG.QuasithinUnique.Vol2Native.L239
