module

public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.CGT.Stroth77

namespace Stroth43ZStar

open scoped Pointwise

private theorem image_conj_eq_image_of_commute {X : Type} [Group X] [Finite X]
    {Z : Subgroup X} [Z.Normal] {a : X} (hZ : Z = Subgroup.zpowers (a ^ 2))
    (T : Sylow 2 X) (ha4 : a ^ 4 = 1) (ha2 : a ^ 2 ≠ 1)
    (hz : ∀ x : X, x * a ^ 2 = a ^ 2 * x)
    (hsc : ∀ g : X, g⁻¹ * a * g ∈ (T : Subgroup X) →
      g⁻¹ * a * g ∈ Subgroup.zpowers a)
    {g' : X}
    (hcomm : (QuotientGroup.mk' Z (g' * a * g'⁻¹)) * (QuotientGroup.mk' Z a) =
      (QuotientGroup.mk' Z a) * (QuotientGroup.mk' Z (g' * a * g'⁻¹))) :
    QuotientGroup.mk' Z (g' * a * g'⁻¹) = QuotientGroup.mk' Z a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  let t : X ⧸ Z := π a
  let y : X := g' * a * g'⁻¹
  let u : X ⧸ Z := π y
  have hz2 : (a ^ 2) * (a ^ 2) = 1 := by
    rw [← pow_two, ← pow_mul]
    exact ha4
  have haaZ : a * a ∈ Z := by
    rw [hZ, ← pow_two]
    exact Subgroup.mem_zpowers (a ^ 2)
  have ht2 : t * t = 1 := by
    rw [show t * t = π (a * a) by simp only [t, map_mul]]
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact haaZ
  have hyyZ : y * y ∈ Z := by
    rw [hZ]
    rw [show y * y = a ^ 2 by
      calc
        y * y = g' * (a * a) * g'⁻¹ := by simp only [y]; group
        _ = g' * (a ^ 2) * g'⁻¹ := by rw [pow_two]
        _ = a ^ 2 := by rw [hz g']; group]
    exact Subgroup.mem_zpowers (a ^ 2)
  have hu2 : u * u = 1 := by
    rw [show u * u = π (y * y) by simp only [u, map_mul]]
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hyyZ
  have hcomm' : u * t = t * u := by
    simpa only [u, t, y, π] using hcomm
  have hpt : IsPGroup 2 (Subgroup.zpowers t) :=
    CFSG.ZStar.TransferReduction.isPGroup_zpowers_two_of_sq_eq_one t ht2
  have hpu : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ZStar.TransferReduction.isPGroup_zpowers_two_of_sq_eq_one u hu2
  have hnorm : Subgroup.zpowers t ≤
      Subgroup.normalizer (Subgroup.zpowers u : Set (X ⧸ Z)) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun w hw => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact (Commute.zpow_left hcomm' k).eq)
  have hH : IsPGroup 2 (Subgroup.zpowers t ⊔ Subgroup.zpowers u :
      Subgroup (X ⧸ Z)) :=
    IsPGroup.to_sup_of_normal_right' hpt hpu hnorm
  let Q : Subgroup X := (Subgroup.zpowers t ⊔ Subgroup.zpowers u).comap π
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk', hZ]
    exact CFSG.ZStar.TransferReduction.isPGroup_zpowers_two_of_sq_eq_one (a ^ 2) hz2
  have hQ : IsPGroup 2 Q :=
    IsPGroup.comap_of_ker_isPGroup (H := Subgroup.zpowers t ⊔ Subgroup.zpowers u)
      hH π hker
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  obtain ⟨h, hhP⟩ := MulAction.exists_smul_eq X P T
  let k : X := h⁻¹
  have hkT : ∀ q ∈ Q, k⁻¹ * q * k ∈ (T : Subgroup X) := by
    intro q hq
    have hqP : q ∈ (P : Subgroup X) := hQP hq
    have hmem : (MulAut.conj h) • q ∈ (MulAut.conj h) • (P : Subgroup X) :=
      Subgroup.smul_mem_pointwise_smul q (MulAut.conj h) (P : Subgroup X) hqP
    have hPeq : (MulAut.conj h) • (P : Subgroup X) = (T : Subgroup X) := by
      rw [← Sylow.coe_subgroup_smul, hhP]
    rw [hPeq] at hmem
    simpa [k, MulAut.conj_apply] using hmem
  have haQ : a ∈ Q := by
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hyQ : y ∈ Q := by
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hka : k⁻¹ * a * k ∈ Subgroup.zpowers a := hsc k (hkT a haQ)
  have hky : k⁻¹ * y * k ∈ Subgroup.zpowers a := by
    have hyT : k⁻¹ * y * k ∈ (T : Subgroup X) := hkT y hyQ
    have hyconj : k⁻¹ * y * k = (g'⁻¹ * k)⁻¹ * a * (g'⁻¹ * k) := by
      simp only [y]
      group
    rw [hyconj]
    exact hsc (g'⁻¹ * k) (by rwa [hyconj] at hyT)
  have hka_sq : (k⁻¹ * a * k) * (k⁻¹ * a * k) = a ^ 2 := by
    calc
      (k⁻¹ * a * k) * (k⁻¹ * a * k) = k⁻¹ * (a * a) * k := by group
      _ = k⁻¹ * (a ^ 2) * k := by rw [pow_two]
      _ = a ^ 2 := by rw [hz k⁻¹]; group
  have hyy : y * y = a ^ 2 := by
    calc
      y * y = g' * (a * a) * g'⁻¹ := by simp only [y]; group
      _ = g' * (a ^ 2) * g'⁻¹ := by rw [pow_two]
      _ = a ^ 2 := by rw [hz g']; group
  have hky_sq : (k⁻¹ * y * k) * (k⁻¹ * y * k) = a ^ 2 := by
    calc
      (k⁻¹ * y * k) * (k⁻¹ * y * k) = k⁻¹ * (y * y) * k := by group
      _ = k⁻¹ * (a ^ 2) * k := by rw [hyy]
      _ = a ^ 2 := by rw [hz k⁻¹]; group
  have key : ∀ x : X, x ∈ Subgroup.zpowers a → x * x = a ^ 2 → π x = t := by
    intro x hx hxx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hzpow2 : (a ^ 2) ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
      exact hz2
    rcases Int.emod_two_eq_zero_or_one j with he | ho
    · exfalso
      have hxj : a ^ j = (a ^ 2) ^ (j / 2) := by
        conv_lhs => rw [show j = 2 * (j / 2) by
          have h := Int.emod_add_mul_ediv j 2
          omega]
        rw [zpow_mul]
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
      have hxx1 : (a ^ j) * (a ^ j) = 1 := by
        rw [hxj, ← zpow_add, show j / 2 + j / 2 = 2 * (j / 2) by ring,
          zpow_mul, hzpow2, one_zpow]
      rw [hxx1] at hxx
      exact ha2 hxx.symm
    · have hxj : a ^ j = a * (a ^ 2) ^ (j / 2) := by
        conv_lhs => rw [show j = 1 + 2 * (j / 2) by
          have h := Int.emod_add_mul_ediv j 2
          omega]
        rw [zpow_add, zpow_mul, zpow_one]
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
      have hzi : (a ^ 2) ^ (j / 2) ∈ Z := by
        exact hZ.symm ▸ Subgroup.mem_zpowers_iff.mpr ⟨j / 2, rfl⟩
      have hπzi : π ((a ^ 2) ^ (j / 2)) = 1 := by
        change QuotientGroup.mk' Z ((a ^ 2) ^ (j / 2)) = 1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hzi
      calc
        π (a ^ j) = π (a * (a ^ 2) ^ (j / 2)) := by rw [hxj]
        _ = π a * π ((a ^ 2) ^ (j / 2)) := map_mul ..
        _ = π a * 1 := by rw [hπzi]
        _ = π a := mul_one _
        _ = t := rfl
  have hπa : π (k⁻¹ * a * k) = t := key _ hka hka_sq
  have hπy : π (k⁻¹ * y * k) = t := key _ hky hky_sq
  have hconj_a : (π k)⁻¹ * t * π k = t := by
    simpa only [t, map_mul, map_inv] using hπa
  have hconj_y : (π k)⁻¹ * u * π k = t := by
    simpa only [u, y, t, map_mul, map_inv] using hπy
  have hu_eq : u = t := by
    calc
      u = (π k) * ((π k)⁻¹ * u * π k) * (π k)⁻¹ := by group
      _ = (π k) * ((π k)⁻¹ * t * π k) * (π k)⁻¹ := by rw [hconj_y, hconj_a]
      _ = t := by group
  simpa only [u, t, y, π] using hu_eq

private theorem false_of_normal_odd_quotient {X : Type} [Group X] [Finite X]
    {Z : Subgroup X} [Z.Normal] {a : X} (hZ : Z = Subgroup.zpowers (a ^ 2))
    (ha4 : a ^ 4 = 1) (ha2 : a ^ 2 ≠ 1)
    (hz : ∀ x : X, x * a ^ 2 = a ^ 2 * x)
    {e g : X} (he : e⁻¹ * a * e = a⁻¹)
    (hg : g⁻¹ * e * g * a = a * (g⁻¹ * e * g))
    {N : Subgroup (X ⧸ Z)} (hNn : N.Normal) (hNodd : Odd (Nat.card N))
    (hN : ∀ q : X ⧸ Z,
      q * QuotientGroup.mk' Z a * q⁻¹ * (QuotientGroup.mk' Z a)⁻¹ ∈ N) : False := by
  classical
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  let t : X ⧸ Z := π a
  let y : X := g * a * g⁻¹
  let n : X := a⁻¹ * y
  have hz2 : (a ^ 2) * (a ^ 2) = 1 := by
    rw [← pow_two, ← pow_mul]
    exact ha4
  have hey : e * y = y * e := by
    have h := congrArg (fun z => g * z * g⁻¹) hg
    calc
      e * y = g * (g⁻¹ * e * g * a) * g⁻¹ := by simp only [y]; group
      _ = g * (a * (g⁻¹ * e * g)) * g⁻¹ := by rw [h]
      _ = y * e := by simp only [y]; group
  have hea : e * a⁻¹ * e⁻¹ = a := by
    calc
      e * a⁻¹ * e⁻¹ = e * (e⁻¹ * a * e) * e⁻¹ := by rw [he]
      _ = a := by group
  have heye : e * y * e⁻¹ = y := by
    rw [hey]
    group
  have hen : e * n * e⁻¹ = (a ^ 2) * n := by
    calc
      e * n * e⁻¹ = (e * a⁻¹ * e⁻¹) * (e * y * e⁻¹) := by simp only [n]; group
      _ = a * y := by rw [hea, heye]
      _ = a * (a * n) := by rw [show y = a * n by simp only [n]; group]
      _ = (a ^ 2) * n := by rw [pow_two]; group
  have hπn : π n ∈ N := by
    have hw : π g * t * (π g)⁻¹ * t⁻¹ ∈ N := by
      simpa only [t, π] using hN (π g)
    have hconj : t⁻¹ * (π g * t * (π g)⁻¹ * t⁻¹) * t ∈ N := by
      simpa using hNn.conj_mem (π g * t * (π g)⁻¹ * t⁻¹) hw t⁻¹
    have hπn_eq : π n = t⁻¹ * (π g * t * (π g)⁻¹ * t⁻¹) * t := by
      simp only [n, y, t, π, map_mul, map_inv]
      group
    rwa [hπn_eq]
  let r : ℕ := orderOf (π n)
  have hrOdd : Odd r :=
    Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hπn)
  have hnr_ker : n ^ r ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact pow_orderOf_eq_one (π n)
  have hnrZ : n ^ r ∈ Z := by
    rwa [QuotientGroup.ker_mk'] at hnr_ker
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hZ ▸ hnrZ)
  have hz_pow_odd : (a ^ 2) ^ r = a ^ 2 := by
    obtain ⟨k, hk⟩ := hrOdd
    rw [show r = 2 * k + 1 by omega, pow_succ, pow_mul,
      show (a ^ 2) ^ 2 = 1 by rw [pow_two]; exact hz2]
    simp
  have hcomm_n : e * n ^ r * e⁻¹ = n ^ r := by
    rw [← hi, (Commute.zpow_right (hz e) i).eq]
    group
  have hcalc : e * n ^ r * e⁻¹ = (a ^ 2) * n ^ r := by
    calc
      e * n ^ r * e⁻¹ = (e * n * e⁻¹) ^ r := by rw [conj_pow]
      _ = ((a ^ 2) * n) ^ r := by rw [hen]
      _ = (a ^ 2) ^ r * n ^ r := by rw [Commute.mul_pow (hz n).symm]
      _ = (a ^ 2) * n ^ r := by rw [hz_pow_odd]
  have h1 : (a ^ 2) * n ^ r = 1 * n ^ r := by
    simpa using hcalc.symm.trans hcomm_n
  exact ha2 (mul_right_cancel h1)

theorem false_of_cyclic_four_of_central {X : Type} [Group X] [Finite X] (T : Sylow 2 X) {a : X}
    (ha4 : a ^ 4 = 1) (ha2 : a ^ 2 ≠ 1) (hz : ∀ x : X, x * a ^ 2 = a ^ 2 * x)
    (hsc : ∀ g : X, g⁻¹ * a * g ∈ (T : Subgroup X) → g⁻¹ * a * g ∈ Subgroup.zpowers a)
    {e g : X} (he : e⁻¹ * a * e = a⁻¹) (hg : g⁻¹ * e * g * a = a * (g⁻¹ * e * g)) : False := by
  let Z : Subgroup X := Subgroup.zpowers (a ^ 2)
  have hZeq : Z = Subgroup.zpowers (a ^ 2) := rfl
  have hzc : a ^ 2 ∈ Subgroup.center X :=
    Subgroup.mem_center_iff.mpr fun x => hz x
  have hZn : Z.Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzc)
  letI : Z.Normal := hZn
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  let t : X ⧸ Z := π a
  have hz2 : (a ^ 2) * (a ^ 2) = 1 := by
    rw [← pow_two, ← pow_mul]
    exact ha4
  have haaZ : a * a ∈ Z := by
    rw [hZeq, ← pow_two]
    exact Subgroup.mem_zpowers (a ^ 2)
  have ht2 : t * t = 1 := by
    rw [show t * t = π (a * a) by simp only [t, map_mul]]
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact haaZ
  have ht1 : t ≠ 1 := by
    intro ht
    have haZ : a ∈ Z := by
      rw [← QuotientGroup.ker_mk' Z]
      exact MonoidHom.mem_ker.mpr ht
    have haZ' : a ∈ Subgroup.zpowers (a ^ 2) := hZeq ▸ haZ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp haZ'
    have ha_sq' : (a ^ 2) ^ j * (a ^ 2) ^ j = 1 := by
      have hzpow2 : (a ^ 2) ^ (2 : ℤ) = 1 := by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
        exact hz2
      rcases Int.emod_two_eq_zero_or_one j with hev | hod
      · have hxj : (a ^ 2) ^ j = 1 := by
          conv_lhs => rw [show j = 2 * (j / 2) by
            have h := Int.emod_add_mul_ediv j 2
            omega]
          rw [zpow_mul, hzpow2, one_zpow]
        rw [hxj]
        simp
      · have hxj : (a ^ 2) ^ j = a ^ 2 := by
          conv_lhs => rw [show j = 1 + 2 * (j / 2) by
            have h := Int.emod_add_mul_ediv j 2
            omega]
          rw [zpow_add, zpow_mul, hzpow2, one_zpow, mul_one, zpow_one]
        rw [hxj]
        exact hz2
    have ha_sq : a * a = 1 := hj ▸ ha_sq'
    exact ha2 (by rw [pow_two]; exact ha_sq)
  have hiso : ∀ q : X ⧸ Z,
      (q * t * q⁻¹) * t = t * (q * t * q⁻¹) → q * t * q⁻¹ = t := by
    intro q hq
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective Z q
    have hq' : (QuotientGroup.mk' Z (g' * a * g'⁻¹)) * (QuotientGroup.mk' Z a) =
        (QuotientGroup.mk' Z a) * (QuotientGroup.mk' Z (g' * a * g'⁻¹)) := by
      simpa only [π, t, map_mul, map_inv] using hq
    have h := image_conj_eq_image_of_commute hZeq T ha4 ha2 hz hsc hq'
    simpa only [π, t, map_mul, map_inv] using h
  haveI : Fintype (X ⧸ Z) := Fintype.ofFinite (X ⧸ Z)
  obtain ⟨N, hNn, hNodd, hN⟩ :=
    CFSG.ZStar.glauberman_zStar (X ⧸ Z) t ht1 ht2 hiso
  exact false_of_normal_odd_quotient hZeq ha4 ha2 hz he hg hNn hNodd fun q => by
    simpa only [π, t] using hN q

end Stroth43ZStar

end CFSG.CGT.Stroth77
