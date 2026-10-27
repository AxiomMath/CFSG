module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdQuot
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdFusion
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem orderOf_mk'_eq_two_of_odd {U : Subgroup X} [U.Normal]
    (hU : Odd (Nat.card U)) {t : X} (ht : orderOf t = 2) :
    orderOf (QuotientGroup.mk' U t) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, show t ^ 2 = 1 by rw [← ht]; exact pow_orderOf_eq_one t, map_one]
  · intro h1
    have htU : t ∈ U := by
      rw [← QuotientGroup.eq_one_iff (N := U) t, ← QuotientGroup.mk'_apply]
      exact h1
    exact hU.not_two_dvd_nat (ht ▸ Subgroup.orderOf_dvd_natCard U htU)

theorem lieModel_map_and_center_of_odd {U : Subgroup X} [U.Normal] (hU : Odd (Nat.card U))
    {K : Subgroup X} (hKq : IsQuasisimple ↥K)
    (hKL : Blueprint.LieModel (↥K ⧸ center ↥K) .PSL 3 2 2)
    {w : X} (hwK : w ∈ K) (hw : orderOf w = 4)
    (hZK : ∀ c ∈ K, (∀ k ∈ K, c * k = k * c) → (∃ n : ℕ, c ^ 2 ^ n = 1) → c ∈ zpowers w) :
    IsQuasisimple ↥(K.map (QuotientGroup.mk' U)) ∧
      Blueprint.LieModel (↥(K.map (QuotientGroup.mk' U)) ⧸ center ↥(K.map (QuotientGroup.mk' U)))
        .PSL 3 2 2 ∧
      orderOf (QuotientGroup.mk' U w) = 4 ∧
      ∀ c ∈ K.map (QuotientGroup.mk' U),
        (∀ d ∈ K.map (QuotientGroup.mk' U), c * d = d * c) → orderOf c = 2 →
          c = QuotientGroup.mk' U w * QuotientGroup.mk' U w := by
  classical
  let π : X →* X ⧸ U := QuotientGroup.mk' U
  let D : Subgroup (X ⧸ U) := K.map π
  have hw2ord : orderOf (w * w) = 2 := by
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [hw]; norm_num), hw]
  have hK2 : ∃ k ∈ K, orderOf k = 2 := ⟨w * w, K.mul_mem hwK hwK, hw2ord⟩
  let φ : ↥K →* ↥D :=
    { toFun := fun k => ⟨π (k : X), Subgroup.mem_map.mpr ⟨k, k.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  have hφsurj : Function.Surjective φ := by
    intro d
    obtain ⟨k, hk, hval⟩ := Subgroup.mem_map.mp d.2
    exact ⟨⟨k, hk⟩, Subtype.ext hval⟩
  have hcent_map : ∀ k : ↥K, φ k ∈ center ↥D ↔ k ∈ center ↥K := by
    intro k
    constructor
    · intro hkZ
      rw [Subgroup.mem_center_iff] at hkZ ⊢
      have hcomm : ∀ k' ∈ K, (k : X) * k' * (k : X)⁻¹ * k'⁻¹ ∈ U := by
        intro k' hk'
        have h := hkZ (φ ⟨k', hk'⟩)
        have hval : π k' * π (k : X) = π (k : X) * π k' := by
          have h' := congrArg (Subtype.val) h
          change π k' * π (k : X) = π (k : X) * π k' at h'
          exact h'
        have h1 : π (k' * (k : X) * k'⁻¹ * (k : X)⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hval]
          group
        have h2 : k' * (k : X) * k'⁻¹ * (k : X)⁻¹ ∈ U :=
          (QuotientGroup.eq_one_iff _).mp h1
        have h3 : (k' * (k : X) * k'⁻¹ * (k : X)⁻¹)⁻¹ ∈ U := U.inv_mem h2
        simpa [mul_inv_rev, mul_assoc] using h3
      have hcommK := commute_of_commutator_mem_of_odd hU hKq hK2 k.2 hcomm
      intro y
      apply Subtype.ext
      exact (hcommK (y : X) y.2).symm
    · intro hkZ
      rw [Subgroup.mem_center_iff] at hkZ ⊢
      intro d
      obtain ⟨k', hk', hval⟩ := Subgroup.mem_map.mp d.2
      have hd : d = φ ⟨k', hk'⟩ := Subtype.ext hval.symm
      rw [hd]
      apply Subtype.ext
      show π k' * π (k : X) = π (k : X) * π k'
      have h := congrArg (Subtype.val) (hkZ ⟨k', hk'⟩)
      change (k' : X) * (k : X) = (k : X) * k' at h
      rw [← map_mul, ← map_mul, h]
  let ψ : ↥K →* ↥D ⧸ center ↥D := (QuotientGroup.mk' (center ↥D)).comp φ
  have hψker : ψ.ker = center ↥K := by
    ext k
    rw [MonoidHom.mem_ker]
    constructor
    · intro hk
      exact (hcent_map k).mp ((QuotientGroup.eq_one_iff (φ k)).mp hk)
    · intro hk
      exact (QuotientGroup.eq_one_iff (φ k)).mpr ((hcent_map k).mpr hk)
  have hψsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective (center ↥D)).comp hφsurj
  let e : ↥K ⧸ center ↥K ≃* ↥D ⧸ center ↥D :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  have hKperf : ⁅K, K⁆ = K := (Subgroup.isPerfect_iff (H := K)).mp hKq.1
  have hDcomm : ⁅D, D⁆ = D := by
    have h := Subgroup.map_commutator K K π
    rw [hKperf] at h
    exact h.symm
  have hDperf : Group.IsPerfect ↥D := (Subgroup.isPerfect_iff (H := D)).mpr hDcomm
  have hDsimple : IsSimpleGroup (↥D ⧸ center ↥D) :=
    (MulEquiv.isSimpleGroup_congr e).mp hKq.2.1
  have hDnonab : ∃ a b : ↥D ⧸ center ↥D, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKq.2.2
    refine ⟨e a, e b, fun h => hab ?_⟩
    have h' : e (a * b) = e (b * a) := by
      simpa only [map_mul] using h
    exact e.injective h'
  have hπw4 : orderOf (π w) = 4 := by
    have hdvd : orderOf (π w) ∣ 4 := by
      rw [← hw]
      exact orderOf_map_dvd π w
    have hne1 : π w ≠ 1 := by
      intro h1
      have hwU : w ∈ U := (QuotientGroup.eq_one_iff w).mp h1
      have hd : orderOf w ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hwU
      rw [hw] at hd
      exact hU.not_two_dvd_nat (dvd_trans (by norm_num) hd)
    have hne2 : (π w) ^ 2 ≠ 1 := by
      intro h2
      have hw2U : w * w ∈ U := by
        have h1 : π (w * w) = 1 := by
          rw [map_mul]
          rw [show π w * π w = (π w) ^ 2 from (pow_two _).symm, h2]
        exact (QuotientGroup.eq_one_iff (w * w)).mp h1
      have hd : orderOf (w * w) ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hw2U
      rw [hw2ord] at hd
      exact hU.not_two_dvd_nat hd
    have hdvd2 : ¬ orderOf (π w) ∣ 2 := fun h => hne2 (orderOf_dvd_iff_pow_eq_one.mp h)
    obtain ⟨k, hk2, hk⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two (m := 2) (i := orderOf (π w))).mp (by simpa using hdvd)
    interval_cases k
    · exact absurd (orderOf_eq_one_iff.mp hk) hne1
    · exact absurd (by rw [hk]; norm_num) hdvd2
    · rw [hk]
      norm_num
  refine ⟨⟨hDperf, hDsimple, hDnonab⟩, ?_, hπw4, ?_⟩
  · exact Blueprint.LieModel.of_mulEquiv e hKL
  ·
    intro c hcD hccent hc2
    obtain ⟨k, hkK, hkπ⟩ := Subgroup.mem_map.mp hcD
    have hφk : φ ⟨k, hkK⟩ = ⟨c, hcD⟩ := Subtype.ext hkπ
    have hkZ : (⟨k, hkK⟩ : ↥K) ∈ center ↥K := by
      refine (hcent_map ⟨k, hkK⟩).mp ?_
      rw [hφk]
      rw [Subgroup.mem_center_iff]
      intro d
      apply Subtype.ext
      exact (hccent (d : X ⧸ U) d.2).symm
    have hkcomm : ∀ k' ∈ K, k * k' = k' * k := by
      intro k' hk'
      exact (congrArg (Subtype.val) (Subgroup.mem_center_iff.mp hkZ ⟨k', hk'⟩)).symm
    obtain ⟨a, s, hsodd, hkord⟩ :=
      Nat.exists_eq_two_pow_mul_odd (n := orderOf k) (orderOf_pos k).ne'
    have hk₂K : k ^ s ∈ K := K.pow_mem hkK s
    have hk₂comm : ∀ k' ∈ K, k ^ s * k' = k' * (k ^ s) := by
      intro k' hk'
      exact (Commute.pow_left (a := k) (b := k') (hkcomm k' hk') s).eq
    have hk₂pow : ∃ n : ℕ, (k ^ s) ^ 2 ^ n = 1 := by
      refine ⟨a, ?_⟩
      rw [← pow_mul, Nat.mul_comm s (2 ^ a), ← hkord]
      exact pow_orderOf_eq_one k
    have hk₂zp : k ^ s ∈ zpowers w := hZK (k ^ s) hk₂K hk₂comm hk₂pow
    have hcs : (π k) ^ s = c := by
      have hck2 : c ^ 2 = 1 := by
        rw [← hc2]
        exact pow_orderOf_eq_one c
      rw [hkπ]
      obtain ⟨t, ht⟩ := hsodd
      calc c ^ s = c ^ (2 * t + 1) := by rw [ht]
        _ = c ^ (2 * t) * c ^ 1 := pow_add _ _ _
        _ = (c ^ 2) ^ t * c ^ 1 := by rw [pow_mul]
        _ = c := by simp [hck2]
    have hc_eq_k : c = π (k ^ s) := by
      calc c = π k := hkπ.symm
        _ = (π k) ^ s := hkπ.trans hcs.symm
        _ = π (k ^ s) := (map_pow π k s).symm
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hk₂zp
    have hgj : (π w) ^ j = c := by
      calc (π w) ^ j = π (w ^ j) := (map_zpow π w j).symm
        _ = π (k ^ s) := by rw [hj]
        _ = c := hc_eq_k.symm
    have hmod : (π w) ^ (j % 4) = c := by
      have h1 := zpow_mod_orderOf (π w) j
      rw [hπw4] at h1
      exact h1.trans hgj
    set r : ℕ := (j % 4).toNat with hrdef
    have hr : (r : ℤ) = j % 4 := by
      rw [hrdef]
      exact Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num))
    have hr4 : r < 4 := by
      rw [hrdef, Int.toNat_lt (Int.emod_nonneg j (by norm_num))]
      exact Int.emod_lt_of_pos j (by norm_num)
    have hmodn : (π w) ^ r = c := by
      rw [← hr, zpow_natCast] at hmod
      exact hmod
    interval_cases r
    · rw [← hmodn] at hc2
      simp only [pow_zero, orderOf_one] at hc2
      exfalso
      omega
    · rw [← hmodn, pow_one] at hc2
      rw [hπw4] at hc2
      exfalso
      omega
    · rw [← hmodn, pow_two]
    · have h3 : (π w) ^ 3 = (π w)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        show (π w) ^ 3 * (π w) = 1
        rw [← pow_succ]
        have h4 : (π w) ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hπw4])
        simpa using h4
      rw [← hmodn, h3, orderOf_inv, hπw4] at hc2
      exfalso
      omega

theorem false_of_isComponent_map_of_conj_eq_mul {U : Subgroup X} [U.Normal]
    (hU : Odd (Nat.card U)) {t : X} (ht : t ^ 2 = 1) {K : Subgroup X} (hKq : IsQuasisimple ↥K)
    (hK2 : ∃ k ∈ K, orderOf k = 2) (hKt : K ≤ centralizer ({t} : Set X))
    (hperf : ∀ L : Subgroup X, L ≤ centralizer ({t} : Set X) → ⁅L, L⁆ = L → L ≤ K)
    (hcomp : IsComponent (K.map (QuotientGroup.mk' U))) {u x : X} (huK : u ∈ K)
    (hu : ∃ k ∈ K, u * k ≠ k * u) (hconj : x⁻¹ * t * x = u * t) : False := by
  classical
  let π : X →* X ⧸ U := QuotientGroup.mk' U
  have htbar : π t * π t = 1 := by simpa [pow_two, map_mul] using congrArg π ht
  have hKbarC : K.map π ≤ centralizer ({π t} : Set (X ⧸ U)) := by
    rintro _ ⟨k, hkK, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hkt : t * k = k * t := Subgroup.mem_centralizer_iff.mp (hKt hkK) t rfl
    rw [← map_mul, ← map_mul, hkt]
  have hperfbar : ∀ L : Subgroup (X ⧸ U),
      L ≤ centralizer ({π t} : Set (X ⧸ U)) → ⁅L, L⁆ = L → L ≤ K.map π := by
    intro L hL hLp
    exact le_map_of_perfect_le_centralizer_quotient hU ht hperf hL hLp
  have hconjbar : (π x)⁻¹ * π t * π x = π u * π t := by
    have h := congrArg π hconj
    simpa only [map_mul, map_inv] using h
  have hcent : ∀ k ∈ K.map π, π u * k = k * π u :=
    commute_of_conj_eq_mul_of_isComponent (Y := X ⧸ U) (K := K.map π) hcomp
      hKbarC hperfbar (Subgroup.mem_map_of_mem π huK) hconjbar
  have huU : ∀ k ∈ K, u * k * u⁻¹ * k⁻¹ ∈ U := by
    intro k hkK
    have hkbar : π k ∈ K.map π := Subgroup.mem_map_of_mem π hkK
    have hcommπ : π u * π k = π k * π u := hcent (π k) hkbar
    have hq : π (u * k * u⁻¹ * k⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcommπ]
      group
    have hq' : (QuotientGroup.mk' U (u * k * u⁻¹ * k⁻¹) : X ⧸ U) = 1 := by
      simpa [π] using hq
    rw [QuotientGroup.mk'_apply] at hq'
    exact (QuotientGroup.eq_one_iff _).mp hq'
  have hcommu : ∀ k ∈ K, u * k = k * u :=
    commute_of_commutator_mem_of_odd hU hKq hK2 huK huU
  obtain ⟨k, hk, huk⟩ := hu
  exact huk (hcommu k hk)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
