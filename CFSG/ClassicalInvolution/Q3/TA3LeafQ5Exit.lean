module

public import CFSG.ClassicalInvolution.Q3.TA3SmallCriteria
public import CFSG.ClassicalInvolution.Q3.Q3TLT3Act
public import CFSG.ClassicalInvolution.AschTight.S1916Omega

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic QuaternionGroup
open CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

namespace Q5Exit

theorem q8_exists_inv : ∀ g : QuaternionGroup 2, g ^ 2 ≠ 1 → ∃ h, h * g * h⁻¹ = g⁻¹ := by
  decide

end Q5Exit

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.exists_conj_mem_of_pow (S : Sylow 2 R) {s : Y} (hsR : s ∈ R) {k : ℕ}
    (hs : s ^ 2 ^ k = 1) : ∃ r ∈ R, r * s * r⁻¹ ∈ (S : Subgroup R).map R.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s' : R := ⟨s, hsR⟩ with hs'
  have hs'k : s' ^ 2 ^ k = 1 := Subtype.ext (by simpa [hs'] using hs)
  obtain ⟨m, hm⟩ := exists_orderOf_eq_prime_pow_iff.mpr ⟨k, hs'k⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers s') :=
    IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨Q, hQ⟩ := h2.exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R Q S
  have hmem : r * s' * r⁻¹ ∈ ((r • Q : Sylow 2 R) : Subgroup R) := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr
      (by simpa [mul_assoc] using hQ (Subgroup.mem_zpowers s'))
  rw [hr] at hmem
  exact ⟨r, r.2, _, hmem, rfl⟩

theorem TightDatum.exists_eq_conjSub_of_mem_RSet (hD : TightDatum R S t) {P : Subgroup Y}
    (hP : P ∈ RSet (CoreAssembly.conjClass (tightCore R))) :
    ∃ x : Y, P = conjSub x ((S : Subgroup R).map R.subtype) := by
  obtain ⟨J, hJ, hPJ⟩ := exists_isSylow2In_of_mem_RSet hP
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class _ J hJ
  obtain ⟨c, -, hc⟩ := Disconnected.AschTight.S1916.IsSylow2In.exists_conj
    (Disconnected.AschTight.S1916.IsSylow2In.conj hD.sylow_core g) hPJ
  exact ⟨c * g, by rw [conjSub_mul, hc]⟩

theorem TightDatum.sq_eq_of_orderOf_eq_four (hD : TightDatum R S t) {s : Y} (hsR : s ∈ R)
    (hs4 : orderOf s = 4) : s * s = t := by
  have h1 : orderOf (s ^ 2) = 2 := by
    rw [orderOf_pow' s (by norm_num), hs4]
    rfl
  rw [← pow_two]
  exact hD.eq_of_orderOf_eq_two (R.pow_mem hsR 2) h1

theorem TightDatum.not_tightActs3_of_cyclic4 (hD : TightDatum R S t)
    (hS : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) {N : Subgroup Y} [N.Normal]
    {s : Y} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4)
    (hab : ∀ a ∈ R, a ∈ N → ∀ b ∈ R, b ∈ N → a * b = b * a) : ¬ TightActs3 R t := by
  rintro ⟨x, k, hxC, hx3, r, hr, hxr⟩
  obtain ⟨eS⟩ := hS
  have hO : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S hD.quat hD.mem hD.order hD.cent hD.normal hD.twoGroup
  let eM : (R ⧸ oddCore R) ≃* QuaternionGroup 2 :=
    (MulEquiv.ofBijective _ hO.bijective_restrict).symm.trans
      ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans eS)
  have hxN : x ∈ Subgroup.normalizer (R : Set Y) := hD.le_normalizer hxC
  set φ := tl3Act R ⟨x, hxN⟩ with hφ
  have hφ3 : φ ^ 3 ^ k = 1 := by
    have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (R : Set Y)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [hφ, ← map_pow, h1, map_one]
  have hφ1 : φ ≠ 1 := fun h => hxr ((tl3Act_eq_one_iff R _).mp h r hr)
  set sb : R ⧸ oddCore R := ((⟨s, hsR⟩ : R) : R ⧸ oddCore R) with hsb
  have hs2 := TightDatum.sq_eq_of_orderOf_eq_four hD hsR hs4
  have htO : t ∉ oddCoreImg R := fun ht => by
    have hdvd : orderOf t ∣ Nat.card (oddCoreImg R) := Subgroup.orderOf_dvd_natCard _ ht
    rw [hD.order] at hdvd
    exact (Nat.not_even_iff_odd.mpr (odd_natCard_oddCoreImg R)) (even_iff_two_dvd.mpr hdvd)
  have hsb2 : ¬ sb ^ 2 ^ 1 = 1 := by
    intro h
    rw [hsb, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
      mem_oddCore_iff_coe_mem_oddCoreImg] at h
    apply htO
    rw [← hs2]
    simpa [pow_two] using h
  have hsb4' : sb ^ 2 ^ (1 + 1) = 1 := by
    rw [hsb, ← QuotientGroup.mk_pow]
    have h1 : (⟨s, hsR⟩ : R) ^ 2 ^ (1 + 1) = 1 :=
      Subtype.ext (by simp [← hs4, pow_orderOf_eq_one])
    rw [h1, QuotientGroup.mk_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsb4 : orderOf sb = 4 := orderOf_eq_prime_pow hsb2 hsb4'
  have hpow : ∀ m : ℕ, (φ ^ m) sb =
      ((R.normalizerMonoidHom (⟨x, hxN⟩ ^ m) ⟨s, hsR⟩ : R) : R ⧸ oddCore R) := fun m => by
    rw [hφ, ← map_pow, hsb, tl3Act_mk]
  have hmemN : ∀ m : ℕ, ((R.normalizerMonoidHom (⟨x, hxN⟩ ^ m) ⟨s, hsR⟩ : R) : Y) ∈ N :=
    fun m => by
      rw [tl3_normalizerMonoidHom_coe]
      exact (inferInstance : N.Normal).conj_mem s hsN _
  have hA4 : orderOf (eM.symm (a 1)) = 4 := by
    rw [MulEquiv.orderOf_eq, orderOf_a_one]
  have hB4 : orderOf (eM.symm (xa 0)) = 4 := by
    rw [MulEquiv.orderOf_eq, orderOf_xa]
  obtain ⟨m₁, -, h₁⟩ := tl3_aut_transitive eM hφ3 hφ1 hsb4 hA4
  obtain ⟨m₂, -, h₂⟩ := tl3_aut_transitive eM hφ3 hφ1 hsb4 hB4
  rw [hpow] at h₁ h₂
  set n₁ := (R.normalizerMonoidHom (⟨x, hxN⟩ ^ m₁) ⟨s, hsR⟩ : R)
  set n₂ := (R.normalizerMonoidHom (⟨x, hxN⟩ ^ m₂) ⟨s, hsR⟩ : R)
  have hn : n₁ * n₂ = n₂ * n₁ := Subtype.ext (hab _ n₁.2 (hmemN m₁) _ n₂.2 (hmemN m₂))
  have hc : Commute (n₁ : R ⧸ oddCore R) (n₂ : R ⧸ oddCore R) := by
    show _ * _ = _ * _
    rw [← QuotientGroup.mk_mul, hn, QuotientGroup.mk_mul]
  have key : Commute (eM.symm (a 1)) (eM.symm (xa 0)) := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁, h₂] at hc
    · exact hc
    · exact Commute.inv_right_iff.mp hc
    · exact Commute.inv_left_iff.mp hc
    · exact Commute.inv_left_iff.mp (Commute.inv_right_iff.mp hc)
  have h := congrArg eM key.eq
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
  exact absurd h (by decide)

theorem TightDatum.tightEdgeless_of_sq (hD : TightDatum R S t)
    (hS : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) {N J : Subgroup Y} [N.Normal]
    (htN : t ∈ N) (hRJ : R ≤ Subgroup.centralizer (J : Set Y))
    {s : Y} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4)
    (hinv : ∀ v ∈ N, v ∈ Subgroup.centralizer ({t} : Set Y) →
      v ∈ Subgroup.centralizer (J : Set Y) → v * v = 1 → v = 1 ∨ v = t)
    (hsq : ∀ y ∈ N, y ∈ Subgroup.centralizer ({t} : Set Y) → y * y = t →
      y ∉ Subgroup.centralizer (J : Set Y) → y ∈ J) : TightEdgeless R := by
  obtain ⟨eS⟩ := hS
  set S₀ := (S : Subgroup R).map R.subtype with hS₀
  have ht1 : t ≠ 1 := fun h => by
    have := hD.order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have htt : t * t = 1 := by rw [← pow_two, ← hD.order, pow_orderOf_eq_one]
  obtain ⟨r, hrR, hrs⟩ := TightDatum.exists_conj_mem_of_pow S hsR (k := 2)
    (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hs4, pow_orderOf_eq_one])
  set s' := r * s * r⁻¹ with hs'
  have hs'R : s' ∈ R := R.mul_mem (R.mul_mem hrR hsR) (R.inv_mem hrR)
  have hs'N : s' ∈ N := (inferInstance : N.Normal).conj_mem s hsN r
  have hs'4 : orderOf s' = 4 := by
    rw [hs', ← MulAut.conj_apply, MulEquiv.orderOf_eq, hs4]
  have hs'2 := TightDatum.sq_eq_of_orderOf_eq_four hD hs'R hs'4
  let eS₀ : S₀ ≃* QuaternionGroup 2 :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans eS
  have he2 : eS₀ ⟨s', hrs⟩ ^ 2 ≠ 1 := by
    intro h
    have h1 : (⟨s', hrs⟩ : S₀) ^ 2 = 1 := eS₀.injective (by rw [map_pow, h, map_one])
    have h2 : s' * s' = 1 := by simpa [pow_two] using congrArg Subtype.val h1
    exact ht1 (hs'2.symm.trans h2)
  obtain ⟨h, hh⟩ := Q5Exit.q8_exists_inv _ he2
  set j : Y := ((eS₀.symm h : S₀) : Y) with hj
  have hjS : j ∈ S₀ := (eS₀.symm h).2
  have hjs : j * s' * j⁻¹ = s'⁻¹ := by
    have h1 : eS₀.symm h * ⟨s', hrs⟩ * (eS₀.symm h)⁻¹ = (⟨s', hrs⟩ : S₀)⁻¹ :=
      eS₀.injective (by simpa using hh)
    simpa [hj] using congrArg Subtype.val h1
  refine TightDatum.edgeless_of_forall hD fun P hP hPC => ?_
  obtain ⟨x, rfl⟩ := TightDatum.exists_eq_conjSub_of_mem_RSet hD hP
  set v := x⁻¹ * t * x with hv
  have hSv : ∀ g ∈ S₀, g * v = v * g := fun g hg => by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hPC (conj_mem_conjSub (n := x) hg))
    calc g * v = x⁻¹ * ((x * g * x⁻¹) * t) * x := by rw [hv]; group
      _ = x⁻¹ * (t * (x * g * x⁻¹)) * x := by rw [h1]
      _ = v * g := by rw [hv]; group
  have hvt : v = t := by
    by_contra hne
    have hvN : v ∈ N := by
      have := (inferInstance : N.Normal).conj_mem t htN x⁻¹
      rwa [inv_inv] at this
    have hv2 : v * v = 1 := by
      calc v * v = x⁻¹ * (t * t) * x := by rw [hv]; group
        _ = 1 := by rw [htt]; group
    have hvC : v ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hSv t hD.mem).symm
    have hs'v : s' * v = v * s' := hSv s' hrs
    have hs'C : s' ∈ Subgroup.centralizer ({t} : Set Y) := hD.cent hs'R
    have hs'J : s' ∈ Subgroup.centralizer (J : Set Y) := hRJ hs'R
    have hyN : s' * v ∈ N := N.mul_mem hs'N hvN
    have hyC : s' * v ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.mul_mem _ hs'C hvC
    have hy2 : s' * v * (s' * v) = t := by
      calc s' * v * (s' * v) = s' * (v * s') * v := by group
        _ = s' * (s' * v) * v := by rw [hs'v]
        _ = s' * s' * (v * v) := by group
        _ = t := by rw [hs'2, hv2, mul_one]
    by_cases hyJ : s' * v ∈ Subgroup.centralizer (J : Set Y)
    · have hvJ : v ∈ Subgroup.centralizer (J : Set Y) := by
        have e : v = s'⁻¹ * (s' * v) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hs'J) hyJ
      rcases hinv v hvN hvC hvJ hv2 with h1 | h1
      · apply ht1
        have e : t = x * v * x⁻¹ := by rw [hv]; group
        rw [e, h1]
        group
      · exact hne h1
    · have hyJ' := hsq _ hyN hyC hy2 hyJ
      have hjR : j ∈ R := Subgroup.map_subtype_le _ hjS
      have hjy : (s' * v) * j = j * (s' * v) :=
        Subgroup.mem_centralizer_iff.mp (hRJ hjR) _ hyJ'
      have hjv : j * v = v * j := hSv j hjS
      have e1 : s' * v = s'⁻¹ * v := by
        calc s' * v = j * (s' * v) * j⁻¹ := by rw [← hjy]; group
          _ = (j * s' * j⁻¹) * (j * v * j⁻¹) := by group
          _ = s'⁻¹ * v := by rw [hjs, hjv]; group
      have e2 : s' * s' = 1 := by
        have := mul_right_cancel e1
        calc s' * s' = s' * s'⁻¹ := by rw [← this]
          _ = 1 := mul_inv_cancel s'
      exact ht1 (hs'2.symm.trans e2)
  rw [mem_conjSub_iff, ← hv, hvt]
  exact hD.mem

end CFSG.ClassicalInvolution.Q3.TA3
