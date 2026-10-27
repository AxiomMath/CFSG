module

public import CFSG.CharacterTheory.Wreathed.StationaryScalarCoverageSupport
public import CFSG.CharacterTheory.Semidihedral.EscapingLocalEigensubgroups

public section

open scoped Pointwise commutatorElement

namespace CFSG.Semidihedral.StationaryConfinement

open CFSG.SignalizerFunctor.Helpers
open CFSG.Wreathed.OriginalSylowNormalizerWitness
open CFSG.Semidihedral.EscapingLocalEigensubgroups

section Elements

variable {G : Type*} [Group G]

theorem eq_one_of_eq_inv_of_odd {v : G} (hv : Odd (orderOf v)) (h : v = v⁻¹) : v = 1 := by
  have hsq : v ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h]
    exact mul_inv_cancel v
  have h1 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hv
    exact absurd hv (by decide)

theorem eq_one_of_conj_fixed_inverted {x v : G} (hv : Odd (orderOf v))
    (hfix : x * v * x⁻¹ = v) (hinv : x * v * x⁻¹ = v⁻¹) : v = 1 :=
  eq_one_of_eq_inv_of_odd hv (hfix.symm.trans hinv)

theorem commute_of_inverted_mem_normalizer {x u w : G} (hw : Odd (orderOf w))
    (hxw : x * w * x⁻¹ = w⁻¹) (hwu : w ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G))
    (hxu : x * u = u * x) : w * u = u * w := by
  obtain ⟨k, hk⟩ := hw
  set w' := w ^ (k + 1) with hw'
  have hsq : w' * w' = w := by
    rw [hw', ← pow_add, show k + 1 + (k + 1) = orderOf w + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hxw' : x * w' * x⁻¹ = w'⁻¹ := by
    rw [hw', ← MulAut.conj_apply, map_pow, MulAut.conj_apply, hxw, inv_pow]
  have hw'N : w' ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G) :=
    Subgroup.pow_mem _ hwu _
  have hc : w' * u * w'⁻¹ ∈ Subgroup.zpowers u :=
    (Subgroup.mem_normalizer_iff.mp hw'N u).mp (Subgroup.mem_zpowers u)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hxc : x * (w' * u * w'⁻¹) * x⁻¹ = w' * u * w'⁻¹ := by
    rw [← hi, mul_inv_eq_iff_eq_mul]
    exact ((Commute.zpow_right (show Commute x u from hxu) i)).eq
  have hxc' : x * (w' * u * w'⁻¹) * x⁻¹ = w'⁻¹ * u * w' := by
    have hux : x * u * x⁻¹ = u := by rw [hxu, mul_inv_cancel_right]
    calc x * (w' * u * w'⁻¹) * x⁻¹ = (x * w' * x⁻¹) * (x * u * x⁻¹) * (x * w' * x⁻¹)⁻¹ := by
          group
      _ = w'⁻¹ * u * w' := by rw [hxw', hux, inv_inv]
  have heq : w'⁻¹ * u * w' = w' * u * w'⁻¹ := hxc'.symm.trans hxc
  rw [← hsq]
  calc w' * w' * u = w' * (w' * u * w'⁻¹) * w' := by group
    _ = w' * (w'⁻¹ * u * w') * w' := by rw [heq]
    _ = u * (w' * w') := by group

theorem mem_normalizer_zpowers_of_conj {g u : G} (h : g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u⁻¹) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers (g * u * g⁻¹) = _
  rcases h with h | h
  · rw [h]
  · rw [h, Subgroup.zpowers_inv]

theorem mem_normalizer_zpowers_of_commute {g u : G} (h : g * u = u * g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G) :=
  mem_normalizer_zpowers_of_conj (Or.inl (by rw [h, mul_inv_cancel_right]))

theorem normalizer_zpowers_le_of_conj {K : Subgroup G} {c u : G} (hc : c ∈ K)
    (h : Subgroup.normalizer (Subgroup.zpowers (c * u * c⁻¹) : Set G) ≤ K) :
    Subgroup.normalizer (Subgroup.zpowers u : Set G) ≤ K := by
  intro g hg
  have h1 : c * g * c⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers (c * u * c⁻¹) : Set G) := by
    have := Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hg
    rw [Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers] at this
    exact this
  have h2 := h h1
  have : g = c⁻¹ * (c * g * c⁻¹) * c := by group
  rw [this]
  exact K.mul_mem (K.mul_mem (K.inv_mem hc) h2) hc

theorem normalizer_le_normalizer_centralizer' (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro h
  have hK := Subgroup.mem_normalizer_iff.mp hg
  have hKinv := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg)
  constructor
  · intro hh
    apply Subgroup.mem_centralizer_iff.mpr
    intro k hk
    have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ K := (hKinv k).mp hk
    have hc := Subgroup.mem_centralizer_iff.mp hh _ hk'
    rw [inv_inv] at hc
    calc k * (g * h * g⁻¹) = g * ((g⁻¹ * k * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc]
      _ = g * h * g⁻¹ * k := by group
  · intro hh
    apply Subgroup.mem_centralizer_iff.mpr
    intro k hk
    have hk' : g * k * g⁻¹ ∈ K := (hK k).mp hk
    have hc := Subgroup.mem_centralizer_iff.mp hh _ hk'
    calc k * h = g⁻¹ * ((g * k * g⁻¹) * (g * h * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * h * g⁻¹) * (g * k * g⁻¹)) * g := by rw [hc]
      _ = h * k := by group

theorem mem_normalizer_localFixedGroup {W : Subgroup G} {g i : G}
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) (hgi : g * i = i * g) :
    g ∈ Subgroup.normalizer (localFixedGroup W i : Set G) := by
  apply Subgroup.inf_normalizer_le_normalizer_inf
  refine ⟨hgW, ?_⟩
  apply Subgroup.le_normalizer
  exact Subgroup.mem_centralizer_singleton_iff.mpr hgi

theorem commutatorElement_of_inverted {s u : G} (hsu : s * u * s⁻¹ = u⁻¹) :
    ⁅u, s⁆ = u ^ 2 := by
  have h : s * u⁻¹ * s⁻¹ = u := by
    rw [show s * u⁻¹ * s⁻¹ = (s * u * s⁻¹)⁻¹ by group, hsu, inv_inv]
  rw [commutatorElement_def, pow_two, mul_assoc, mul_assoc, ← mul_assoc s, h]

theorem mem_zpowers_sq_of_odd {u : G} (hu : Odd (orderOf u)) :
    u ∈ Subgroup.zpowers (u ^ 2) := by
  obtain ⟨k, hk⟩ := hu
  refine Subgroup.mem_zpowers_iff.mpr ⟨((k + 1 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, ← pow_mul, show 2 * (k + 1) = orderOf u + 1 by omega, pow_succ,
    pow_orderOf_eq_one, one_mul]

end Elements

section Finite

variable {G : Type*} [Group G] [Finite G]

theorem eq_top_of_forall_sylow_le {X : Type*} [Group X] [Finite X] (B : Subgroup X)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card X → ∃ Q : Sylow ℓ X, (Q : Subgroup X) ≤ B) :
    B = ⊤ := by
  by_contra hne
  have hidx : B.index ≠ 1 := fun h1 => hne (Subgroup.index_eq_one.mp h1)
  obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd hidx
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓX : ℓ ∣ Nat.card X := hdvd.trans B.index_dvd_card
  obtain ⟨Q, hQB⟩ := h ℓ hℓ hℓX
  exact Q.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hQB))

theorem exists_invariant_core_sylow_not_le (H V K : Subgroup G) (hV2 : IsPGroup 2 V)
    (hVH : V ≤ H) (hRK : ¬ (CFSG.pPrimeCore 2 H).map H.subtype ≤ K) :
    ∃ ell : ℕ, ell.Prime ∧ ell ∣ Nat.card (CFSG.pPrimeCore 2 H) ∧
      ∃ W : Sylow ell (CFSG.pPrimeCore 2 H),
        V ≤ Subgroup.normalizer (coveringOddSylowAmbient H W : Set G) ∧
        ¬ coveringOddSylowAmbient H W ≤ K := by
  by_contra hcon
  push Not at hcon
  apply hRK
  set R := CFSG.pPrimeCore 2 H with hRdef
  set Ra := R.map H.subtype with hRadef
  have hRcard : Nat.card Ra = Nat.card R :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hRodd : Odd (Nat.card Ra) := by
    rw [hRcard]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hVRa : V ≤ Subgroup.normalizer (Ra : Set G) :=
    characteristic_subgroup_map_normalized V H (hVH.trans H.le_normalizer) R
  have htop : K.subgroupOf Ra = ⊤ := by
    apply eq_top_of_forall_sylow_le
    intro ℓ hℓ hdiv
    obtain ⟨Q, hQ⟩ := normalized_subgroup_invariant_sylow 2 ℓ Nat.prime_two hℓ V Ra hV2 hVRa
      hRodd.coprime_two_left
    obtain ⟨W, hW⟩ := StationaryOddLocalization.intrinsic_sylow_from_ambient hℓ H R Q
    have hWa : coveringOddSylowAmbient H W =
        (Q : Subgroup Ra).map Ra.subtype := by
      rw [← hW, coveringOddSylowAmbient, Subgroup.map_map]
    have hdivR : ℓ ∣ Nat.card R := hRcard ▸ hdiv
    have hle := hcon ℓ hℓ hdivR W (by rw [hWa]; exact hQ)
    refine ⟨Q, fun x hx => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    apply hle
    rw [hWa]
    exact Subgroup.mem_map_of_mem _ hx
  intro x hx
  have hmem : (⟨x, hx⟩ : Ra) ∈ K.subgroupOf Ra := htop ▸ Subgroup.mem_top _
  exact hmem

theorem exists_inverted_centralizing_witness (V : Subgroup G) [IsKleinFour V]
    {x y : G} (hxV : x ∈ V) (hyV : y ∈ V) (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y)
    {r : ℕ} (hr : r.Prime) (X : Subgroup G) (hXodd : Odd (Nat.card X))
    (hVX : V ≤ Subgroup.normalizer (X : Set G))
    {u : G} (huX : u ∈ X) (hu : orderOf u = r) (hxu : x * u = u * x)
    (hVu : V ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G))
    (F : Subgroup G) (hFX : F ≤ X) (hFp : IsPGroup r F)
    (hVF : V ≤ Subgroup.normalizer (F : Set G))
    {w : G} (hwF : w ∈ F) (hw1 : w ≠ 1) (hxw : x * w * x⁻¹ = w⁻¹) :
    ∃ v : G, v ≠ 1 ∧ IsPGroup r (Subgroup.zpowers v) ∧ x * v * x⁻¹ = v⁻¹ ∧
      v * u = u * v := by
  have : Fact r.Prime := ⟨hr⟩
  have hV2 : IsPGroup 2 V :=
    IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  have hrodd : Odd r := by
    rw [← hu]
    exact hXodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard X huX)
  have hup : IsPGroup r (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨Q, huQ, hVQ⟩ := CFSG.Wreathed.StationaryScalarCoverage.exists_invariant_sylow_containing
    hr V X (Subgroup.zpowers u) hV2 hXodd hVX (Subgroup.zpowers_le.mpr huX) hup hVu
  set QG := (Q : Subgroup X).map X.subtype with hQG
  have hQGp : IsPGroup r QG := Q.isPGroup'.map X.subtype
  obtain ⟨c, hc, hFle⟩ :=
    CFSG.Semidihedral.StationaryOddLocalization.invariant_pgroup_le_fixed_conjugate_sylow
      hr V X F hV2 hVX hXodd Q hVQ hFX hFp hVF
  obtain ⟨q, hq, hqw⟩ := hFle hwF
  change c * q * c⁻¹ = w at hqw
  have hcx : c * x = x * c := (Subgroup.mem_centralizer_iff.mp hc.2 x hxV).symm
  have hxq : x * q * x⁻¹ = q⁻¹ := by
    have hq' : q = c⁻¹ * w * c := by rw [← hqw]; group
    have h1 : x * c⁻¹ = c⁻¹ * x := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hcx, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : c * x⁻¹ = x⁻¹ * c := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, hcx, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hq']
    calc x * (c⁻¹ * w * c) * x⁻¹ = (x * c⁻¹) * w * (c * x⁻¹) := by group
      _ = c⁻¹ * (x * w * x⁻¹) * c := by rw [h1, h2]; group
      _ = (c⁻¹ * w * c)⁻¹ := by rw [hxw]; group
  have hq1 : q ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hqw
    exact hw1 hqw.symm
  let _action := conjugationAction V QG hVQ
  let a : V := ⟨x, hxV⟩
  let b : V := ⟨y, hyV⟩
  have ha : a ≠ 1 := fun h => hx (congrArg (fun z : V => (z : G)) h)
  have hb : b ≠ 1 := fun h => hy (congrArg (fun z : V => (z : G)) h)
  have hab : a ≠ b := fun h => hxy (congrArg (fun z : V => (z : G)) h)
  have hF : actionCentralizer (X := QG) a ≠ ⊤ := by
    intro htop
    have hmem : (⟨q, hq⟩ : QG) ∈ actionCentralizer (X := QG) a := by
      rw [htop]
      exact Subgroup.mem_top _
    have hfix := congrArg (fun z : QG => (z : G)) ((mem_actionCentralizer (a := a)).mp hmem)
    change x * q * x⁻¹ = q at hfix
    have hqodd : Odd (orderOf q) := hXodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard X
      (Subgroup.map_subtype_le _ hq))
    exact hq1 (eq_one_of_conj_fixed_inverted hqodd hfix hxq)
  obtain ⟨-, -, v, hv1, hva, -, hvcomm, -⟩ :=
    four_group_odd_p_group_centralizing_inverted_witness hr hrodd hQGp a b ha hb hab hF
  have huQG : (⟨u, huQ (Subgroup.mem_zpowers u)⟩ : QG) ∈ actionCentralizer (X := QG) a := by
    apply (mem_actionCentralizer (a := a)).mpr
    apply Subtype.ext
    change x * u * x⁻¹ = u
    rw [hxu, mul_inv_cancel_right]
  have hvu := congrArg (fun z : QG => (z : G)) (hvcomm _ huQG).eq
  exact ⟨v, fun h => hv1 (Subtype.ext h), hQGp.to_le (Subgroup.zpowers_le.mpr v.property),
    congrArg (fun z : QG => (z : G)) hva, hvu⟩

omit [Finite G] in
theorem orderOf_ne_of_normal_inverted_core_sylow {x u : G} (H0 : Subgroup G)
    (hH0 : H0 ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G))
    (huO : u ∈ (CFSG.pPrimeCore 2 H0).map H0.subtype) {ell : ℕ} (hell : ell.Prime)
    (W : Sylow ell (CFSG.pPrimeCore 2 H0))
    (hWinv : ∀ w ∈ coveringOddSylowAmbient H0 W, x * w * x⁻¹ = w⁻¹)
    (hxu : x * u = u * x) (huodd : Odd (orderOf u)) (hu1 : u ≠ 1) : orderOf u ≠ ell := by
  intro hul
  have : Fact ell.Prime := ⟨hell⟩
  let φ : CFSG.pPrimeCore 2 H0 →* G := H0.subtype.comp (CFSG.pPrimeCore 2 H0).subtype
  have hφ : Function.Injective φ :=
    H0.subtype_injective.comp (CFSG.pPrimeCore 2 H0).subtype_injective
  let U' : Subgroup (CFSG.pPrimeCore 2 H0) := (Subgroup.zpowers u).comap φ
  have hU'n : U'.Normal := ⟨fun a ha o => by
    change φ (o * a * o⁻¹) ∈ Subgroup.zpowers u
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hH0 (o : H0).2) (φ a)).mp ha⟩
  have hU'p : IsPGroup ell U' := by
    intro a
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    apply hφ
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    change φ ((a : CFSG.pPrimeCore 2 H0) ^ ell) = φ 1
    rw [map_pow, map_one, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      ← hul, pow_orderOf_eq_one, one_zpow]
  have hle := hU'p.le_sylow_of_normal W
  obtain ⟨o, ho, hou⟩ := huO
  have ha : (⟨o, ho⟩ : CFSG.pPrimeCore 2 H0) ∈ U' := by
    change (o : G) ∈ Subgroup.zpowers u
    rw [show (o : G) = u from hou]
    exact Subgroup.mem_zpowers u
  have huW : u ∈ coveringOddSylowAmbient H0 W := by
    refine ⟨⟨o, ho⟩, hle ha, ?_⟩
    exact hou
  have h1 := hWinv u huW
  rw [hxu, mul_inv_cancel_right] at h1
  exact hu1 (eq_one_of_eq_inv_of_odd huodd h1)

theorem eq_one_of_orderOf_dvd_odd_prime {X : Type*} [Group X] (K : Subgroup X) [Finite K]
    {z : X} (hz : z ∈ K) {r p f : ℕ} (hr : r.Prime) (hrodd : Odd r) (hp : p.Prime)
    (hrp : r ≠ p) (hK : Nat.card K = p ^ f * 2) (hzr : orderOf z ∣ r) : z = 1 := by
  have hzK : orderOf z ∣ p ^ f * 2 := hK ▸ Subgroup.orderOf_dvd_natCard K hz
  rcases (Nat.dvd_prime hr).mp hzr with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    rw [h1] at hzK
    rcases (Nat.Prime.dvd_mul hr).mp hzK with h2 | h2
    · exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h2))
    · have h3 : r ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      have h4 := hr.two_le
      have h5 : r = 2 := by omega
      rw [h5] at hrodd
      exact absurd hrodd (by decide)

end Finite

end CFSG.Semidihedral.StationaryConfinement
