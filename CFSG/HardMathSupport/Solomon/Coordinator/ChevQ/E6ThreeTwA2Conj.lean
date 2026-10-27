module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwA2ConjLift
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwA2ConjStmt
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjBar
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjClass
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjIndex

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LieType.Steinberg

theorem twistHom_mul_of_twLang {L : Type} [Field L] {Fr : L →+* L}
    {a b n : ModGL TwistTag.E6.tag L} (ha : twistHom TwistTag.E6 L Fr a = a * n)
    (hb : twistHom TwistTag.E6 L Fr b = n⁻¹ * b * n) :
    twistHom TwistTag.E6 L Fr (a * b) = a * b * n := by
  rw [map_mul, ha, hb]
  group

theorem twistHom_of_twFrob_fixed {L : Type} [Field L] {Fr : L →+* L}
    {n u : ModGL TwistTag.E6.tag L} (h : twFrob TwistTag.E6 n Fr u = u) :
    twistHom TwistTag.E6 L Fr u = n⁻¹ * u * n := by
  rw [twFrob_apply] at h
  calc twistHom TwistTag.E6 L Fr u = n⁻¹ * (n * twistHom TwistTag.E6 L Fr u * n⁻¹) * n := by
        group
    _ = n⁻¹ * u * n := by rw [h]

section Conj


theorem tw_exists_lang_datum_threeA2 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (p ^ f))
    {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {z : ModGL Tag.E6 K}
    (hz : z ∈ twistedE6RootGroup K σ) (hz3 : z ^ 3 = 1)
    (hdim : Module.finrank K
      (LinearMap.ker ((z : Module.End K (RootModule Tag.E6 K)) - 1)) = 24) :
    ∃ g ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
          g * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) e6W0Four ∧
        baseChangeGL (algebraMap K (AlgebraicClosure K)) z =
          g * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (rootDiagUnit Tag.E6 (e6LineChar ω)) * g⁻¹ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K p :=
    charP_of_card_eq_prime_pow (f := f * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  obtain rfl : Fr = iterateFrobenius (AlgebraicClosure K) p f :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_def]
  obtain ⟨g0, hg0C, hF0⟩ : ∃ g0 : ModGL Tag.E6 (AlgebraicClosure K),
      g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K) ∧
        twistHom TwistTag.E6 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) p f)
          g0 = g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) e6W0Four :=
    CFSG.RankThree.PartOne.KE.lang_conjugator_twisted_gen K (ℓ := p) hf (AlgebraicClosure K)
      (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) e6W0Four)
      (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) (AlgebraicClosure K) e6W0Four)
  have hzC : z ∈ adjointGroup Tag.E6 K :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hz)).1
  obtain ⟨s, hs⟩ : ∃ s, s = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) z * g0 :=
    ⟨_, rfl⟩
  have hsC : s ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hs]
    exact mul_mem (mul_mem (inv_mem hg0C)
      (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hzC)) hg0C
  have hs3 : s ^ 3 = 1 := by
    rw [show s = MulAut.conj g0⁻¹ (baseChangeGL (algebraMap K (AlgebraicClosure K)) z) by
      rw [hs, MulAut.conj_apply, inv_inv], ← map_pow, ← map_pow, hz3, map_one, map_one]
  have hdimL : Module.finrank (AlgebraicClosure K) (LinearMap.ker
      ((baseChangeGL (algebraMap K (AlgebraicClosure K)) z : Module.End (AlgebraicClosure K)
        (RootModule Tag.E6 (AlgebraicClosure K))) - 1)) = 24 := by
    have h := finrank_ker_baseChangeEnd (L := AlgebraicClosure K)
      ((z : Module.End K (RootModule Tag.E6 K)) - 1)
    rw [baseChangeEnd_sub_aux, baseChangeEnd_one_aux] at h
    rw [coe_baseChangeGL, h, hdim]
  have hsdim : Module.finrank (AlgebraicClosure K) (LinearMap.ker
      ((s : Module.End (AlgebraicClosure K) (RootModule Tag.E6 (AlgebraicClosure K))) - 1)) =
        24 := by
    have h := finrank_ker_conj_sub_one g0⁻¹ (baseChangeGL (algebraMap K (AlgebraicClosure K)) z)
    rw [inv_inv, ← hs] at h
    rw [h, hdimL]
  obtain ⟨y, hyC, hsy⟩ := exists_conj_e6Line_bar hω3 hω1 hsC hs3 hsdim
  have hzy : baseChangeGL (algebraMap K (AlgebraicClosure K)) z =
      g0 * (y * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (rootDiagUnit Tag.E6 (e6LineChar ω)) * y⁻¹) * g0⁻¹ := by
    rw [← hsy, hs]
    group
  have hc := tw_cocycle_mem_toralRootGroup_threeA2 hp hf hK σ hσ hq
    (iterateFrobenius (AlgebraicClosure K) p f) hFr hg0C hF0 hω3 hz hyC hzy
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ,
      a₀ = fun i => Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (e6LineChar ω i) :=
    ⟨_, rfl⟩
  rw [← ha₀] at hc
  have hd : baseChangeGL (algebraMap K (AlgebraicClosure K))
      (rootDiagUnit Tag.E6 (e6LineChar ω)) = rootDiagUnit Tag.E6 a₀ := by
    rw [baseChangeGL_rootDiagUnit, ha₀]
  obtain ⟨w, hwM, hwc⟩ := toralRootGroup_lang_twq p f hf a₀ _ hc
  have hwC := mem_toralCentralizer.1 (toralRootGroup_le a₀ hwM)
  have hwd : w⁻¹ * rootDiagUnit Tag.E6 a₀ * w = rootDiagUnit Tag.E6 a₀ := by
    calc w⁻¹ * rootDiagUnit Tag.E6 a₀ * w
        = w⁻¹ * (rootDiagUnit Tag.E6 a₀ * w * (rootDiagUnit Tag.E6 a₀)⁻¹) *
          rootDiagUnit Tag.E6 a₀ := by group
      _ = rootDiagUnit Tag.E6 a₀ := by rw [hwC.2]; group
  obtain ⟨u, hu⟩ : ∃ u, u = y * w⁻¹ := ⟨_, rfl⟩
  have hFw : twE6F0 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) p f) w =
      w * (y⁻¹ * twE6F0 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) p f) y) := by
    rw [← hwc]
    group
  have hFu : twE6F0 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) p f) u = u := by
    rw [hu, map_mul, map_inv, hFw]
    group
  have huC : u ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hu]
    exact mul_mem hyC (inv_mem hwC.1)
  have hud : u * rootDiagUnit Tag.E6 a₀ * u⁻¹ = y * rootDiagUnit Tag.E6 a₀ * y⁻¹ := by
    rw [hu]
    calc y * w⁻¹ * rootDiagUnit Tag.E6 a₀ * (y * w⁻¹)⁻¹
        = y * (w⁻¹ * rootDiagUnit Tag.E6 a₀ * w) * y⁻¹ := by group
      _ = y * rootDiagUnit Tag.E6 a₀ * y⁻¹ := by rw [hwd]
  refine ⟨g0 * u, mul_mem hg0C huC,
    twistHom_mul_of_twLang hF0 (twistHom_of_twFrob_fixed hFu), ?_⟩
  rw [hzy, hd, ← hud]
  group

theorem tw_exists_conj_threeA2 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2) {ω : Kˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) {x y : ModGL TwistTag.E6.tag K} (hx : x ∈ twistedE6RootGroup K σ)
    (hy : y ∈ twistedE6RootGroup K σ) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hxd : Module.finrank K
      (LinearMap.ker ((x : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24)
    (hyd : Module.finrank K
      (LinearMap.ker ((y : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24) :
    ∃ g ∈ twistedE6RootGroup K σ, g * x * g⁻¹ = y := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K p :=
    charP_of_card_eq_prime_pow (f := f * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  obtain ⟨Fr, hFr⟩ : ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, ∀ c, Fr c = c ^ (p ^ f) :=
    ⟨iterateFrobenius _ p f, fun c => by rw [iterateFrobenius_def]⟩
  obtain ⟨gx, hgxC, hFx, hgx⟩ : ∃ g : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
          g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 ∧
        baseChangeGL (algebraMap K (AlgebraicClosure K)) x =
          g * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (rootDiagUnit TwistTag.E6.tag (e6LineChar ω)) * g⁻¹ :=
    tw_exists_lang_datum_threeA2 hp hf hK σ hσ hq Fr hFr hω3 hω1 hx hx3 hxd
  obtain ⟨gy, hgyC, hFy, hgy⟩ : ∃ g : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
          g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 ∧
        baseChangeGL (algebraMap K (AlgebraicClosure K)) y =
          g * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (rootDiagUnit TwistTag.E6.tag (e6LineChar ω)) * g⁻¹ :=
    tw_exists_lang_datum_threeA2 hp hf hK σ hσ hq Fr hFr hω3 hω1 hy hy3 hyd
  have hkR : gy * gx⁻¹ ∈ CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr := by
    refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).2
      ⟨mul_mem hgyC (inv_mem hgxC), ?_⟩
    rw [map_mul, map_inv, hFy, hFx]
    group
  have hkx : gy * gx⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * (gy * gx⁻¹)⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) y := by
    rw [hgx, hgy]
    group
  obtain ⟨t, htT, hFt, htC⟩ : ∃ t : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr t =
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)⁻¹ * t *
            canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 ∧
        gx * t * gx⁻¹ ∉ (twistedE6RootGroup K σ).map
          (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    tw_exists_class_element hp hf hK σ hσ hq Fr hFr gx hgxC isReduced_e6W0FourWord hFx
  have hc0R : gx * t * gx⁻¹ ∈
      CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr := by
    refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).2
      ⟨mul_mem (mul_mem hgxC (CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup' htT))
        (inv_mem hgxC), ?_⟩
    rw [map_mul, map_mul, map_inv, hFx, hFt]
    group
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT
  have htd : t * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (rootDiagUnit TwistTag.E6.tag (e6LineChar ω)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        (rootDiagUnit TwistTag.E6.tag (e6LineChar ω)) * t := by
    rw [hb, baseChangeGL_rootDiagUnit (τ := TwistTag.E6.tag) _ (e6LineChar ω),
      ← CFSG.LieType.Chevalley.rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
      mul_comm]
  generalize baseChangeGL (algebraMap K (AlgebraicClosure K))
    (rootDiagUnit TwistTag.E6.tag (e6LineChar ω)) = d at hgx htd
  have hcx : Commute (gx * t * gx⁻¹) (baseChangeGL (algebraMap K (AlgebraicClosure K)) x) := by
    rw [hgx]
    show gx * t * gx⁻¹ * (gx * d * gx⁻¹) = gx * d * gx⁻¹ * (gx * t * gx⁻¹)
    calc gx * t * gx⁻¹ * (gx * d * gx⁻¹) = gx * (t * d) * gx⁻¹ := by group
      _ = gx * (d * t) * gx⁻¹ := by rw [htd]
      _ = gx * d * gx⁻¹ * (gx * t * gx⁻¹) := by group
  obtain ⟨j, hj⟩ := tw_class_correction hp hf hK σ hσ hq Fr hFr hc0R (inv_mem hkR) htC
  have hcj := hcx.zpow_left j
  generalize (gx * t * gx⁻¹) ^ j = P at hj hcj
  obtain ⟨g, hgC, hg⟩ := Subgroup.mem_map.1 (inv_mem hj)
  refine ⟨g, hgC, ?_⟩
  apply baseChangeGL_injective (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K))
  rw [map_mul, map_mul, map_inv, hg, ← hkx]
  generalize baseChangeGL (algebraMap K (AlgebraicClosure K)) x = X at hcj ⊢
  calc (P * (gy * gx⁻¹)⁻¹)⁻¹ * X * ((P * (gy * gx⁻¹)⁻¹)⁻¹)⁻¹
      = gy * gx⁻¹ * (P⁻¹ * (X * P)) * (gy * gx⁻¹)⁻¹ := by group
    _ = gy * gx⁻¹ * (P⁻¹ * (P * X)) * (gy * gx⁻¹)⁻¹ := by rw [← hcj.eq]
    _ = gy * gx⁻¹ * X * (gy * gx⁻¹)⁻¹ := by group

theorem twE6ThreeA2Conj_holds : TwE6ThreeA2ConjStmt := by
  intro K _ _ σ q _ hσ hKq h3 _ x hx y hy hx3 hy3 hxd hyd
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpn, hcard⟩ := FiniteField.card K (ringChar K)
  obtain ⟨p, hp⟩ : ∃ p, p = ringChar K := ⟨_, rfl⟩
  rw [← hp] at hpn hcard
  have hq2 : q ∣ p ^ (n : ℕ) := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hKq]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hpn).1 hq2
  have hq3 : (p ^ m) % 3 = 2 := by omega
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, pow_zero] at h3
      omega
    · exact h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3K : 3 ∣ Nat.card Kˣ := by
    have h1 : (p ^ m) ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod, hq3]
    rw [Nat.card_units, hKq]
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3K
  have hω3 : ω ^ 3 = 1 := by
    rw [← hω]
    exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    omega
  exact tw_exists_conj_threeA2 hpn hm1 hKq σ hσ hq3 hω3 hω1 hx hy hx3 hy3 hxd hyd

end Conj

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
