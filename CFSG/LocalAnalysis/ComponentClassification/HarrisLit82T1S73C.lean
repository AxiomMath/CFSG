module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73SL3
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73I
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RF
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RC

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.HighestRoot
open scoped MatrixGroups

theorem normal_subgroupOf_of_le {G : Type*} [Group G] {A B C : Subgroup G}
    (hA : (A.subgroupOf C).Normal) (hAC : A ≤ C) (hBC : B ≤ C) : (A.subgroupOf B).Normal := by
  rw [normal_subgroupOf_iff hAC] at hA
  exact ⟨fun n hn g => hA n g hn (hBC g.2)⟩

theorem sl23_map_neg_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {G : Type*}
    [Group G] (ρ : SL(2, K) →* G) (hρ : Function.Injective ρ) :
    ((MonoidHom.ofInjective hρ).symm.trans (slEquivSL23 hK))
      ⟨ρ (-1), MonoidHom.mem_range.mpr ⟨-1, rfl⟩⟩ = -1 := by
  have h1 : (MonoidHom.ofInjective hρ).symm ⟨ρ (-1), MonoidHom.mem_range.mpr ⟨-1, rfl⟩⟩ = -1 := by
    apply (MonoidHom.ofInjective hρ).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hodd : Odd (Nat.card (ZMod 3)) := by rw [card_zmod_three]; decide
  have hoddK : Odd (Nat.card K) := by rw [hK]; decide
  rw [MulEquiv.trans_apply, h1, ← CFSG.ClassicalInvolution.sl2_orderOf_eq_two_iff hodd,
    MulEquiv.orderOf_eq]
  exact CFSG.ClassicalInvolution.sl2_orderOf_neg_one hoddK

section NonCentral

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
include hK

theorem exists_mem_inf_of_noncentral {G : Type*} [Group G] {C J : Subgroup G}
    (ρ : SL(2, K) →* G) (hρ : Function.Injective ρ) (hRC : ρ.range ≤ C)
    (hRn : (ρ.range.subgroupOf C).Normal) (hJC : J ≤ C) (hJsn : (J.subgroupOf C).IsSubnormal)
    {x a y : G} (hxJ : x ∈ J) (hx3 : x ^ 3 = 1) (ha : a ∈ ρ.range)
    (hyc : ∀ r ∈ ρ.range, r * y = y * r) (hxa : x = a * y)
    (ha3 : a ^ 3 = 1 ∨ a ^ 3 = ρ (-1)) (ha1 : a ≠ 1) (ha2 : a ≠ ρ (-1)) :
    ∃ k ∈ J ⊓ ρ.range, k ^ 4 = 1 ∧ k ^ 2 ≠ 1 := by
  set φ := (MonoidHom.ofInjective hρ).symm.trans (slEquivSL23 hK) with hφ
  have hφneg := sl23_map_neg_one hK ρ hρ
  have hφ1 : ∀ {u v : ↥ρ.range}, φ u = φ v → u = v := fun h => φ.injective h
  set a' : ↥ρ.range := ⟨a, ha⟩ with ha'
  have hφa3 : φ a' ^ 3 = 1 ∨ φ a' ^ 3 = -1 := by
    rcases ha3 with h | h
    · left
      rw [← map_pow, show a' ^ 3 = 1 from Subtype.ext (by simp [ha', h]), map_one]
    · right
      rw [← map_pow, ← hφneg]
      congr 1
      exact Subtype.ext (by simp [ha', h])
  have hφa1 : φ a' ≠ 1 := fun h => ha1 (congrArg Subtype.val (hφ1 (h.trans (map_one φ).symm)))
  have hφa2 : φ a' ≠ -1 := fun h => ha2 (congrArg Subtype.val (hφ1 (h.trans hφneg.symm)))
  obtain ⟨g₀, hg₀4, hk₀⟩ := sl23_exists_pow_four (φ a') hφa3 hφa1 hφa2
  set g' : ↥ρ.range := φ.symm g₀ with hg'
  set g : G := (↑g' : G) with hgdef
  have hgR : g ∈ ρ.range := g'.2
  have hg4 : g ^ 4 = 1 := by
    have h : g' ^ 4 = 1 := φ.injective (by rw [map_pow, hg', MulEquiv.apply_symm_apply, hg₀4,
      map_one])
    rw [hgdef, ← SubgroupClass.coe_pow, h, OneMemClass.coe_one]
  set N : Subgroup G :=
    { carrier := {u | u ∈ ρ.range ∧ u ^ 4 = 1}
      mul_mem' := by
        rintro u v ⟨huR, hu⟩ ⟨hvR, hv⟩
        refine ⟨mul_mem huR hvR, ?_⟩
        set u' : ↥ρ.range := ⟨u, huR⟩
        set v' : ↥ρ.range := ⟨v, hvR⟩
        have hu' : φ u' ^ 4 = 1 := by
          rw [← map_pow, show u' ^ 4 = 1 from Subtype.ext (by simp [u', hu]), map_one]
        have hv' : φ v' ^ 4 = 1 := by
          rw [← map_pow, show v' ^ 4 = 1 from Subtype.ext (by simp [v', hv]), map_one]
        have h := sl23_mul_pow_four _ _ hu' hv'
        rw [← map_mul, ← map_pow, ← map_one φ] at h
        have h' := congrArg Subtype.val (φ.injective h)
        simpa [u', v'] using h'
      one_mem' := ⟨one_mem _, one_pow 4⟩
      inv_mem' := by
        rintro u ⟨huR, hu⟩
        exact ⟨inv_mem huR, by rw [inv_pow, hu, inv_one]⟩ } with hN
  have hNR : N ≤ ρ.range := fun u hu => hu.1
  have hNn : (N.subgroupOf C).Normal := by
    rw [normal_subgroupOf_iff (hNR.trans hRC)]
    intro u c hu hc
    rw [normal_subgroupOf_iff hRC] at hRn
    exact ⟨hRn u c hu.1 hc, by rw [conj_pow, hu.2, mul_one, mul_inv_cancel]⟩
  have hgN : g ∈ N := ⟨hgR, hg4⟩
  have hxC : x ∈ C := hJC hxJ
  have hgC : g ∈ C := hRC hgR
  have hconj : g * x * g⁻¹ ∈ J := by
    have h := conj_mem_of_isSubnormal (p := 2) (q := 3) (by norm_num) hNn
      (fun n hn => ⟨2, by
        have h4 : (n : G) ^ 4 = 1 := (Subgroup.mem_subgroupOf.mp hn).2
        exact Subtype.ext (by simpa using h4)⟩)
      hJsn (x := ⟨x, hxC⟩) hxJ (b := 1) (Subtype.ext (by simpa using hx3))
      (g := ⟨g, hgC⟩) hgN
    exact h
  set k := a⁻¹ * g * a * g⁻¹ with hkdef
  have hkR : k ∈ ρ.range := mul_mem (mul_mem (mul_mem (inv_mem ha) hgR) ha) (inv_mem hgR)
  have hgy : g * y = y * g := hyc g hgR
  have hky : k * y = y * k := hyc k hkR
  have hk : k = x⁻¹ * (g * x * g⁻¹) := by
    have hgy' : y * g⁻¹ = g⁻¹ * y := by
      calc y * g⁻¹ = g⁻¹ * (g * y) * g⁻¹ := by group
        _ = g⁻¹ * (y * g) * g⁻¹ := by rw [hgy]
        _ = g⁻¹ * y := by group
    rw [hxa]
    calc k = y⁻¹ * (y * k) := by group
      _ = y⁻¹ * (k * y) := by rw [hky]
      _ = y⁻¹ * (a⁻¹ * g * a * g⁻¹ * y) := by rw [hkdef]
      _ = y⁻¹ * (a⁻¹ * g * a * (g⁻¹ * y)) := by group
      _ = y⁻¹ * (a⁻¹ * g * a * (y * g⁻¹)) := by rw [hgy']
      _ = (a * y)⁻¹ * (g * (a * y) * g⁻¹) := by group
  have hkJ : k ∈ J := by
    rw [hk]
    exact mul_mem (inv_mem hxJ) hconj
  have hkN : k ∈ N := by
    have h1 : a⁻¹ * g * a ∈ N := by
      have h := (normal_subgroupOf_iff (hNR.trans hRC)).mp hNn g a⁻¹ hgN (inv_mem (hRC ha))
      rwa [inv_inv] at h
    exact mul_mem h1 (inv_mem hgN)
  refine ⟨k, ⟨hkJ, hkR⟩, hkN.2, fun hk2 => hk₀ ?_⟩
  have ha6 : φ a' ^ 6 = 1 := by
    rcases hφa3 with h | h
    · rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, h, one_pow]
    · rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, h]
      simp
  have hainv : (φ a')⁻¹ = φ a' ^ 5 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact ha6
  have hginv : g₀⁻¹ = g₀ ^ 3 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hg₀4
  have hφk : φ ⟨k, hkR⟩ = φ a' ^ 5 * g₀ * φ a' * g₀ ^ 3 := by
    have e : (⟨k, hkR⟩ : ↥ρ.range) = a'⁻¹ * g' * a' * g'⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hg', MulEquiv.apply_symm_apply, hainv,
      hginv]
  rw [← hφk, ← map_pow, show (⟨k, hkR⟩ : ↥ρ.range) ^ 2 = 1 from Subtype.ext (by simp [hk2]),
    map_one]

end NonCentral

section Card

variable {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  (hK : Nat.card K = p ^ f)
include hp hp2 hK

theorem spinJ_inf_eq_one_odd {y : spinGroup (quadOdd 3 K)} :
    (y ∈ spinJ₁ K → y ∈ spinJ₂ K → y = 1) ∧ (y ∈ spinJ₁ K → y ∈ spinJ₃ K → y = 1) ∧
      (y ∈ spinJ₂ K → y ∈ spinJ₃ K → y = 1) := by
  obtain ⟨hzz, hz1, hzc, htt, ht1, htc, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  have hzt1 : spinZ K * tSeven K ≠ 1 := fun h => htc (by
    rw [(eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hzz)]; exact hzc)
  refine ⟨fun h1 h2 => ?_, fun h1 h3 => ?_, fun h2 h3 => ?_⟩
  · rcases (mem_ker_spinMulOdd_iff hp hp2 hK ((⟨y, h1⟩, ⟨y⁻¹, inv_mem h2⟩), 1)).mp (by
      rw [MonoidHom.mem_ker, spinMulOdd_apply]
      show y * y⁻¹ * 1 = 1
      rw [mul_inv_cancel, mul_one]) with hw | hw
    · exact congrArg (fun v => (v.1.1 : spinGroup (quadOdd 3 K))) hw
    · exact absurd (congrArg (fun v => (v.2 : spinGroup (quadOdd 3 K))) hw).symm hzt1
  · rcases (mem_ker_spinMulOdd_iff hp hp2 hK ((⟨y, h1⟩, 1), ⟨y⁻¹, inv_mem h3⟩)).mp (by
      rw [MonoidHom.mem_ker, spinMulOdd_apply]
      show y * 1 * y⁻¹ = 1
      rw [mul_one, mul_inv_cancel]) with hw | hw
    · exact congrArg (fun v => (v.1.1 : spinGroup (quadOdd 3 K))) hw
    · exact absurd (congrArg (fun v => (v.1.2 : spinGroup (quadOdd 3 K))) hw).symm ht1
  · rcases (mem_ker_spinMulOdd_iff hp hp2 hK ((1, ⟨y, h2⟩), ⟨y⁻¹, inv_mem h3⟩)).mp (by
      rw [MonoidHom.mem_ker, spinMulOdd_apply]
      show 1 * y * y⁻¹ = 1
      rw [one_mul, mul_inv_cancel]) with hw | hw
    · exact congrArg (fun v => (v.1.2 : spinGroup (quadOdd 3 K))) hw
    · exact absurd (congrArg (fun v => (v.1.1 : spinGroup (quadOdd 3 K))) hw).symm hz1

end Card

section Three

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
include hK

theorem isSolvable_spinE_three : Group.IsSolvable ↥(spinE K) := by
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hodd := odd_card_spin Nat.prime_three (by norm_num) hK'
  have s1 : Group.IsSolvable ↥(spinJ₁ K) :=
    isSolvable_of_mulEquiv hK (MonoidHom.ofInjective injective_shortSeven).symm
  have s2 : Group.IsSolvable ↥(spinJ₂ K) :=
    isSolvable_of_mulEquiv hK
      (MonoidHom.ofInjective (longSL2_injective _ fin3_zero_ne_one true true)).symm
  have s3 : Group.IsSolvable ↥(spinJ₃ K) :=
    isSolvable_of_mulEquiv hK
      (MonoidHom.ofInjective (longSL2_injective _ fin3_zero_ne_one true false)).symm
  rw [← range_spinMulOdd hodd]
  exact Group.isSolvable_of_surjective (spinMulOdd hodd).rangeRestrict_surjective

theorem not_isTwoComponentIn_three (J : Subgroup (spinGroup (quadOdd 3 K))) :
    ¬ IsTwoComponentIn J (centralizer {tSeven K}) := by
  intro hJ
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have := finite_spinSeven (two_ne_zero_spin Nat.prime_three hp2 hK')
  have hO := pPrimeCore_centralizer_tSeven_odd Nat.prime_three hp2 hK'
  have hJq := isQuasisimple_of_isTwoComponentIn hJ hO
  have hJperf : Group.IsPerfect ↥J := hJ.2.2.1
  have hJnt : Nontrivial ↥J := LocalCores.isQuasisimple_nontrivial hJq
  have hJE : J ≤ spinE K := le_of_isPerfect_of_index_dvd
    (normal_spinE_odd Nat.prime_three hp2 hK') (index_spinE_dvd_odd Nat.prime_three hp2 hK')
    hJ.1 hJperf
  have := isSolvable_spinE_three hK
  have hJs : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hJE)
  exact Group.IsPerfect.not_isSolvable ↥J hJs

theorem isSolvableTwoComponentIn_spinJ_three {J : Subgroup (spinGroup (quadOdd 3 K))}
    (hJ : J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) :
    IsSolvableTwoComponentIn J (centralizer {tSeven K}) ∧
      (J.subgroupOf (centralizer {tSeven K})).Normal := by
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) Nat.prime_three hp2 hK'
  obtain ⟨n1, n2, n3⟩ := normal_spinJ_odd (K := K) Nat.prime_three hp2 hK'
  obtain ⟨o1, o2, o3⟩ := pPrimeCore_spinJ_odd (K := K) Nat.prime_three hp2 hK'
  have hO := pPrimeCore_centralizer_tSeven_odd Nat.prime_three hp2 hK'
  have key : ∀ (ρ : SL(2, K) →* spinGroup (quadOdd 3 K)) (hρ : Function.Injective ρ),
      ρ.range ≤ centralizer {tSeven K} →
      (ρ.range.subgroupOf (centralizer {tSeven K})).Normal → pPrimeCore 2 ↥ρ.range = ⊥ →
      IsSolvableTwoComponentIn ρ.range (centralizer {tSeven K}) ∧
        (ρ.range.subgroupOf (centralizer {tSeven K})).Normal := by
    intro ρ hρ hle hn ho
    refine ⟨⟨hle, hn.isSubnormal, ?_, Or.inr ⟨?_⟩⟩, hn⟩
    · rw [ho, hO, Subgroup.map_bot, Subgroup.map_bot]
    · exact ((QuotientGroup.quotientMulEquivOfEq ho).trans QuotientGroup.quotientBot).trans
        ((MonoidHom.ofInjective hρ).symm.trans (slEquivSL23 hK))
  rcases hJ with rfl | rfl | rfl
  · exact key _ injective_shortSeven l1 n1 o1
  · exact key _ (longSL2_injective _ fin3_zero_ne_one true true) l2 n2 o2
  · exact key _ (longSL2_injective _ fin3_zero_ne_one true false) l3 n3 o3


theorem eq_spinJ_of_isSolvableTwoComponentIn_three {J : Subgroup (spinGroup (quadOdd 3 K))}
    (hJ : IsSolvableTwoComponentIn J (centralizer {tSeven K})) :
    J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K := by
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK, pow_one]
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_card_spin Nat.prime_three hp2 hK'
  have := finite_spinSeven (two_ne_zero_spin Nat.prime_three hp2 hK')
  have hQ : quadOdd 3 K ≠ 0 := (nondegenerate_quadOdd 3 K).ne_zero
  obtain ⟨hzz, hz1, hzc, htt, ht1, htc, hzJ₁, htJ₂, hztJ₃, h3eq⟩ :=
    spinZ_facts Nat.prime_three hp2 hK'
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  have htz : tSeven K * spinZ K = spinZ K * tSeven K := (hzcomm _).symm
  have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
    rw [mul_assoc, ← mul_assoc (tSeven K), htz, mul_assoc, htt, mul_one, hzz]
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) Nat.prime_three hp2 hK'
  obtain ⟨n1, n2, n3⟩ := normal_spinJ_odd (K := K) Nat.prime_three hp2 hK'
  have hinf := fun y : spinGroup (quadOdd 3 K) =>
    spinJ_inf_eq_one_odd (K := K) Nat.prime_three hp2 hK' (y := y)
  obtain ⟨hJC, hJsn, hJO, hJiso⟩ := hJ
  have hO := pPrimeCore_centralizer_tSeven_odd Nat.prime_three hp2 hK'
  have hJO' : pPrimeCore 2 ↥J = ⊥ := by
    rw [hO, Subgroup.map_bot, map_eq_bot_iff_of_injective _ (subtype_injective _)] at hJO
    exact hJO
  set eO : ↥J ≃* ↥J ⧸ pPrimeCore 2 ↥J :=
    ((QuotientGroup.quotientMulEquivOfEq hJO').trans QuotientGroup.quotientBot).symm with heO
  have hJiso' : Nonempty (↥J ≃* PSL(2, ZMod 3)) ∨ Nonempty (↥J ≃* SL(2, ZMod 3)) := by
    rcases hJiso with h | h
    · obtain ⟨e⟩ := h
      exact Or.inl ⟨eO.trans e⟩
    · obtain ⟨e⟩ := h
      exact Or.inr ⟨eO.trans e⟩
  have hidx := index_spinE_eq_two_odd (K := K) Nat.prime_three hp2 hK'
  have hJE : J ≤ spinE K := by
    refine (le_closure_mul_self_of_sl23 hJiso').trans ((closure_le _).mpr ?_)
    rintro _ ⟨y, hy, rfl⟩
    exact mul_self_mem_of_index_two hidx ⟨y, hJC hy⟩
  obtain ⟨x₀, hx₀3, hx₀1, hx₀2⟩ := sl23_exists_pow_three
  obtain ⟨x, hxJ, hx3, hx1⟩ : ∃ x ∈ J, x ^ 3 = 1 ∧ x ≠ 1 := by
    rcases hJiso' with h | h
    · obtain ⟨e⟩ := h
      refine ⟨(e.symm (QuotientGroup.mk x₀) : spinGroup (quadOdd 3 K)), (e.symm _).2, ?_, ?_⟩
      · rw [← SubgroupClass.coe_pow, ← map_pow, ← QuotientGroup.mk_pow, hx₀3,
          QuotientGroup.mk_one, map_one, OneMemClass.coe_one]
      · intro h1
        have h2 : (QuotientGroup.mk x₀ : PSL(2, ZMod 3)) = 1 :=
          e.symm.injective (by rw [map_one]; exact Subtype.ext h1)
        rw [QuotientGroup.eq_one_iff, mem_center_SL23_iff] at h2
        rcases h2 with h2 | h2
        · exact hx₀1 h2
        · exact hx₀2 h2
    · obtain ⟨e⟩ := h
      refine ⟨(e.symm x₀ : spinGroup (quadOdd 3 K)), (e.symm _).2, ?_, ?_⟩
      · rw [← SubgroupClass.coe_pow, ← map_pow, hx₀3, map_one, OneMemClass.coe_one]
      · intro h1
        exact hx₀1 (e.symm.injective (by rw [map_one]; exact Subtype.ext h1))
  have hxE : x ∈ spinE K := hJE hxJ
  rw [← range_spinMulOdd hodd] at hxE
  obtain ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨c, hc⟩⟩, hw⟩ := hxE
  rw [spinMulOdd_apply] at hw
  change a * b * c = x at hw
  have hab : a * b = b * a := commute_spinJ₁_spinJ₂ ha hb
  have hac : a * c = c * a := commute_spinJ₁_spinJ₃ ha hc
  have hbc : b * c = c * b := commute_spinJ₂_spinJ₃_odd hodd hb hc
  have hcube : ((⟨a, ha⟩, ⟨b, hb⟩), ⟨c, hc⟩) ^ 3 ∈ (spinMulOdd hodd).ker := by
    rw [MonoidHom.mem_ker, map_pow, spinMulOdd_apply]
    change (a * b * c) ^ 3 = 1
    rw [hw, hx3]
  have hcub : (a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c ^ 3 = 1) ∨
      (a ^ 3 = spinZ K ∧ b ^ 3 = tSeven K ∧ c ^ 3 = spinZ K * tSeven K) := by
    rcases (mem_ker_spinMulOdd_iff Nat.prime_three hp2 hK' _).mp hcube with h | h
    · left
      refine ⟨?_, ?_, ?_⟩
      · simpa using congrArg (fun v => ((v.1.1 : spinJ₁ K) : spinGroup (quadOdd 3 K))) h
      · simpa using congrArg (fun v => ((v.1.2 : spinJ₂ K) : spinGroup (quadOdd 3 K))) h
      · simpa using congrArg (fun v => ((v.2 : spinJ₃ K) : spinGroup (quadOdd 3 K))) h
    · right
      refine ⟨?_, ?_, ?_⟩
      · simpa using congrArg (fun v => ((v.1.1 : spinJ₁ K) : spinGroup (quadOdd 3 K))) h
      · simpa using congrArg (fun v => ((v.1.2 : spinJ₂ K) : spinGroup (quadOdd 3 K))) h
      · simpa using congrArg (fun v => ((v.2 : spinJ₃ K) : spinGroup (quadOdd 3 K))) h
  have ha3 : a ^ 3 = 1 ∨ a ^ 3 = spinZ K := hcub.imp (fun h => h.1) (fun h => h.1)
  have hb3 : b ^ 3 = 1 ∨ b ^ 3 = tSeven K := hcub.imp (fun h => h.2.1) (fun h => h.2.1)
  have hc3 : c ^ 3 = 1 ∨ c ^ 3 = spinZ K * tSeven K :=
    hcub.imp (fun h => h.2.2) (fun h => h.2.2)
  have hne1 : spinZ K ≠ 1 := hz1
  have hzt1 : spinZ K * tSeven K ≠ 1 := fun h => htc (by
    rw [(eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hzz)]; exact hzc)
  have hk1 : ¬ (a = 1 ∨ a = spinZ K) → ∃ k ∈ J ⊓ spinJ₁ K, k ^ 4 = 1 ∧ k ^ 2 ≠ 1 := by
    intro hnc
    have hz : shortSeven K (-1) = spinZ K := shortSeven_neg_one hQ
    refine exists_mem_inf_of_noncentral hK (shortSeven K) injective_shortSeven l1 n1 hJC hJsn
      hxJ hx3 ha (y := b * c) (fun r hr => ?_) ?_ (hz ▸ ha3)
      (fun h => hnc (Or.inl h)) (fun h => hnc (Or.inr (h.trans hz)))
    · rw [← mul_assoc, commute_spinJ₁_spinJ₂ hr hb, mul_assoc, commute_spinJ₁_spinJ₃ hr hc,
        ← mul_assoc]
    · rw [← hw, mul_assoc]
  have hk2 : ¬ (b = 1 ∨ b = tSeven K) → ∃ k ∈ J ⊓ spinJ₂ K, k ^ 4 = 1 ∧ k ^ 2 ≠ 1 := by
    intro hnc
    refine exists_mem_inf_of_noncentral hK _ (longSL2_injective _ fin3_zero_ne_one true true) l2
      n2 hJC hJsn hxJ hx3 hb (y := a * c) (fun r hr => ?_) ?_ hb3
      (fun h => hnc (Or.inl h)) (fun h => hnc (Or.inr h))
    · rw [← mul_assoc, ← commute_spinJ₁_spinJ₂ ha hr, mul_assoc,
        commute_spinJ₂_spinJ₃_odd hodd hr hc, ← mul_assoc]
    · rw [← hw, hab, mul_assoc]
  have hk3 : ¬ (c = 1 ∨ c = spinZ K * tSeven K) →
      ∃ k ∈ J ⊓ spinJ₃ K, k ^ 4 = 1 ∧ k ^ 2 ≠ 1 := by
    intro hnc
    refine exists_mem_inf_of_noncentral hK _ (longSL2_injective _ fin3_zero_ne_one true false)
      l3 n3 hJC hJsn hxJ hx3 hc (y := a * b) (fun r hr => ?_) ?_
      (h3eq ▸ hc3) (fun h => hnc (Or.inl h)) (fun h => hnc (Or.inr (h.trans h3eq)))
    · rw [← mul_assoc, ← commute_spinJ₁_spinJ₃ ha hr, mul_assoc,
        ← commute_spinJ₂_spinJ₃_odd hodd hb hr, ← mul_assoc]
    · rw [← hw, mul_assoc, hbc, ← mul_assoc, hac, mul_assoc]
  have hnot : ¬ ((a = 1 ∨ a = spinZ K) ∧ (b = 1 ∨ b = tSeven K) ∧
      (c = 1 ∨ c = spinZ K * tSeven K)) := by
    rintro ⟨h1, h2, h3⟩
    have ha2 : a * a = 1 := by rcases h1 with rfl | rfl <;> simp [hzz]
    have hb2 : b * b = 1 := by rcases h2 with rfl | rfl <;> simp [htt]
    have hc2 : c * c = 1 := by rcases h3 with rfl | rfl <;> simp [hztzt]
    have hx2 : x * x = 1 := by
      rw [← hw]
      calc a * b * c * (a * b * c) = a * a * (b * b) * (c * c) := by
            rw [mul_mul_mul_mul_mul_of_commute hab hac hbc]
        _ = 1 := by rw [ha2, hb2, hc2, one_mul, one_mul]
    apply hx1
    calc x = x ^ 3 * (x * x)⁻¹ := by group
      _ = 1 := by rw [hx3, hx2, inv_one, one_mul]
  rcases hJiso' with h | h
  ·
    exfalso
    obtain ⟨e⟩ := h
    have hno : ∀ k ∈ J, k ^ 4 = 1 → k ^ 2 = 1 := fun k hk h4 => by
      have h := psl23_sq_eq_one e (y := ⟨k, hk⟩) (Subtype.ext (by simpa using h4))
      simpa using congrArg Subtype.val h
    by_cases h1 : a = 1 ∨ a = spinZ K
    · by_cases h2 : b = 1 ∨ b = tSeven K
      · by_cases h3 : c = 1 ∨ c = spinZ K * tSeven K
        · exact hnot ⟨h1, h2, h3⟩
        · obtain ⟨k, hk, hk4, hk2'⟩ := hk3 h3
          exact hk2' (hno k hk.1 hk4)
      · obtain ⟨k, hk, hk4, hk2'⟩ := hk2 h2
        exact hk2' (hno k hk.1 hk4)
    · obtain ⟨k, hk, hk4, hk2'⟩ := hk1 h1
      exact hk2' (hno k hk.1 hk4)
  ·
    obtain ⟨e⟩ := h
    have hodd3 : Odd (Nat.card (ZMod 3)) := by rw [card_zmod_three]; decide
    set ι : ↥J := e.symm (-1) with hι
    have hι2 : orderOf ι = 2 :=
      (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd3 e ι).mpr rfl
    have hι1 : (ι : spinGroup (quadOdd 3 K)) ≠ 1 := fun h1 => by
      have h1' : ι = 1 := Subtype.ext h1
      rw [h1', orderOf_one] at hι2
      exact absurd hι2 (by norm_num)
    have hsq : ∀ k ∈ J, k ^ 4 = 1 → k ^ 2 ≠ 1 → k ^ 2 = ι := by
      intro k hk hk4 hk2'
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 : orderOf (⟨k ^ 2, pow_mem hk 2⟩ : ↥J) = 2 :=
        orderOf_eq_prime (Subtype.ext (show (k ^ 2) ^ 2 = 1 by rw [← pow_mul]; exact hk4))
          (fun h => hk2' (congrArg Subtype.val h))
      have h3 := (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd3 e _).mp h2
      exact congrArg Subtype.val h3
    have htwo : ∀ {R R' : Subgroup (spinGroup (quadOdd 3 K))},
        (∀ y, y ∈ R → y ∈ R' → y = 1) → (∃ k ∈ J ⊓ R, k ^ 4 = 1 ∧ k ^ 2 ≠ 1) →
          (∃ k ∈ J ⊓ R', k ^ 4 = 1 ∧ k ^ 2 ≠ 1) → False := by
      intro R R' hRR' ⟨k, hk, hk4, hk2'⟩ ⟨k', hk', hk4', hk2''⟩
      have e1 := hsq k hk.1 hk4 hk2'
      have e2 := hsq k' hk'.1 hk4' hk2''
      apply hι1
      apply hRR'
      · rw [← e1]
        exact pow_mem hk.2 2
      · rw [← e2]
        exact pow_mem hk'.2 2
    have hconc : ∀ {R : Subgroup (spinGroup (quadOdd 3 K))}, R ≤ centralizer {tSeven K} →
        (R.subgroupOf (centralizer {tSeven K})).Normal → Nat.card R = 24 → x ∈ R → J = R := by
      intro R hRC hRn hR24 hxR
      have hN := normal_subgroupOf_of_le hRn hRC hJC
      have htop := normal_eq_top_of_mem_sl23 e hN (x := ⟨x, hxJ⟩) hxR
        (Subtype.ext (by simpa using hx3)) (fun h => hx1 (congrArg Subtype.val h))
      have hJR : J ≤ R := (subgroupOf_eq_top.mp htop)
      refine eq_of_le_of_card_ge hJR ?_
      rw [card_eq_24 card_zmod_three e]
      exact hR24.le
    have h24 : ∀ (ρ : SL(2, K) →* spinGroup (quadOdd 3 K)) (hρ : Function.Injective ρ),
        Nat.card ρ.range = 24 := fun ρ hρ =>
      card_eq_24 hK (MonoidHom.ofInjective hρ).symm
    have ht3 : tSeven K ^ 3 = tSeven K := by rw [pow_succ, pow_two, htt, one_mul]
    have hzt3 : (spinZ K * tSeven K) ^ 3 = spinZ K * tSeven K := by
      rw [pow_succ, pow_two, hztzt, one_mul]
    have hz3 : spinZ K ^ 3 = spinZ K := by rw [pow_succ, pow_two, hzz, one_mul]
    by_cases h1 : a = 1 ∨ a = spinZ K
    · by_cases h2 : b = 1 ∨ b = tSeven K
      · by_cases h3 : c = 1 ∨ c = spinZ K * tSeven K
        · exact absurd ⟨h1, h2, h3⟩ hnot
        ·
          right; right
          refine hconc l3 n3 (h24 _ (longSL2_injective _ fin3_zero_ne_one true false)) ?_
          rcases hcub with ⟨ha', hb', -⟩ | ⟨ha', hb', -⟩
          · have ha1 : a = 1 := by
              rcases h1 with rfl | rfl
              · rfl
              · rw [hz3] at ha'; exact absurd ha' hz1
            have hb1 : b = 1 := by
              rcases h2 with rfl | rfl
              · rfl
              · rw [ht3] at hb'; exact absurd hb' ht1
            rw [← hw, ha1, hb1, one_mul, one_mul]
            exact hc
          · have haz : a = spinZ K := by
              rcases h1 with rfl | rfl
              · rw [one_pow] at ha'; exact absurd ha'.symm hz1
              · rfl
            have hbt : b = tSeven K := by
              rcases h2 with rfl | rfl
              · rw [one_pow] at hb'; exact absurd hb'.symm ht1
              · rfl
            rw [← hw, haz, hbt]
            exact mul_mem hztJ₃ hc
      · by_cases h3 : c = 1 ∨ c = spinZ K * tSeven K
        ·
          right; left
          refine hconc l2 n2 (h24 _ (longSL2_injective _ fin3_zero_ne_one true true)) ?_
          rcases hcub with ⟨ha', -, hc'⟩ | ⟨ha', -, hc'⟩
          · have ha1 : a = 1 := by
              rcases h1 with rfl | rfl
              · rfl
              · rw [hz3] at ha'; exact absurd ha' hz1
            have hc1 : c = 1 := by
              rcases h3 with rfl | rfl
              · rfl
              · rw [hzt3] at hc'; exact absurd hc' hzt1
            rw [← hw, ha1, hc1, one_mul, mul_one]
            exact hb
          · have haz : a = spinZ K := by
              rcases h1 with rfl | rfl
              · rw [one_pow] at ha'; exact absurd ha'.symm hz1
              · rfl
            have hczt : c = spinZ K * tSeven K := by
              rcases h3 with rfl | rfl
              · rw [one_pow] at hc'; exact absurd hc'.symm hzt1
              · rfl
            have hprod : a * b * c = b * tSeven K := by
              rw [haz, hczt, hzcomm b, mul_assoc, ← mul_assoc (spinZ K), hzz, one_mul]
            rw [← hw, hprod]
            exact mul_mem hb htJ₂
        · exact (htwo (fun y hy hy' => (hinf y).2.2 hy hy') (hk2 h2) (hk3 h3)).elim
    · by_cases h2 : b = 1 ∨ b = tSeven K
      · by_cases h3 : c = 1 ∨ c = spinZ K * tSeven K
        ·
          left
          refine hconc l1 n1 (h24 _ injective_shortSeven) ?_
          rcases hcub with ⟨-, hb', hc'⟩ | ⟨-, hb', hc'⟩
          · have hb1 : b = 1 := by
              rcases h2 with rfl | rfl
              · rfl
              · rw [ht3] at hb'; exact absurd hb' ht1
            have hc1 : c = 1 := by
              rcases h3 with rfl | rfl
              · rfl
              · rw [hzt3] at hc'; exact absurd hc' hzt1
            rw [← hw, hb1, hc1, mul_one, mul_one]
            exact ha
          · have hbt : b = tSeven K := by
              rcases h2 with rfl | rfl
              · rw [one_pow] at hb'; exact absurd hb'.symm ht1
              · rfl
            have hczt : c = spinZ K * tSeven K := by
              rcases h3 with rfl | rfl
              · rw [one_pow] at hc'; exact absurd hc'.symm hzt1
              · rfl
            have hprod : a * b * c = a * spinZ K := by
              rw [hbt, hczt, mul_assoc, ← mul_assoc (tSeven K), htz, mul_assoc, htt, mul_one]
            rw [← hw, hprod]
            exact mul_mem ha hzJ₁
        · exact (htwo (fun y hy hy' => (hinf y).2.1 hy hy') (hk1 h1) (hk3 h3)).elim
      · exact (htwo (fun y hy hy' => (hinf y).1 hy hy') (hk1 h1) (hk2 h2)).elim

end Three

end CFSG.ComponentClassification.HarrisLit.T1
