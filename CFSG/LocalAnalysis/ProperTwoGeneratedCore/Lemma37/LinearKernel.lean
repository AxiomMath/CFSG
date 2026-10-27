module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearSetup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderComponent

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G]

@[expose] def sylowInvolutionCentralizer (S : Subgroup G) : Subgroup G :=
  S ⊓ Subgroup.centralizer {t | t ∈ S ∧ t * t = 1}

omit [Finite G] in
theorem mem_sylowInvolutionCentralizer_iff {S : Subgroup G} {w : G} :
    w ∈ sylowInvolutionCentralizer S ↔ w ∈ S ∧ ∀ t ∈ S, t * t = 1 → t * w = w * t := by
  rw [sylowInvolutionCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hw, h⟩
    exact ⟨hw, fun t ht htt => h t ⟨ht, htt⟩⟩
  · rintro ⟨hw, h⟩
    exact ⟨hw, fun t ht => h t ht.1 ht.2⟩

omit [Finite G] in
theorem conj_mem_sylowInvolutionCentralizer {S : Subgroup G} {w n : G}
    (hw : w ∈ sylowInvolutionCentralizer S) (hn : n ∈ Subgroup.normalizer (S : Set G)) :
    n⁻¹ * w * n ∈ sylowInvolutionCentralizer S := by
  rw [mem_sylowInvolutionCentralizer_iff] at hw ⊢
  refine ⟨(Subgroup.mem_normalizer_iff''.mp hn w).mp hw.1, fun t ht htt => ?_⟩
  have hnt : n * t * n⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hn t).mp ht
  have hntt : n * t * n⁻¹ * (n * t * n⁻¹) = 1 := by
    calc n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have h := hw.2 _ hnt hntt
  calc t * (n⁻¹ * w * n) = n⁻¹ * (n * t * n⁻¹ * w) * n := by group
    _ = n⁻¹ * (w * (n * t * n⁻¹)) * n := by rw [h]
    _ = n⁻¹ * w * n * t := by group

variable {S : Sylow 2 G} {H : Subgroup G} {z : G} (hset : CoreSetting G S H)
  (hz : IsCentralInvolution (S : Subgroup G) z) (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H)
  {J : Subgroup (EscapingQuotient z)} (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∉ J)
  {D : Subgroup (EscapingQuotient z)} {q : ℕ}
  (hlin : LinearSylowData J ((sylowBar hz).range ⊓ J) D q)
include hset hz hesc hJ hzJ hlin

omit hset hesc hJ hzJ in
theorem caseOne_sylowBar_centralizes {w : G} (hw : w ∈ sylowInvolutionCentralizer S) :
    ∀ x ∈ (sylowBar hz).range ⊓ J, sylowBar hz ⟨w, hw.1⟩ * x = x * sylowBar hz ⟨w, hw.1⟩ := by
  intro x hx
  obtain ⟨t, rfl⟩ := hx.1
  have htt := mul_self_eq_one_of_sylowBar hz (hlin.sq _ hx)
  have h := ((mem_sylowInvolutionCentralizer_iff.mp hw).2 t t.2 htt).symm
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h

theorem caseOne_exists_mem_centralizer {s : EscapingQuotient z}
    (hs : ∀ x ∈ (sylowBar hz).range ⊓ J, s * x = x * s) :
    ∃ j ∈ (sylowBar hz).range ⊓ J,
      j⁻¹ * s ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
  have hJn := caseOne_component_normal hset hz hesc hJ hzJ
  obtain ⟨j, hjR, hj⟩ := hlin.inner s (fun y hy => hJn.conj_mem y hy s) hs
  refine ⟨j, hjR, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have h := hj y hy
  calc y * (j⁻¹ * s) = j⁻¹ * (j * y * j⁻¹) * s := by group
    _ = j⁻¹ * (s * y * s⁻¹) * s := by rw [h]
    _ = j⁻¹ * s * y := by group

theorem caseOne_not_sq_fused {r a w : G} (hrS : r ∈ (S : Subgroup G)) (hr1 : r ≠ 1)
    (hrJ : sylowBar hz ⟨r, hrS⟩ ∈ J) (ha : a = r ∨ a = r * z) (haS : a ∈ (S : Subgroup G))
    (hw : w ∈ sylowInvolutionCentralizer S) : w * w ≠ a := by
  intro hwa
  have hq := caseOne_quotientData hset hz hesc
  set wb := sylowBar hz ⟨w, hw.1⟩
  obtain ⟨j, hjR, hk⟩ :=
    caseOne_exists_mem_centralizer hset hz hesc hJ hzJ hlin
      (caseOne_sylowBar_centralizes hz hlin hw)
  set k := j⁻¹ * wb
  have hjk : j * k = k * j := (Subgroup.mem_centralizer_iff.mp hk j (hlin.le hjR))
  have hsq : wb * wb = k * k := by
    have hwb : wb = j * k := by rw [mul_inv_cancel_left]
    rw [hwb, mul_assoc, ← mul_assoc k, ← hjk, ← mul_assoc, ← mul_assoc j j k, hlin.sq j hjR,
      one_mul]
  have haK : sylowBar hz ⟨a, haS⟩ ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    have h : sylowBar hz ⟨a, haS⟩ = wb * wb := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hwa.symm
    rw [h, hsq]
    exact Subgroup.mul_mem _ hk hk
  have hrK : sylowBar hz ⟨r, hrS⟩ ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    rcases ha with rfl | rfl
    · exact haK
    · have h : sylowBar hz ⟨r * z, haS⟩ = sylowBar hz ⟨r, hrS⟩ * escapingBar z := by
        rw [← sylowBar_self hz, ← map_mul]
        rfl
      have h2 : sylowBar hz ⟨r, hrS⟩ = sylowBar hz ⟨r * z, haS⟩ * escapingBar z := by
        rw [h, mul_assoc, escapingBar_mul_self hz.2.1, mul_one]
      rw [h2]
      exact Subgroup.mul_mem _ haK hq.bar_mem_component_centralizer
  have hbot := hq.component_inf_centralizer_eq_bot hJ hzJ
  have h1 : sylowBar hz ⟨r, hrS⟩ = 1 := by
    have h := Subgroup.mem_inf.mpr ⟨hrJ, hrK⟩
    rwa [hbot, Subgroup.mem_bot] at h
  apply hr1
  have h2 := sylowBar_injective hz (h1.trans (map_one _).symm)
  exact congrArg Subtype.val h2

theorem caseOne_not_sq_central {w : G} (hw : w ∈ sylowInvolutionCentralizer S) : w * w ≠ z := by
  intro hwz
  obtain ⟨r, hr, -, hrJ, a, ha, haS, -, n, hn, -, hna⟩ :=
    coreSetting_component_fused_class hset hz hesc hJ hzJ
  have hr1 : (r : G) ≠ 1 := by
    intro h
    have h2 := hr.2.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  refine caseOne_not_sq_fused hset hz hesc hJ hzJ hlin hr.1 hr1 hrJ ha haS.1
    (conj_mem_sylowInvolutionCentralizer hw hn) ?_
  rw [← hna, ← hwz]
  group

theorem caseOne_component_centralizer_eq :
    Subgroup.centralizer (J : Set (EscapingQuotient z)) = Subgroup.zpowers (escapingBar z) := by
  have hq := caseOne_quotientData hset hz hesc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hq.component_centralizer_normal hJ hzJ
  refine le_antisymm (normal_le_zpowers_of_unique_involution hq.oddCore_eq_bot hq.bar_mem_center
    (fun k hk hk2 => hq.eq_bar_of_mem_component_centralizer hJ hzJ hk hk2) ?_)
    (Subgroup.zpowers_le.mpr hq.bar_mem_component_centralizer)
  intro k hk hk2
  have hk4 : k ^ 2 ^ 2 = 1 := by
    rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul, hk2, pow_two, escapingBar_mul_self hz.2.1]
  have hkp : IsPGroup 2 (Subgroup.zpowers k) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨2, Subtype.ext ?_⟩
    change (k ^ i) ^ 2 ^ 2 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk4, one_zpow]
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow (sylowBarSylow hz) hkp
  have hk' : g⁻¹ * k * g ∈ (sylowBar hz).range := by
    rw [← coe_sylowBarSylow]
    exact hg k (Subgroup.mem_zpowers k)
  obtain ⟨w, hw⟩ := hk'
  have hwK : sylowBar hz w ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    rw [hw]
    simpa using (Subgroup.Normal.conj_mem inferInstance k hk g⁻¹)
  have hwsq : sylowBar hz w * sylowBar hz w = escapingBar z := by
    rw [hw]
    calc g⁻¹ * k * g * (g⁻¹ * k * g) = g⁻¹ * (k * k) * g := by group
      _ = g⁻¹ * escapingBar z * g := by rw [← pow_two, hk2]
      _ = escapingBar z := by
          rw [mul_assoc, ← (hq.commute_bar g).eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hwz : (w : G) * w = z := by
    have h : sylowBar hz (w * w) = sylowBar hz ⟨z, hz.1⟩ := by rw [map_mul, hwsq, sylowBar_self]
    exact congrArg Subtype.val (sylowBar_injective hz h)
  refine caseOne_not_sq_central hset hz hesc hJ hzJ hlin
    (mem_sylowInvolutionCentralizer_iff.mpr ⟨w.2, fun t ht htt => ?_⟩) hwz
  have htt' : sylowBar hz ⟨t, ht⟩ * sylowBar hz ⟨t, ht⟩ = 1 := by
    rw [← map_mul]
    rw [show (⟨t, ht⟩ : (S : Subgroup G)) * ⟨t, ht⟩ = 1 from Subtype.ext htt, map_one]
  have hcomm : sylowBar hz ⟨t, ht⟩ * sylowBar hz w = sylowBar hz w * sylowBar hz ⟨t, ht⟩ := by
    by_cases ht1 : sylowBar hz ⟨t, ht⟩ = 1
    · rw [ht1, one_mul, mul_one]
    have ht2 : orderOf (sylowBar hz ⟨t, ht⟩) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact htt') ht1
    rcases hq.involution_mem_component_or hJ hzJ ht2 with htJ | htJ
    · exact Subgroup.mem_centralizer_iff.mp hwK _ htJ
    · have h := Subgroup.mem_centralizer_iff.mp hwK _ htJ
      have hzc := (hq.commute_bar (sylowBar hz w)).eq
      calc sylowBar hz ⟨t, ht⟩ * sylowBar hz w
          = escapingBar z * (escapingBar z * sylowBar hz ⟨t, ht⟩ * sylowBar hz w) := by
            rw [← mul_assoc, ← mul_assoc, escapingBar_mul_self hz.2.1, one_mul]
        _ = escapingBar z * (sylowBar hz w * (escapingBar z * sylowBar hz ⟨t, ht⟩)) := by rw [h]
        _ = sylowBar hz w * sylowBar hz ⟨t, ht⟩ := by
            rw [← mul_assoc (sylowBar hz w), hzc, ← mul_assoc, ← mul_assoc,
              escapingBar_mul_self hz.2.1, one_mul]
  exact commute_of_sylowBar hz hcomm

theorem caseOne_mem_or_of_centralizes {s : EscapingQuotient z}
    (hs : ∀ x ∈ (sylowBar hz).range ⊓ J, s * x = x * s) : s ∈ J ∨ escapingBar z * s ∈ J := by
  have hq := caseOne_quotientData hset hz hesc
  obtain ⟨j, hjR, hjK⟩ := caseOne_exists_mem_centralizer hset hz hesc hJ hzJ hlin hs
  rw [caseOne_component_centralizer_eq hset hz hesc hJ hzJ hlin] at hjK
  have hjJ : j ∈ J := hlin.le hjR
  rcases eq_one_or_eq_of_mem_zpowers hq.bar_order hjK with h | h
  · left
    rw [inv_mul_eq_one] at h
    exact h ▸ hjJ
  · right
    have hs' : s = j * escapingBar z := by rw [← h, mul_inv_cancel_left]
    rw [hs', (hq.commute_bar j).eq, ← mul_assoc, escapingBar_mul_self hz.2.1, one_mul]
    exact hjJ

end CFSG.ProperTwoGeneratedCore.Lemma37
