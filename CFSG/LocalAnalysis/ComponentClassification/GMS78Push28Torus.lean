module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Push28Trans
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315Torus

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem exists_mul_two_odd [Finite G] (n : G) :
    ∃ a ∈ zpowers n, ∃ b ∈ zpowers n, n = a * b ∧ (∃ k : ℕ, a ^ 2 ^ k = 1) ∧ Odd (orderOf b) := by
  obtain ⟨k, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have hb := Nat.gcd_eq_gcd_ab (2 ^ k) m
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at hb
  set α := Nat.gcdA (2 ^ k) m
  set β := Nat.gcdB (2 ^ k) m
  have hNz : ((orderOf n : ℕ) : ℤ) = (2 ^ k : ℕ) * (m : ℤ) := by rw [hN, Nat.cast_mul]
  have hone : n ^ ((orderOf n : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  refine ⟨n ^ ((m : ℤ) * β), zpow_mem (mem_zpowers n) _, n ^ (((2 ^ k : ℕ) : ℤ) * α),
    zpow_mem (mem_zpowers n) _, ?_, ⟨k, ?_⟩, ?_⟩
  · rw [← zpow_add, add_comm, ← hb, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul]
    have : (m : ℤ) * β * ((2 ^ k : ℕ) : ℤ) = ((orderOf n : ℕ) : ℤ) * β := by rw [hNz]; ring
    rw [this, zpow_mul, hone, one_zpow]
  · apply hm.of_dvd_nat
    apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul]
    have : ((2 ^ k : ℕ) : ℤ) * α * (m : ℤ) = ((orderOf n : ℕ) : ℤ) * α := by rw [hNz]; ring
    rw [this, zpow_mul, hone, one_zpow]

theorem mem_normalizer_of_conj_mem_of_finite' [Finite G] {H : Subgroup G} {g : G}
    (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hle : rightConjugate H g⁻¹ ≤ H := by
    intro x hx
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have := hg _ hx
    simpa [mul_assoc] using this
  have heq : rightConjugate H g⁻¹ = H :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
  have := inv_mem ((rightConjugate_eq_self_iff H g⁻¹).mp heq)
  rwa [inv_inv] at this

structure Push28Torus (L T R : Subgroup G) (y d : G) : Prop where
  mem_normalizer : d ∈ normalizer (R : Set G)
  mem_normalizer_V : d ∈ normalizer (gmsV L T : Set G)
  odd : Odd (orderOf d)
  conj_eq : ∀ v ∈ gmsV L T, d * v * d⁻¹ = y * v * y⁻¹

variable [Finite G] {L T R : Subgroup G} {f : ℕ}

namespace Sec3.IsR

theorem exists_push28Torus
    (hR : Sec3.IsR L T R) (h313 : Lemma313 L T (2 ^ f)) (h : Sec3 G L T) (hF : Foundation)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    {y : G} (hy : Sec3.IsTorus L T y) : ∃ d, Push28Torus L T R y d := by
  obtain ⟨d, hdR, hdW, hdo, hdy⟩ := hR.exists_torus h313 h
    (h.inf_centralizer_eq_of_psl2 hF hf e hX) hy
    (h.commute_of_odd_of_mem_gmsTrans_of_psl2 hF hf e hX)
  rw [h.gmsW_eq_of_psl2 hf e] at hdW hdy
  exact ⟨d, ⟨hdR, hdW, hdo, hdy⟩⟩

end Sec3.IsR

namespace Push28Torus

variable {y d : G}

omit [Finite G] in
theorem conj_T₀ (hd : Push28Torus L T R y d) (hy : Sec3.IsTorus L T y) {t : G}
    (ht : t ∈ T ⊓ centralizer (L : Set G)) : d * t * d⁻¹ = t := by
  rw [hd.conj_eq t (mem_sup_right ht), hy.commute ht, mul_inv_cancel_right]

omit [Finite G] in
theorem pow_conj_eq (hd : Push28Torus L T R y d) (hy : Sec3.IsTorus L T y) (k : ℕ) :
    ∀ v ∈ gmsV L T, d ^ k * v * (d ^ k)⁻¹ = y ^ k * v * (y ^ k)⁻¹ := by
  induction k with
  | zero => intro v _; simp
  | succ k ih =>
    intro v hv
    have hkv : y ^ k * v * (y ^ k)⁻¹ ∈ gmsV L T :=
      (mem_normalizer_iff.mp (pow_mem hy.mem_normalizer k) v).mp hv
    calc d ^ (k + 1) * v * (d ^ (k + 1))⁻¹ = d * (d ^ k * v * (d ^ k)⁻¹) * d⁻¹ := by group
      _ = y * (y ^ k * v * (y ^ k)⁻¹) * y⁻¹ := by rw [ih v hv, hd.conj_eq _ hkv]
      _ = y ^ (k + 1) * v * (y ^ (k + 1))⁻¹ := by group

theorem fix_iff
    (hd : Push28Torus L T R y d) (hR : Sec3.IsR L T R) (hy : Sec3.IsTorus L T y)
    (h313 : Lemma313 L T (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f)) {x : G}
    (hx : x ∈ R) : d * x * d⁻¹ * x⁻¹ ∈ gmsA L T ↔ x ∈ gmsV L T := by
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀
  constructor
  · intro ha
    by_contra hxV
    obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
    have hxN : x ∈ normalizer (gmsV L T : Set G) := hR.le_normalizer_gmsV hx
    set Q := rightConjugate T₀ x⁻¹ with hQ
    have hQΔ : Q ∈ gmsDelta L T := Sec3.rightConjugate_mem_delta Sec3.mem_delta_T₀ (inv_mem hxN)
    have hQT : Q ≠ T₀ := by
      intro heq
      apply hxV
      have h1 := inv_mem ((rightConjugate_eq_self_iff T₀ x⁻¹).mp heq)
      rw [inv_inv] at h1
      rw [← hR.inf_normalizer_eq_of_psl2 h313 h hF hf e hX]
      exact mem_inf.mpr ⟨hx, h1⟩
    have hQV : Q ≤ gmsV L T := hQΔ.2
    have hdQ : ∀ q ∈ Q, d * q * d⁻¹ ∈ Q := by
      intro q hq
      have hq' := hq
      rw [hQ, mem_rightConjugate_iff, inv_inv] at hq'
      set a := d * x * d⁻¹ * x⁻¹ with ha'
      have hcomm : a * q = q * a :=
        congrArg Subtype.val (hVel.1.is_comm.comm ⟨a, mem_sup_left ha⟩ ⟨q, hQV hq⟩)
      have e1 : d * q * d⁻¹ = (d * x * d⁻¹) * (d * (x⁻¹ * q * x) * d⁻¹) * (d * x * d⁻¹)⁻¹ := by
        group
      have e2 : d * (x⁻¹ * q * x) * d⁻¹ = x⁻¹ * q * x := hd.conj_T₀ hy hq'
      have e3 : d * x * d⁻¹ = a * x := by rw [ha']; group
      rw [e1, e2, e3]
      have e4 : a * x * (x⁻¹ * q * x) * (a * x)⁻¹ = a * q * a⁻¹ := by group
      rw [e4, hcomm, mul_inv_cancel_right]
      exact hq
    have hyQ : y ∈ normalizer (Q : Set G) := mem_normalizer_of_conj_mem_of_finite' fun q hq => by
      rw [← hd.conj_eq q (hQV hq)]
      exact hdQ q hq
    have hne : (⟨Q, hQΔ⟩ : gmsDelta L T) ≠ deltaT₀ L T := fun h1 => hQT (congrArg Subtype.val h1)
    exact hy.perm_apply_ne h313 hX h hne ((deltaPerm_apply_eq_iff _ _).mpr hyQ)
  · intro hxV
    rw [hd.conj_eq x hxV]
    exact (Sec3.IsTorus.mem_gmsN₁ hy).2.2 x hxV

theorem exists_conj_mem
    (hd : Push28Torus L T R y d) (hR : Sec3.IsR L T R) (hy : Sec3.IsTorus L T y)
    (h313 : Lemma313 L T (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f)) {x x₀ : G}
    (hx : x ∈ R) (hxV : x ∉ gmsV L T) (hx₀ : x₀ ∈ R) (hx₀V : x₀ ∉ gmsV L T) :
    ∃ k : ℕ, x⁻¹ * ((d ^ k)⁻¹ * x₀ * d ^ k) ∈ gmsV L T := by
  have hW := h.gmsW_eq_of_psl2 hf e
  have h1 := hR.exists_pow_conj_mem h313 hX h hF (h.inf_centralizer_eq_of_psl2 hF hf e hX) hy
    hd.mem_normalizer (hW ▸ hd.mem_normalizer_V) (hW ▸ hd.conj_eq) hx₀ (hW ▸ hx₀V) hx (hW ▸ hxV)
  rwa [hW] at h1

theorem exists_conj_eq_of_mem_centralizer
    (hR : Sec3.IsR L T R) (h313 : Lemma313 L T (2 ^ f))
    (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f))
    (hX : Sec3.Facts L T (2 ^ f)) {n : G} (hn : n ∈ centralizer (gmsV L T : Set G))
    (hnR : n ∈ normalizer (R : Set G)) :
    ∃ v ∈ gmsV L T, ∀ x ∈ R, n * x * n⁻¹ = v * x * v⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀
  obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
  obtain ⟨a, ha, b, hb, hab, ⟨k, hk⟩, hbo⟩ := exists_mul_two_odd n
  have hzC : zpowers n ≤ centralizer (gmsV L T : Set G) := zpowers_le.mpr hn
  have hzR : zpowers n ≤ normalizer (R : Set G) := zpowers_le.mpr hnR
  have haV : a ∈ gmsV L T := by
    have haTr : a ∈ gmsTrans L T := Sec3.centralizer_le_gmsTrans (hzC ha)
    have hap : IsPGroup 2 (zpowers a) := by
      have hdvd : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hp := hap.to_sup_of_normal_right' hR.isPGroup (zpowers_le.mpr (hzR ha))
    have heq := hR.sylow.eq_of_le le_sup_right (sup_le (zpowers_le.mpr haTr) hR.le_gmsTrans) hp
    have haR : a ∈ R := heq ▸ mem_sup_left (mem_zpowers a)
    exact hR.mem_gmsV_of_psl2 h313 h hF hf e hX haR Sec3.mem_delta_T₀
      (Subgroup.centralizer_le_normalizer _ (Sec3.mem_centralizer_T₀ (hzC ha)))
  have hbR : ∀ x ∈ R, b * x * b⁻¹ = x := by
    intro x hx
    have hbC := hzC hb
    have hxN : x ∈ normalizer (gmsV L T : Set G) := hR.le_normalizer_gmsV hx
    have hQ : rightConjugate T₀ x⁻¹ ≤ gmsV L T :=
      (Sec3.rightConjugate_mem_delta Sec3.mem_delta_T₀ (inv_mem hxN)).2
    have hbQ : b ∈ normalizer (rightConjugate T₀ x⁻¹ : Set G) :=
      Subgroup.centralizer_le_normalizer _
        (mem_centralizer_iff.mpr fun q hq => (mem_centralizer_iff.mp hbC q (hQ hq)))
    have hbT₀ : b ∈ normalizer (T₀ : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Sec3.mem_centralizer_T₀ hbC)
    have hxb : x⁻¹ * b * x ∈ normalizer (T₀ : Set G) := by
      rw [← rightConjugate_eq_self_iff]
      have h1 := (rightConjugate_eq_self_iff _ b).mpr hbQ
      rw [← rightConjugate_mul, ← rightConjugate_mul, h1, rightConjugate_mul, inv_mul_cancel,
        rightConjugate_one]
    set z := x⁻¹ * (b * x * b⁻¹) with hz
    have hzR' : z ∈ R :=
      mul_mem (inv_mem hx) ((mem_normalizer_iff.mp (hzR hb) x).mp hx)
    have hzN : z ∈ normalizer (T₀ : Set G) := by
      have : z = (x⁻¹ * b * x) * b⁻¹ := by rw [hz]; group
      rw [this]
      exact mul_mem hxb (inv_mem hbT₀)
    have hzV : z ∈ gmsV L T :=
      hR.mem_gmsV_of_psl2 h313 h hF hf e hX hzR' Sec3.mem_delta_T₀ hzN
    have hbz : b * z = z * b := (mem_centralizer_iff.mp hbC z hzV).symm
    have hzz : z * z = 1 := by rw [← pow_two]; exact hVel.2 z hzV
    exact conj_eq_of_odd_of_eq_mul hbo hbz hzz (by rw [hz]; group)
  refine ⟨a, haV, fun x hx => ?_⟩
  rw [hab]
  calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    _ = a * x * a⁻¹ := by rw [hbR x hx]

theorem exists_conj_eq_of_mem_T
    (hd : Push28Torus L T R y d) (hR : Sec3.IsR L T R) (hy : Sec3.IsTorus L T y)
    (h313 : Lemma313 L T (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f)) {w : G}
    (hw : w ∈ T) : ∃ m : ℕ, ∃ v ∈ gmsV L T, ∀ x ∈ R,
      (w⁻¹ * d * w) * x * (w⁻¹ * d * w)⁻¹ = v * (d ^ m * x * (d ^ m)⁻¹) * v⁻¹ := by
  have hwV := h.le_normalizer_gmsV hw
  have hle : zpowers y ≤ normalizer (centralizer (gmsV L T : Set G) : Set G) :=
    zpowers_le.mpr (Sec3.normalizer_le_normalizer_centralizer_gmsV hy.mem_normalizer)
  obtain ⟨a, ha, c, hc, hac⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hle
    (hy.conj w (mem_inf.mpr ⟨h.sylow.le hw, hwV⟩))
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨m, hm⟩ : ∃ m : ℕ, y ^ m = y ^ k :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (zpow_mem (mem_zpowers y) k))
  rw [← hm] at hac
  set n := (w⁻¹ * d * w) * (d ^ m)⁻¹ with hn
  have hnC : n ∈ centralizer (gmsV L T : Set G) := by
    rw [mem_centralizer_iff]
    intro v hv
    have hv' : (d ^ m)⁻¹ * v * d ^ m ∈ gmsV L T := by
      have := (mem_normalizer_iff.mp (inv_mem (pow_mem hd.mem_normalizer_V m)) v).mp hv
      simpa using this
    have hwv : w * ((d ^ m)⁻¹ * v * d ^ m) * w⁻¹ ∈ gmsV L T :=
      (mem_normalizer_iff.mp hwV _).mp hv'
    have h1 : (w⁻¹ * d * w) * ((d ^ m)⁻¹ * v * d ^ m) * (w⁻¹ * d * w)⁻¹ =
        y ^ m * ((d ^ m)⁻¹ * v * d ^ m) * (y ^ m)⁻¹ := by
      have e1 : (w⁻¹ * d * w) * ((d ^ m)⁻¹ * v * d ^ m) * (w⁻¹ * d * w)⁻¹ =
          w⁻¹ * (d * (w * ((d ^ m)⁻¹ * v * d ^ m) * w⁻¹) * d⁻¹) * w := by group
      rw [e1, hd.conj_eq _ hwv]
      have e2 : w⁻¹ * (y * (w * ((d ^ m)⁻¹ * v * d ^ m) * w⁻¹) * y⁻¹) * w =
          (w⁻¹ * y * w) * ((d ^ m)⁻¹ * v * d ^ m) * (w⁻¹ * y * w)⁻¹ := by group
      rw [e2, ← hac]
      have hcv : c * ((d ^ m)⁻¹ * v * d ^ m) * c⁻¹ = (d ^ m)⁻¹ * v * d ^ m := by
        rw [← mem_centralizer_iff.mp hc _ hv']
        group
      calc y ^ m * c * ((d ^ m)⁻¹ * v * d ^ m) * (y ^ m * c)⁻¹
          = y ^ m * (c * ((d ^ m)⁻¹ * v * d ^ m) * c⁻¹) * (y ^ m)⁻¹ := by group
        _ = y ^ m * ((d ^ m)⁻¹ * v * d ^ m) * (y ^ m)⁻¹ := by rw [hcv]
    have h2 : y ^ m * ((d ^ m)⁻¹ * v * d ^ m) * (y ^ m)⁻¹ = v := by
      rw [← hd.pow_conj_eq hy m _ hv']
      group
    have h3 : n * v * n⁻¹ = v := by
      rw [hn]
      calc (w⁻¹ * d * w) * (d ^ m)⁻¹ * v * ((w⁻¹ * d * w) * (d ^ m)⁻¹)⁻¹
          = (w⁻¹ * d * w) * ((d ^ m)⁻¹ * v * d ^ m) * (w⁻¹ * d * w)⁻¹ := by group
        _ = v := by rw [h1, h2]
    calc v * n = n * v * n⁻¹ * n := by rw [h3]
      _ = n * v := by group
  have hnR : n ∈ normalizer (R : Set G) :=
    mul_mem (mul_mem (mul_mem (inv_mem (hR.le_normalizer hw)) hd.mem_normalizer)
      (hR.le_normalizer hw)) (inv_mem (pow_mem hd.mem_normalizer m))
  obtain ⟨v, hv, hvR⟩ := exists_conj_eq_of_mem_centralizer hR h313 h hF hf e hX hnC hnR
  refine ⟨m, v, hv, fun x hx => ?_⟩
  have hx' : d ^ m * x * (d ^ m)⁻¹ ∈ R :=
    (mem_normalizer_iff.mp (pow_mem hd.mem_normalizer m) x).mp hx
  have e1 : w⁻¹ * d * w = n * d ^ m := by rw [hn]; group
  rw [e1, ← hvR _ hx']
  group

end Push28Torus

end CFSG.ComponentClassification.GMS78
