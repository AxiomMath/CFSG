module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.ComponentClassification.CatFC.DS81.ClLift

open Subgroup CFSG.Open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem commute_of_commute_mk [CharP K 2] {H : Subgroup (GL ι K)} (s t : H)
    (hs : (QuotientGroup.mk s : StatedProj H) ^ 2 = 1)
    (hst : Commute (QuotientGroup.mk s : StatedProj H) (QuotientGroup.mk t)) :
    Commute s t := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : Subsingleton H := ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
    exact Subsingleton.elim (s * t) (t * s)
  set N := (StatedScalars ι K).subgroupOf H
  have hcen : ∀ g : H, g ∈ N → ∀ x : H, x * g = g * x := by
    intro g hg x
    have hg' : (g : GL ι K) ∈ Subgroup.center (GL ι K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hg
    exact Subtype.ext (Subgroup.mem_center_iff.mp hg' x)
  have hsq : ∀ g : H, g ∈ N → g ^ 2 = 1 → g = 1 := by
    intro g hg hg2
    obtain ⟨c, hc⟩ : (g : GL ι K) ∈ (Matrix.GeneralLinearGroup.scalar ι).range := hg
    have hc2 : ((c : K)) ^ 2 = 1 := by
      have h1 : Matrix.GeneralLinearGroup.scalar ι (c ^ 2) = 1 := by
        rw [map_pow, hc, ← Subgroup.coe_pow, hg2, Subgroup.coe_one]
      have h2 := congrArg (fun x : GL ι K => (x : Matrix ι ι K)) h1
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one] at h2
      have h3 : Matrix.scalar ι (((c ^ 2 : Kˣ)) : K) = Matrix.scalar ι 1 := by
        rw [map_one]; exact h2
      have := (Matrix.scalar_inj (n := ι)).mp h3
      simpa using this
    have hc1 : c = 1 := by
      have : (c : K) ^ 2 = 1 ^ 2 := by rw [one_pow, hc2]
      exact Units.ext (frobenius_inj K 2 this)
    apply Subtype.ext
    rw [Subgroup.coe_one, ← hc, hc1, map_one]
  have hmu : (s * t)⁻¹ * (t * s) ∈ N := by
    rw [← QuotientGroup.eq]
    simpa [QuotientGroup.mk_mul] using hst.eq
  set μ := (s * t)⁻¹ * (t * s) with hμ
  have hts : t * s = s * t * μ := by rw [hμ]; group
  have hs2 : s ^ 2 ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using hs
  have h1 : t * s ^ 2 = s ^ 2 * t := hcen _ hs2 t
  have h2 : t * s ^ 2 = s ^ 2 * t * μ ^ 2 := by
    calc t * s ^ 2 = t * s * s := by rw [pow_two, mul_assoc]
      _ = s * t * μ * s := by rw [hts]
      _ = s * t * (s * μ) := by rw [mul_assoc (s * t) μ s, hcen μ hmu s]
      _ = s * (t * s) * μ := by group
      _ = s * (s * t * μ) * μ := by rw [hts]
      _ = s ^ 2 * t * μ ^ 2 := by rw [pow_two, pow_two]; simp only [mul_assoc]
  have hμ2 : μ ^ 2 = 1 := by
    have := h1.symm.trans h2
    exact (mul_eq_left.mp this.symm)
  have hμ1 : μ = 1 := hsq μ hmu hμ2
  show s * t = t * s
  rw [hts, hμ1, mul_one]

theorem exists_lift_pow_twentythree [Finite K] {H : Subgroup (GL ι K)} (y : StatedProj H)
    (hy : orderOf y = 23) :
    ∃ g : H, (QuotientGroup.mk g : StatedProj H) = y ∧ ∃ b : ℕ, g ^ (23 ^ b) = 1 := by
  classical
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective y
  have hm : orderOf g0 ≠ 0 := (orderOf_pos g0).ne'
  obtain ⟨b, m', hm', hdecomp⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm 23 (by norm_num)
  have hco : Nat.Coprime 23 m' :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm')).symm
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hco 1 0
  refine ⟨g0 ^ k, ?_, b, ?_⟩
  · rw [QuotientGroup.mk_pow]
    rw [← pow_mod_orderOf, hy, hk1, Nat.one_mod, pow_one]
  · rw [← pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hdecomp, mul_comm (23 ^ b) m']
    exact Nat.mul_dvd_mul_right (Nat.modEq_zero_iff_dvd.mp hk0) _

theorem exists_commuting_pow_lift [Finite K] [CharP K 2] {H : Subgroup (GL ι K)} (th : H)
    (hτ : (QuotientGroup.mk th : StatedProj H) ^ 2 = 1)
    (h23 : 23 ∣ Nat.card ↥(centralizer ({(QuotientGroup.mk th : StatedProj H)} :
      Set (StatedProj H)))) :
    ∃ (yh : H) (b : ℕ), yh ^ (23 ^ b) = 1 ∧ (QuotientGroup.mk yh : StatedProj H) ≠ 1 ∧
      Commute th yh := by
  classical
  haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' 23 h23
  set y : StatedProj H := (y' : StatedProj H) with hy
  have hyo : orderOf y = 23 := by rw [hy, Subgroup.orderOf_coe, hy']
  have hτy : Commute (QuotientGroup.mk th : StatedProj H) y := by
    have := y'.2
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm
  obtain ⟨yh, hyh, b, hyhb⟩ := exists_lift_pow_twentythree y hyo
  refine ⟨yh, b, hyhb, ?_, commute_of_commute_mk th yh hτ (by rw [hyh]; exact hτy)⟩
  intro h1
  rw [hyh] at h1
  rw [h1, orderOf_one] at hyo
  norm_num at hyo

theorem eightynine_dvd_of_commute {H : Subgroup (GL ι K)} (th zh : H) (hc : Commute th zh)
    (h89 : zh ^ 89 = 1) (h1 : (QuotientGroup.mk zh : StatedProj H) ≠ 1) :
    89 ∣ Nat.card ↥(centralizer ({(QuotientGroup.mk th : StatedProj H)} : Set (StatedProj H))) := by
  set z : StatedProj H := QuotientGroup.mk zh with hz
  have hz89 : z ^ 89 = 1 := by rw [hz, ← QuotientGroup.mk_pow, h89, QuotientGroup.mk_one]
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have hzo : orderOf z = 89 := orderOf_eq_prime hz89 h1
  have hzC : z ∈ centralizer ({(QuotientGroup.mk th : StatedProj H)} : Set (StatedProj H)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hz, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      hc.symm.eq]
  have := orderOf_dvd_natCard (⟨z, hzC⟩ : ↥(centralizer ({(QuotientGroup.mk th : StatedProj H)} :
    Set (StatedProj H))))
  rwa [Subgroup.orderOf_mk, hzo] at this

theorem commute_iff_matrix {H : Subgroup (GL ι K)} (a b : H) :
    Commute a b ↔
      Commute (((a : GL ι K)) : Matrix ι ι K) (((b : GL ι K)) : Matrix ι ι K) := by
  constructor
  · intro h
    have := congrArg (fun x : H => (((x : GL ι K)) : Matrix ι ι K)) h.eq
    show _ * _ = _ * _
    simpa only [Subgroup.coe_mul, Units.val_mul] using this
  · intro h
    apply Subtype.ext
    apply Units.ext
    simpa only [Subgroup.coe_mul, Units.val_mul] using h.eq

theorem pow_eq_one_iff_matrix {H : Subgroup (GL ι K)} (a : H) (m : ℕ) :
    a ^ m = 1 ↔ (((a : GL ι K)) : Matrix ι ι K) ^ m = 1 := by
  constructor
  · intro h
    have := congrArg (fun x : H => (((x : GL ι K)) : Matrix ι ι K)) h
    simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
      using this
  · intro h
    apply Subtype.ext
    apply Units.ext
    simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
      using h

theorem matrix_eq_one_iff {H : Subgroup (GL ι K)} (a : H) :
    (((a : GL ι K)) : Matrix ι ι K) = 1 ↔ a = 1 := by
  constructor
  · intro h
    exact Subtype.ext (Units.ext h)
  · rintro rfl
    rfl

theorem mk_ne_one_of_not_scalar {H : Subgroup (GL ι K)} (zh : H)
    (h : ∀ c : K, (((zh : GL ι K)) : Matrix ι ι K) ≠ Matrix.scalar ι c) :
    (QuotientGroup.mk zh : StatedProj H) ≠ 1 := by
  intro h1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at h1
  obtain ⟨u, hu⟩ := h1
  apply h u
  rw [← hu, Matrix.GeneralLinearGroup.coe_scalar]

@[expose] def glOfPow89 (z : Matrix ι ι K) (h : z ^ 89 = 1) : GL ι K :=
  ⟨z, z ^ 88, by rw [← pow_succ', h], by rw [← pow_succ, h]⟩

theorem eq_one_of_pow_eq_one_of_coprime {c : K} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : c ^ a = 1) (hb : c ^ b = 1) : c = 1 := by
  have : c ^ Nat.gcd a b = 1 := pow_gcd_eq_one.mpr ⟨ha, hb⟩
  rwa [hab, pow_one] at this

theorem form_scalar [Nonempty ι] (θ : K →+* K) (M : Matrix ι ι K) (hM : IsUnit M.det) (c : K)
    (h : ((Matrix.scalar ι c).map θ)ᵀ * M * Matrix.scalar ι c = M) : θ c * c = 1 := by
  have h1 : ((Matrix.scalar ι c).map θ)ᵀ * M * Matrix.scalar ι c = (θ c * c) • M := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_map, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.diagonal_transpose]
    ring
  rw [h1] at h
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp [Matrix.det_zero] at hM
  have h2 : (θ c * c - 1) • M = 0 := by rw [sub_smul, h, one_smul, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 hM0

end CFSG.ComponentClassification.CatFC.DS81.ClLift
