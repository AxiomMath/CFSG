module

public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.SeitzReduction.RankOne

variable {K : Type*} [Field K]

@[expose] def szCommMap (a : ℕ) (γ : K) (x y : K × K × K) : K :=
  x.1 * y.1 ^ 2 ^ (a + 1) + x.1 ^ 2 ^ (a + 1) * y.1 +
    γ * ((x.1 * y.2.1) ^ 2 ^ a + (y.1 * x.2.1) ^ 2 ^ a) + x.2.2 * y.2.1 + y.2.2 * x.2.1

@[expose] def szTorusSmul (a : ℕ) (l : K) (x : K × K × K) : K × K × K :=
  (l * x.1, l ^ (2 ^ (a + 1) + 1) * x.2.1, x.2.2)

variable (K) in
@[expose] def szCoordSpace [CharP K 2] : AddSubgroup (K × K × K) where
  carrier := {x | x.2.2 = 0 ∨ x.2.2 = 1}
  add_mem' := by
    rintro x y (hx | hx) (hy | hy) <;>
      simp [Prod.snd_add, hx, hy, CharTwo.add_self_eq_zero]
  zero_mem' := Or.inl rfl
  neg_mem' := by
    rintro x (hx | hx) <;> simp [hx, CharTwo.neg_eq]

@[expose] def IsSzRad [CharP K 2] (a : ℕ) (γ : K) (x : K × K × K) : Prop :=
  ∃ w : K, ∀ y ∈ szCoordSpace K, szCommMap a γ x y ≠ w

namespace SzRadical

section Powers

variable [Fintype K] {a : ℕ}

theorem pow_theta_pow_sigma (hK : Fintype.card K = 2 ^ (2 * a + 1)) (z : K) :
    (z ^ 2 ^ (a + 1)) ^ 2 ^ a = z := by
  rw [← pow_mul, ← pow_add, show a + 1 + a = 2 * a + 1 by ring, ← hK, FiniteField.pow_card]

theorem pow_sigma_pow_theta (hK : Fintype.card K = 2 ^ (2 * a + 1)) (z : K) :
    (z ^ 2 ^ a) ^ 2 ^ (a + 1) = z := by
  rw [← pow_mul, ← pow_add, show a + (a + 1) = 2 * a + 1 by ring, ← hK, FiniteField.pow_card]

theorem pow_theta_pow_theta (hK : Fintype.card K = 2 ^ (2 * a + 1)) (z : K) :
    (z ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) = z ^ 2 := by
  rw [← pow_mul, ← pow_add, show a + 1 + (a + 1) = (2 * a + 1) + 1 by ring, pow_succ, pow_mul,
    ← hK, FiniteField.pow_card]

theorem exists_pow_sigma_eq (hK : Fintype.card K = 2 ^ (2 * a + 1)) (w : K) :
    ∃ z : K, z ^ 2 ^ a = w :=
  ⟨w ^ 2 ^ (a + 1), pow_theta_pow_sigma hK w⟩

theorem eq_zero_or_eq_one_of_pow_theta_eq (hK : Fintype.card K = 2 ^ (2 * a + 1)) {ν : K}
    (h : ν ^ 2 ^ (a + 1) = ν) : ν = 0 ∨ ν = 1 := by
  have h2 : ν ^ 2 = ν := by rw [← pow_theta_pow_theta hK, h, h]
  have h3 : ν * (ν - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h2, sub_self]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact Or.inl h4
  · exact Or.inr (sub_eq_zero.mp h4)

end Powers

theorem two_pow_ne_zero (k : ℕ) : (2 : ℕ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero

theorem frob_add [CharP K 2] (u v : K) (k : ℕ) : (u + v) ^ 2 ^ k = u ^ 2 ^ k + v ^ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih, pow_mul, pow_mul, add_sq, show (2 : K) = 0 from CharTwo.two_eq_zero,
      zero_mul, zero_mul, add_zero]

section Trace

variable [Fintype K] [Algebra (ZMod 2) K]

theorem trace_pow_two_pow [CharP K 2] (x : K) (m : ℕ) :
    Algebra.trace (ZMod 2) K (x ^ 2 ^ m) = Algebra.trace (ZMod 2) K x := by
  let f : K ≃+* K := iterateFrobeniusEquiv K 2 m
  let fA : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := f) (fun y => by
    have hcomp : f.toRingHom.comp (algebraMap (ZMod 2) K) = algebraMap (ZMod 2) K :=
      Subsingleton.elim _ _
    exact DFunLike.congr_fun hcomp y)
  have h := Algebra.trace_eq_of_algEquiv fA x
  have hx : fA x = x ^ 2 ^ m := iterateFrobeniusEquiv_def K 2 m x
  rwa [hx] at h

theorem eq_zero_of_forall_trace_mul_eq_zero {c : K}
    (h : ∀ y, Algebra.trace (ZMod 2) K (c * y) = 0) : c = 0 := by
  by_contra hc
  obtain ⟨y₀, hy₀⟩ := Algebra.trace_surjective (ZMod 2) K 1
  have := h (y₀ / c)
  rw [mul_div_cancel₀ _ hc, hy₀] at this
  exact one_ne_zero this

theorem exists_eq_trace_mul (f : K →ₗ[ZMod 2] ZMod 2) :
    ∃ δ : K, ∀ y, f y = Algebra.trace (ZMod 2) K (δ * y) := by
  obtain ⟨δ, hδ⟩ :=
    ((Algebra.traceForm (ZMod 2) K).toDual (traceForm_nondegenerate (ZMod 2) K)).surjective f
  refine ⟨δ, fun y => ?_⟩
  have := LinearMap.congr_fun hδ y
  simpa [LinearMap.BilinForm.toDual_def] using this.symm

theorem exists_ne_zero_trace_mul_eq_zero_of_ne_top {H : AddSubgroup K} (hH : H ≠ ⊤) :
    ∃ β : K, β ≠ 0 ∧ ∀ y ∈ H, Algebra.trace (ZMod 2) K (β * y) = 0 := by
  let p : Submodule (ZMod 2) K := AddSubgroup.toZModSubmodule 2 H
  have hp : p < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hH (eq_top_iff.mpr fun y _ => ?_)
    have hy : y ∈ p := h ▸ Submodule.mem_top
    exact hy
  obtain ⟨f, hf0, hpf⟩ := Submodule.exists_le_ker_of_lt_top p hp
  obtain ⟨β, hβ⟩ := exists_eq_trace_mul f
  refine ⟨β, fun h0 => hf0 (LinearMap.ext fun y => ?_), fun y hy => ?_⟩
  · rw [hβ, h0, zero_mul, map_zero, LinearMap.zero_apply]
  · rw [← hβ]
    exact hpf (show y ∈ p from hy)

end Trace

end SzRadical

section Form

variable [CharP K 2] {a : ℕ}

theorem szCommMap_add_right (γ : K) (x y y' : K × K × K) :
    szCommMap a γ x (y + y') = szCommMap a γ x y + szCommMap a γ x y' := by
  simp only [szCommMap, Prod.fst_add, Prod.snd_add]
  have h1 : (y.1 + y'.1) ^ 2 ^ (a + 1) = y.1 ^ 2 ^ (a + 1) + y'.1 ^ 2 ^ (a + 1) :=
    SzRadical.frob_add _ _ _
  have h2 : (x.1 * (y.2.1 + y'.2.1)) ^ 2 ^ a = (x.1 * y.2.1) ^ 2 ^ a + (x.1 * y'.2.1) ^ 2 ^ a := by
    rw [mul_add, SzRadical.frob_add]
  have h3 : ((y.1 + y'.1) * x.2.1) ^ 2 ^ a = (y.1 * x.2.1) ^ 2 ^ a + (y'.1 * x.2.1) ^ 2 ^ a := by
    rw [add_mul, SzRadical.frob_add]
  rw [h1, h2, h3]
  ring

omit [CharP K 2] in
theorem szCommMap_comm (γ : K) (x y : K × K × K) : szCommMap a γ x y = szCommMap a γ y x := by
  simp only [szCommMap]
  ring

theorem szCommMap_add_left (γ : K) (x x' y : K × K × K) :
    szCommMap a γ (x + x') y = szCommMap a γ x y + szCommMap a γ x' y := by
  rw [szCommMap_comm, szCommMap_add_right, szCommMap_comm γ y x, szCommMap_comm γ y x']

theorem szCommMap_zero_right (γ : K) (x : K × K × K) : szCommMap a γ x 0 = 0 := by
  have h := szCommMap_add_right (a := a) γ x 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem eq_zero_of_forall_szCommMap_eq_zero [Fintype K] (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {γ : K} {x : K × K × K}
    (h : ∀ y ∈ szCoordSpace K, szCommMap a γ x y = 0) : x = 0 := by
  classical
  have z1 : (0 : K) ^ 2 ^ (a + 1) = 0 := zero_pow (SzRadical.two_pow_ne_zero _)
  have z2 : (0 : K) ^ 2 ^ a = 0 := zero_pow (SzRadical.two_pow_ne_zero _)
  obtain ⟨x₁, x₂, x₃⟩ := x
  have hx₂ : x₂ = 0 := by
    have := h (0, 0, 1) (Or.inr rfl)
    simpa [szCommMap, z1, z2] using this
  subst hx₂
  have hfst : ∀ s : K, x₁ * s ^ 2 ^ (a + 1) + x₁ ^ 2 ^ (a + 1) * s = 0 := by
    intro s
    have := h (s, 0, 0) (Or.inl rfl)
    simpa [szCommMap, z1, z2] using this
  have hx₁ : x₁ = 0 := by
    have h1 := hfst 1
    rw [one_pow, mul_one, mul_one, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h1
    rcases SzRadical.eq_zero_or_eq_one_of_pow_theta_eq hK h1.symm with h0 | h0
    · exact h0
    · exfalso
      subst h0
      have hall : ∀ s : K, s = 0 ∨ s = 1 := fun s => by
        have := hfst s
        rw [one_mul, one_pow, one_mul, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at this
        exact SzRadical.eq_zero_or_eq_one_of_pow_theta_eq hK this
      have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun s _ => by
        rcases hall s with hs | hs <;> simp [hs]
      have h4 := (Finset.card_le_card hsub).trans Finset.card_le_two
      rw [Finset.card_univ, hK] at h4
      have h5 : 2 ^ 2 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact absurd (h5.trans h4) (by norm_num)
  subst hx₁
  have hx₃ : x₃ = 0 := by
    have := h (0, 1, 0) (Or.inl rfl)
    simpa [szCommMap, z1, z2] using this
  subst hx₃
  rfl

end Form

namespace SzRadical

variable [CharP K 2]

omit [CharP K 2] in
theorem szCommMap_surjective_of_thd_eq_zero [Fintype K] {a : ℕ}
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {γ : K} (hγ : γ ≠ 0) {v : K × K × K} (hv : v ≠ 0)
    (he : v.2.2 = 0) (w : K) : ∃ y : K × K × K, y.2.2 = 0 ∧ szCommMap a γ v y = w := by
  obtain ⟨v₁, v₂, v₃⟩ := v
  simp only at he
  subst he
  have hσ0 : (0 : K) ^ 2 ^ a = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  obtain ⟨z, hz⟩ := exists_pow_sigma_eq hK (w / γ)
  by_cases h1 : v₁ = 0
  · subst h1
    have h2 : v₂ ≠ 0 := by
      rintro rfl
      exact hv rfl
    refine ⟨(z / v₂, 0, 0), rfl, ?_⟩
    simp only [szCommMap, zero_mul, zero_add, mul_zero, hσ0, add_zero]
    rw [div_mul_cancel₀ z h2, hz, mul_div_cancel₀ w hγ, zero_pow (pow_ne_zero _ two_ne_zero),
      zero_mul, zero_add]
  · refine ⟨(0, z / v₁, 0), rfl, ?_⟩
    simp only [szCommMap, zero_mul, add_zero, mul_zero, hσ0]
    rw [zero_pow (pow_ne_zero _ two_ne_zero), mul_zero, zero_add, mul_div_cancel₀ z h1, hz,
      mul_div_cancel₀ w hγ]

omit [CharP K 2] in
theorem szCommMap_surjective_of_fst_eq_zero_of_thd_eq_one {a : ℕ} (γ : K) (r w : K) :
    ∃ y : K × K × K, y.2.2 = 0 ∧ szCommMap a γ (0, r, 1) y = w := by
  refine ⟨(0, w, 0), rfl, ?_⟩
  have hσ0 : (0 : K) ^ 2 ^ a = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  simp only [szCommMap, zero_mul, mul_zero, hσ0, add_zero, zero_add, one_mul]

omit [CharP K 2] in
theorem szCommMap_szTorusSmul [Fintype K] {a : ℕ} (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (γ l : K) (x y : K × K × K) :
    szCommMap a γ (szTorusSmul a l x) (szTorusSmul a l y) =
      l ^ (2 ^ (a + 1) + 1) * szCommMap a γ x y := by
  have key : (l * l ^ (2 ^ (a + 1) + 1)) ^ 2 ^ a = l ^ (2 ^ (a + 1) + 1) := by
    rw [← pow_succ', ← pow_mul, show (2 ^ (a + 1) + 1 + 1) * 2 ^ a = 2 ^ (2 * a + 1) + 2 ^ (a + 1)
      by ring, pow_add, ← hK, FiniteField.pow_card]
    ring
  have k3 : ∀ u v : K, (l * u * (l ^ (2 ^ (a + 1) + 1) * v)) ^ 2 ^ a =
      l ^ (2 ^ (a + 1) + 1) * (u * v) ^ 2 ^ a := by
    intro u v
    rw [show l * u * (l ^ (2 ^ (a + 1) + 1) * v) = (l * l ^ (2 ^ (a + 1) + 1)) * (u * v) by ring,
      mul_pow, key]
  simp only [szCommMap, szTorusSmul]
  rw [k3, k3, mul_pow, mul_pow]
  ring

omit [CharP K 2] in
theorem szTorusSmul_szTorusSmul (a : ℕ) (l m : K) (x : K × K × K) :
    szTorusSmul a l (szTorusSmul a m x) = szTorusSmul a (l * m) x := by
  simp only [szTorusSmul, mul_pow]
  ext <;> simp only <;> ring

theorem szTorusSmul_mem {a : ℕ} (l : K) {x : K × K × K} (hx : x ∈ szCoordSpace K) :
    szTorusSmul a l x ∈ szCoordSpace K :=
  hx

theorem sum_szTorusSmul [Fintype K] [DecidableEq K] {a : ℕ} (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (x : K × K × K) :
    ∑ l : Kˣ, szTorusSmul a (l : K) x = (0, 0, x.2.2) := by
  have hq : 7 ≤ Fintype.card K - 1 := by
    rw [hK]
    have : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hs1 : ∑ l : Kˣ, (l : K) = 0 := by
    have h := FiniteField.sum_pow_units (K := K) 1
    simp only [pow_one] at h
    rw [h, ite_eq_right_iff]
    intro hd
    exfalso
    have := Nat.le_of_dvd one_pos hd
    omega
  have hs2 : ∑ l : Kˣ, (l : K) ^ (2 ^ (a + 1) + 1) = 0 := by
    have h := FiniteField.sum_pow_units (K := K) (2 ^ (a + 1) + 1)
    rw [h, ite_eq_right_iff]
    intro hd
    exfalso
    have hlt : 2 ^ (a + 1) + 1 < Fintype.card K - 1 := by
      rw [hK]
      have h1 : 2 ^ (a + 1) * 2 ≤ 2 ^ (2 * a + 1) := by
        rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ≤ 2 ^ (a + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have := Nat.le_of_dvd (by positivity) hd
    omega
  have hcard : (Fintype.card Kˣ : K) = 1 := by
    rw [Fintype.card_units, hK, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_one, Nat.cast_pow,
      Nat.cast_ofNat, CharTwo.two_eq_zero, zero_pow (by omega), zero_sub, CharTwo.neg_eq]
  obtain ⟨x₁, x₂, x₃⟩ := x
  simp only [szTorusSmul]
  ext
  · simp only [Prod.fst_sum]
    rw [← Finset.sum_mul, hs1, zero_mul]
  · simp only [Prod.snd_sum, Prod.fst_sum]
    rw [← Finset.sum_mul, hs2, zero_mul]
  · simp only [Prod.snd_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, one_mul]

theorem isSzRad_szTorusSmul [Fintype K] {a : ℕ} (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {γ l : K} (hl : l ≠ 0) {x : K × K × K} (hx : IsSzRad a γ x) :
    IsSzRad a γ (szTorusSmul a l x) := by
  obtain ⟨w, hw⟩ := hx
  refine ⟨l ^ (2 ^ (a + 1) + 1) * w, fun y hy hyw => ?_⟩
  have hy' : szTorusSmul a l (szTorusSmul a l⁻¹ y) = y := by
    rw [szTorusSmul_szTorusSmul, mul_inv_cancel₀ hl]
    simp [szTorusSmul]
  rw [← hy', szCommMap_szTorusSmul hK] at hyw
  have hl' : l ^ (2 ^ (a + 1) + 1) ≠ 0 := pow_ne_zero _ hl
  exact hw _ (szTorusSmul_mem _ hy) (mul_left_cancel₀ hl' hyw)

theorem thd_eq_one_and_fst_ne_zero_of_isSzRad [Fintype K] {a : ℕ}
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {γ : K} (hγ : γ ≠ 0) {x : K × K × K}
    (hxV : x ∈ szCoordSpace K) (hx0 : x ≠ 0) (hx : IsSzRad a γ x) : x.2.2 = 1 ∧ x.1 ≠ 0 := by
  obtain ⟨w, hw⟩ := hx
  rcases hxV with h0 | h1
  · exfalso
    obtain ⟨y, hy, hyw⟩ := szCommMap_surjective_of_thd_eq_zero hK hγ hx0 h0 w
    exact hw y (Or.inl hy) hyw
  · refine ⟨h1, fun hx1 => ?_⟩
    obtain ⟨x₁, x₂, x₃⟩ := x
    simp only at h1 hx1
    subst h1; subst hx1
    obtain ⟨y, hy, hyw⟩ := szCommMap_surjective_of_fst_eq_zero_of_thd_eq_one (a := a) γ x₂ w
    exact hw y (Or.inl hy) hyw

theorem isSzRad_map {a : ℕ} {γ : K} (α : szCoordSpace K ≃+ szCoordSpace K) (h : K ≃+ K)
    (hB : ∀ x y : szCoordSpace K, szCommMap a γ (α x) (α y) = h (szCommMap a γ x y))
    (x : szCoordSpace K) (hx : IsSzRad a γ x) : IsSzRad a γ (α x) := by
  obtain ⟨w, hw⟩ := hx
  refine ⟨h w, fun y hy hyw => ?_⟩
  have e : α (α.symm ⟨y, hy⟩) = ⟨y, hy⟩ := α.apply_symm_apply _
  have := hB x (α.symm ⟨y, hy⟩)
  rw [e] at this
  exact hw _ (α.symm ⟨y, hy⟩).2 (h.injective (this.symm.trans hyw))

section TraceRadical

variable [Fintype K] [Algebra (ZMod 2) K]

theorem exists_trace_of_isSzRad {a : ℕ} {γ : K} {x : K × K × K} (hx : IsSzRad a γ x) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ y ∈ szCoordSpace K, Algebra.trace (ZMod 2) K (μ * szCommMap a γ x y) = 0 := by
  let f : szCoordSpace K →+ K :=
    { toFun := fun y => szCommMap a γ x y
      map_zero' := szCommMap_zero_right γ x
      map_add' := fun y y' => szCommMap_add_right γ x y y' }
  have hne : f.range ≠ ⊤ := by
    obtain ⟨w, hw⟩ := hx
    intro htop
    have hw' : w ∈ f.range := htop ▸ AddSubgroup.mem_top w
    obtain ⟨y, hy⟩ := hw'
    exact hw y y.2 hy
  obtain ⟨μ, hμ, hμH⟩ := exists_ne_zero_trace_mul_eq_zero_of_ne_top hne
  exact ⟨μ, hμ, fun y hy => hμH _ ⟨⟨y, hy⟩, rfl⟩⟩

theorem trace_szCommMap_vOne {a : ℕ} (hK : Fintype.card K = 2 ^ (2 * a + 1))
    {γ : K} (hγ : γ ≠ 0) (y : K × K × K) (hy : y.2.2 = 0 ∨ y.2.2 = 1) :
    Algebra.trace (ZMod 2) K
      (szCommMap a γ (γ⁻¹ ^ 2 ^ (a + 1), γ⁻¹ ^ (2 ^ (a + 1) + 1) + γ⁻¹ ^ (2 ^ (a + 1) + 2), 1) y) =
      0 := by
  obtain ⟨y₁, y₂, y₃⟩ := y
  simp only at hy
  set δ : K := γ⁻¹ with hδ
  set r : K := δ ^ (2 ^ (a + 1) + 1) + δ ^ (2 ^ (a + 1) + 2) with hr
  have hγδ : γ * δ = 1 := mul_inv_cancel₀ hγ
  have e1 : γ ^ 2 ^ (a + 1) * δ ^ (2 ^ (a + 1) + 1) = δ := by
    rw [pow_add δ (2 ^ (a + 1)) 1, pow_one, ← mul_assoc, ← mul_pow, hγδ, one_pow, one_mul]
  have e2 : γ ^ 2 ^ (a + 1) * δ ^ (2 ^ (a + 1) + 2) = δ ^ 2 := by
    rw [pow_add δ (2 ^ (a + 1)) 2, ← mul_assoc, ← mul_pow, hγδ, one_pow, one_mul]
  have e3 : (δ ^ (2 ^ (a + 1) + 1)) ^ 2 ^ (a + 1) = δ ^ (2 ^ (a + 1) + 2) := by
    rw [pow_add δ (2 ^ (a + 1)) 1, pow_one, mul_pow, pow_theta_pow_theta hK,
      pow_add δ (2 ^ (a + 1)) 2, mul_comm]
  set tr := Algebra.trace (ZMod 2) K with htr
  have h1 : tr (δ ^ 2 ^ (a + 1) * y₁ ^ 2 ^ (a + 1)) = tr (δ * y₁) := by
    rw [← mul_pow, htr, trace_pow_two_pow]
  have h2 : (δ ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) * y₁ = δ ^ 2 * y₁ := by
    rw [pow_theta_pow_theta hK]
  have h3 : tr (γ * (δ ^ 2 ^ (a + 1) * y₂) ^ 2 ^ a) = tr y₂ := by
    rw [mul_pow, pow_theta_pow_sigma hK, ← mul_assoc, hγδ, one_mul, htr, trace_pow_two_pow]
  have h4 : tr (γ * (y₁ * r) ^ 2 ^ a) = tr (y₁ * δ) + tr (y₁ * δ ^ 2) := by
    rw [htr, ← trace_pow_two_pow (γ * (y₁ * r) ^ 2 ^ a) (a + 1), mul_pow, pow_sigma_pow_theta hK,
      ← map_add]
    congr 1
    rw [hr]
    linear_combination y₁ * e1 + y₁ * e2
  have h5 : tr r = 0 := by
    rw [hr, map_add, ← e3, htr, trace_pow_two_pow, ← two_mul]
    exact mul_eq_zero_of_left (by decide) _
  have hsplit : szCommMap a γ (δ ^ 2 ^ (a + 1), r, 1) (y₁, y₂, y₃) =
      δ ^ 2 ^ (a + 1) * y₁ ^ 2 ^ (a + 1) + (δ ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) * y₁ +
        γ * (δ ^ 2 ^ (a + 1) * y₂) ^ 2 ^ a + γ * (y₁ * r) ^ 2 ^ a + y₂ + y₃ * r := by
    simp only [szCommMap]
    ring
  rw [hsplit, h2]
  simp only [map_add]
  rw [h1, h3, h4]
  have h6 : tr (y₃ * r) = 0 := by
    rcases hy with h0 | h0 <;> rw [h0]
    · rw [zero_mul, map_zero]
    · rw [one_mul, h5]
  rw [h6, mul_comm y₁ δ, mul_comm y₁ (δ ^ 2)]
  have h2z : (2 : ZMod 2) = 0 := rfl
  linear_combination (tr (δ * y₁) + tr (δ ^ 2 * y₁) + tr y₂) * h2z

theorem coeff_snd {a : ℕ} (hK : Fintype.card K = 2 ^ (2 * a + 1)) {γ μ : K} {x : K × K × K}
    (hx3 : x.2.2 = 1)
    (h : ∀ y ∈ szCoordSpace K, Algebra.trace (ZMod 2) K (μ * szCommMap a γ x y) = 0) :
    (μ * γ) ^ 2 ^ (a + 1) * x.1 = μ := by
  have z1 : (0 : K) ^ 2 ^ (a + 1) = 0 := zero_pow (two_pow_ne_zero _)
  have z2 : (0 : K) ^ 2 ^ a = 0 := zero_pow (two_pow_ne_zero _)
  have key : ∀ r : K, Algebra.trace (ZMod 2) K (((μ * γ) ^ 2 ^ (a + 1) * x.1 + μ) * r) = 0 := by
    intro r
    have h0 := h (0, r, 0) (Or.inl rfl)
    have hrB : szCommMap a γ x (0, r, 0) = γ * (x.1 * r) ^ 2 ^ a + r := by
      simp only [szCommMap, hx3, z1, z2, zero_mul, mul_zero, one_mul, add_zero, zero_add]
    rw [hrB, mul_add, map_add] at h0
    have e : Algebra.trace (ZMod 2) K (μ * (γ * (x.1 * r) ^ 2 ^ a)) =
        Algebra.trace (ZMod 2) K ((μ * γ) ^ 2 ^ (a + 1) * x.1 * r) := by
      rw [← trace_pow_two_pow (μ * (γ * (x.1 * r) ^ 2 ^ a)) (a + 1)]
      congr 1
      rw [show μ * (γ * (x.1 * r) ^ 2 ^ a) = (μ * γ) * (x.1 * r) ^ 2 ^ a by ring, mul_pow,
        pow_sigma_pow_theta hK]
      ring
    rw [e] at h0
    rw [add_mul, map_add]
    exact h0
  have hz := eq_zero_of_forall_trace_mul_eq_zero key
  rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hz

theorem coeff_fst {a : ℕ} (hK : Fintype.card K = 2 ^ (2 * a + 1)) {γ μ : K} {x : K × K × K}
    (h : ∀ y ∈ szCoordSpace K, Algebra.trace (ZMod 2) K (μ * szCommMap a γ x y) = 0) :
    (μ * x.1) ^ 2 ^ a + μ * x.1 ^ 2 ^ (a + 1) + (μ * γ) ^ 2 ^ (a + 1) * x.2.1 = 0 := by
  have z2 : (0 : K) ^ 2 ^ a = 0 := zero_pow (two_pow_ne_zero _)
  refine eq_zero_of_forall_trace_mul_eq_zero fun s => ?_
  have h0 := h (s, 0, 0) (Or.inl rfl)
  have hrB : szCommMap a γ x (s, 0, 0) =
      x.1 * s ^ 2 ^ (a + 1) + x.1 ^ 2 ^ (a + 1) * s + γ * (s * x.2.1) ^ 2 ^ a := by
    simp only [szCommMap, z2, zero_mul, mul_zero, add_zero, zero_add]
  rw [hrB, mul_add, mul_add, map_add, map_add] at h0
  have e1 : Algebra.trace (ZMod 2) K (μ * (x.1 * s ^ 2 ^ (a + 1))) =
      Algebra.trace (ZMod 2) K ((μ * x.1) ^ 2 ^ a * s) := by
    rw [← trace_pow_two_pow (μ * (x.1 * s ^ 2 ^ (a + 1))) a]
    congr 1
    rw [show μ * (x.1 * s ^ 2 ^ (a + 1)) = (μ * x.1) * s ^ 2 ^ (a + 1) by ring, mul_pow,
      pow_theta_pow_sigma hK]
  have e3 : Algebra.trace (ZMod 2) K (μ * (γ * (s * x.2.1) ^ 2 ^ a)) =
      Algebra.trace (ZMod 2) K ((μ * γ) ^ 2 ^ (a + 1) * x.2.1 * s) := by
    rw [← trace_pow_two_pow (μ * (γ * (s * x.2.1) ^ 2 ^ a)) (a + 1)]
    congr 1
    rw [show μ * (γ * (s * x.2.1) ^ 2 ^ a) = (μ * γ) * (s * x.2.1) ^ 2 ^ a by ring, mul_pow,
      pow_sigma_pow_theta hK]
    ring
  rw [e1, e3] at h0
  rw [add_mul, add_mul, map_add, map_add, show μ * x.1 ^ 2 ^ (a + 1) * s =
    μ * (x.1 ^ 2 ^ (a + 1) * s) by ring]
  exact h0

@[expose] def vOne (a : ℕ) (γ : K) : K × K × K :=
  (γ⁻¹ ^ 2 ^ (a + 1), γ⁻¹ ^ (2 ^ (a + 1) + 1) + γ⁻¹ ^ (2 ^ (a + 1) + 2), 1)

theorem isSzRad_vOne {a : ℕ} (hK : Fintype.card K = 2 ^ (2 * a + 1)) {γ : K} (hγ : γ ≠ 0) :
    IsSzRad a γ (vOne a γ) := by
  obtain ⟨w, hw⟩ := Algebra.trace_surjective (ZMod 2) K 1
  refine ⟨w, fun y hy hyw => ?_⟩
  have h0 := trace_szCommMap_vOne hK hγ y hy
  rw [show (γ⁻¹ ^ 2 ^ (a + 1), γ⁻¹ ^ (2 ^ (a + 1) + 1) + γ⁻¹ ^ (2 ^ (a + 1) + 2), (1 : K)) =
    vOne a γ from rfl, hyw, hw] at h0
  exact one_ne_zero h0

theorem eq_of_isSzRad {a : ℕ} (hK : Fintype.card K = 2 ^ (2 * a + 1)) {γ : K} (hγ : γ ≠ 0)
    {x x' : K × K × K} (hx : IsSzRad a γ x) (hx' : IsSzRad a γ x') (h3 : x.2.2 = 1)
    (h3' : x'.2.2 = 1) (h1 : x.1 = x'.1) : x = x' := by
  obtain ⟨μ, hμ, hμx⟩ := exists_trace_of_isSzRad hx
  obtain ⟨μ', hμ', hμx'⟩ := exists_trace_of_isSzRad hx'
  have c1 := coeff_snd hK h3 hμx
  have c1' := coeff_snd hK h3' hμx'
  set ν := μ' / μ with hν
  have hμν : μ' = ν * μ := by rw [hν, div_mul_cancel₀ _ hμ]
  have hνθ : ν ^ 2 ^ (a + 1) = ν := by
    have e : ν ^ 2 ^ (a + 1) * μ = ν * μ := by
      calc ν ^ 2 ^ (a + 1) * μ = ν ^ 2 ^ (a + 1) * ((μ * γ) ^ 2 ^ (a + 1) * x.1) := by rw [c1]
        _ = (μ' * γ) ^ 2 ^ (a + 1) * x'.1 := by rw [hμν, ← h1]; ring
        _ = ν * μ := by rw [c1', hμν]
    exact mul_right_cancel₀ hμ e
  have hν0 : ν ≠ 0 := div_ne_zero hμ' hμ
  have hν1 : ν = 1 := (eq_zero_or_eq_one_of_pow_theta_eq hK hνθ).resolve_left hν0
  have hμμ : μ' = μ := by rw [hμν, hν1, one_mul]
  subst hμμ
  have c2 := coeff_fst hK hμx
  have c2' := coeff_fst hK hμx'
  have hc : (μ' * γ) ^ 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ (mul_ne_zero hμ hγ)
  have h2 : x.2.1 = x'.2.1 := by
    have e : (μ' * γ) ^ 2 ^ (a + 1) * x.2.1 = (μ' * γ) ^ 2 ^ (a + 1) * x'.2.1 := by
      rw [← h1] at c2'
      have := c2.trans c2'.symm
      linear_combination this
    exact mul_left_cancel₀ hc e
  obtain ⟨x₁, x₂, x₃⟩ := x
  obtain ⟨y₁, y₂, y₃⟩ := x'
  simp only at h1 h2 h3 h3'
  rw [h1, h2, h3, h3']

theorem eq_szTorusSmul_vOne_of_isSzRad {a : ℕ} (hK : Fintype.card K = 2 ^ (2 * a + 1)) {γ : K}
    (hγ : γ ≠ 0) {x : K × K × K} (hxV : x ∈ szCoordSpace K) (hx0 : x ≠ 0) (hx : IsSzRad a γ x) :
    x = szTorusSmul a (x.1 * γ ^ 2 ^ (a + 1)) (vOne a γ) := by
  obtain ⟨h3, h1⟩ := thd_eq_one_and_fst_ne_zero_of_isSzRad hK hγ hxV hx0 hx
  have hl : x.1 * γ ^ 2 ^ (a + 1) ≠ 0 := mul_ne_zero h1 (pow_ne_zero _ hγ)
  refine eq_of_isSzRad hK hγ hx (isSzRad_szTorusSmul hK hl (isSzRad_vOne hK hγ)) h3 rfl ?_
  simp only [szTorusSmul, vOne]
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hγ, one_pow, mul_one]

theorem szRadical_fixed_of_ne_zero [DecidableEq K] {a : ℕ} (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {γ : K} (hγ : γ ≠ 0)
    (α : szCoordSpace K ≃+ szCoordSpace K) (h : K ≃+ K)
    (hB : ∀ x y : szCoordSpace K, szCommMap a γ (α x) (α y) = h (szCommMap a γ x y)) :
    α ⟨(0, 0, 1), Or.inr rfl⟩ = ⟨(0, 0, 1), Or.inr rfl⟩ := by
  let o : Kˣ → szCoordSpace K := fun l => ⟨szTorusSmul a (l : K) (vOne a γ), Or.inr rfl⟩
  have ho_rad : ∀ l : Kˣ, IsSzRad a γ (o l) := fun l =>
    isSzRad_szTorusSmul hK l.ne_zero (isSzRad_vOne hK hγ)
  have hvOne1 : (vOne a γ).1 ≠ 0 := pow_ne_zero _ (inv_ne_zero hγ)
  have ho_ne : ∀ l : Kˣ, (o l : K × K × K) ≠ 0 := by
    intro l hl
    have := congrArg Prod.fst hl
    simp only [o, szTorusSmul, Prod.fst_zero] at this
    exact mul_ne_zero l.ne_zero hvOne1 this
  have ho_inj : Function.Injective o := by
    intro l l' hll'
    have := congrArg (fun v : szCoordSpace K => (v : K × K × K).1) hll'
    simp only [o, szTorusSmul] at this
    exact Units.ext (mul_right_cancel₀ hvOne1 this)
  have hαo : ∀ l : Kˣ, ∃ l' : Kˣ, α (o l) = o l' := by
    intro l
    have hne : ((α (o l) : szCoordSpace K) : K × K × K) ≠ 0 := by
      intro h0
      have : α (o l) = 0 := Subtype.ext h0
      exact ho_ne l (by rw [α.map_eq_zero_iff.mp this]; rfl)
    have hrad := isSzRad_map α h hB _ (ho_rad l)
    have key := eq_szTorusSmul_vOne_of_isSzRad hK hγ (α (o l)).2 hne hrad
    obtain ⟨-, h1⟩ := thd_eq_one_and_fst_ne_zero_of_isSzRad hK hγ (α (o l)).2 hne hrad
    exact ⟨Units.mk0 ((α (o l) : K × K × K).1 * γ ^ 2 ^ (a + 1))
      (mul_ne_zero h1 (pow_ne_zero _ hγ)), Subtype.ext key⟩
  choose e he using hαo
  have he_inj : Function.Injective e := by
    intro l l' hll'
    apply ho_inj
    apply α.injective
    rw [he, he, hll']
  have he_bij : Function.Bijective e := Finite.injective_iff_bijective.mp he_inj
  have ht : (⟨(0, 0, 1), Or.inr rfl⟩ : szCoordSpace K) = ∑ l : Kˣ, o l := by
    apply Subtype.ext
    rw [AddSubgroup.val_finsetSum]
    exact (sum_szTorusSmul ha hK (vOne a γ)).symm
  rw [ht, map_sum]
  simp only [he]
  exact Function.Bijective.sum_comp he_bij o

end TraceRadical

omit [CharP K 2] in
theorem thd_eq_zero_of_isSzRad_zero [CharP K 2] {a : ℕ} {x : K × K × K}
    (hxV : x ∈ szCoordSpace K) (hx : IsSzRad a 0 x) : x.2.2 = 0 := by
  rcases hxV with h0 | h1
  · exact h0
  · exfalso
    obtain ⟨w, hw⟩ := hx
    apply hw (0, w, 0) (Or.inl rfl)
    have z1 : (0 : K) ^ 2 ^ (a + 1) = 0 := zero_pow (two_pow_ne_zero _)
    simp only [szCommMap, h1, z1, zero_mul, mul_zero, one_mul, add_zero, zero_add]

theorem isSzRad_fst_zero [Finite K] {a : ℕ} (s : K) : IsSzRad a 0 (s, 0, 0) := by
  let f : K → K := fun z => s * z ^ 2 ^ (a + 1) + s ^ 2 ^ (a + 1) * z
  have hval : ∀ y : K × K × K, szCommMap a 0 (s, 0, 0) y = f y.1 := by
    intro y
    simp only [szCommMap, f, zero_mul, mul_zero, add_zero]
  by_cases hs : s = 0
  · subst hs
    refine ⟨1, fun y _ hy => ?_⟩
    rw [hval] at hy
    have z1 : (0 : K) ^ 2 ^ (a + 1) = 0 := zero_pow (two_pow_ne_zero _)
    simp only [f, zero_mul, z1, add_zero] at hy
    exact zero_ne_one hy
  · have hninj : ¬ Function.Injective f := by
      intro hinj
      have h0 : f s = f 0 := by
        have z1 : (0 : K) ^ 2 ^ (a + 1) = 0 := zero_pow (two_pow_ne_zero _)
        simp only [f, z1, mul_zero, add_zero]
        rw [mul_comm, CharTwo.add_self_eq_zero]
      exact hs (hinj h0)
    have hnsurj : ¬ Function.Surjective f := fun hsurj =>
      hninj (Finite.injective_iff_surjective.mpr hsurj)
    obtain ⟨w, hw⟩ : ∃ w, ∀ z, f z ≠ w := by
      by_contra hcon
      push Not at hcon
      exact hnsurj hcon
    exact ⟨w, fun y _ hy => hw y.1 (by rw [← hval]; exact hy)⟩

theorem isSzRad_snd_zero [Fintype K] {a : ℕ} (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (r : K) : IsSzRad a 0 (0, r, 0) := by
  classical
  have hw : ∃ w : K, w ≠ 0 ∧ w ≠ r := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, r} := fun w _ => by
      by_cases hw0 : w = 0
      · simp [hw0]
      · simp [hcon w hw0]
    have h1 := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ, hK] at h1
    have h2 : 2 ^ 1 < 2 ^ (2 * a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨w, hw0, hwr⟩ := hw
  refine ⟨w, fun y hy hyw => ?_⟩
  have z1 : (0 : K) ^ 2 ^ (a + 1) = 0 := zero_pow (two_pow_ne_zero _)
  have hval : szCommMap a 0 (0, r, 0) y = y.2.2 * r := by
    simp only [szCommMap, z1, zero_mul, add_zero, zero_add]
  rw [hval] at hyw
  rcases hy with h0 | h1
  · rw [h0, zero_mul] at hyw; exact hw0 hyw.symm
  · rw [h1, one_mul] at hyw; exact hwr hyw.symm

theorem thd_map_eq_zero [Fintype K] {a : ℕ} (ha : 1 ≤ a) (hK : Fintype.card K = 2 ^ (2 * a + 1))
    (α : szCoordSpace K ≃+ szCoordSpace K) (h : K ≃+ K)
    (hB : ∀ x y : szCoordSpace K, szCommMap a 0 (α x) (α y) = h (szCommMap a 0 x y))
    (v : szCoordSpace K) (hv : (v : K × K × K).2.2 = 0) : (α v : K × K × K).2.2 = 0 := by
  obtain ⟨⟨v₁, v₂, v₃⟩, hvV⟩ := v
  simp only at hv
  subst hv
  let p : szCoordSpace K := ⟨(v₁, 0, 0), Or.inl rfl⟩
  let q : szCoordSpace K := ⟨(0, v₂, 0), Or.inl rfl⟩
  have hpq : (⟨(v₁, v₂, 0), hvV⟩ : szCoordSpace K) = p + q := by
    apply Subtype.ext
    simp [p, q]
  rw [hpq, map_add, AddSubgroup.coe_add, Prod.snd_add, Prod.snd_add,
    thd_eq_zero_of_isSzRad_zero (α p).2 (isSzRad_map α h hB p (isSzRad_fst_zero v₁)),
    thd_eq_zero_of_isSzRad_zero (α q).2 (isSzRad_map α h hB q (isSzRad_snd_zero ha hK v₂)),
    add_zero]

theorem szRadical_thd_of_eq_zero [Fintype K] {a : ℕ} (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (α : szCoordSpace K ≃+ szCoordSpace K) (h : K ≃+ K)
    (hB : ∀ x y : szCoordSpace K, szCommMap a 0 (α x) (α y) = h (szCommMap a 0 x y)) :
    ((α ⟨(0, 0, 1), Or.inr rfl⟩ : szCoordSpace K) : K × K × K).2.2 = 1 := by
  rcases (α ⟨(0, 0, 1), Or.inr rfl⟩).2 with h0 | h1
  · exfalso
    have hB' : ∀ x y : szCoordSpace K,
        szCommMap a 0 (α.symm x) (α.symm y) = h.symm (szCommMap a 0 x y) := by
      intro x y
      have := hB (α.symm x) (α.symm y)
      rw [α.apply_symm_apply, α.apply_symm_apply] at this
      rw [this, h.symm_apply_apply]
    have := thd_map_eq_zero ha hK α.symm h.symm hB' _ h0
    rw [α.symm_apply_apply] at this
    exact one_ne_zero this
  · exact h1

end SzRadical

theorem szRadical_fixed [CharP K 2] [Fintype K] {a : ℕ} (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (γ : K)
    (α : szCoordSpace K ≃+ szCoordSpace K) (h : K ≃+ K)
    (hB : ∀ x y : szCoordSpace K, szCommMap a γ (α x) (α y) = h (szCommMap a γ x y)) :
    ((α ⟨(0, 0, 1), Or.inr rfl⟩ : szCoordSpace K) : K × K × K).2.2 = 1 ∧
      (γ ≠ 0 → α ⟨(0, 0, 1), Or.inr rfl⟩ = ⟨(0, 0, 1), Or.inr rfl⟩) := by
  classical
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  by_cases hγ : γ = 0
  · subst hγ
    exact ⟨SzRadical.szRadical_thd_of_eq_zero ha hK α h hB, fun h0 => absurd rfl h0⟩
  · have hfix := SzRadical.szRadical_fixed_of_ne_zero ha hK hγ α h hB
    refine ⟨?_, fun _ => hfix⟩
    rw [hfix]

end CFSG.SeitzReduction.RankOne
