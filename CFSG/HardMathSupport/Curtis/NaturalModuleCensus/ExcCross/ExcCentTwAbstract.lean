module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcCentAbstract
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.HardMathSupport.Curtis.UnitaryLevi
  (lift_mem_centralizer cube_of_conj eightyOne_dvd_of_ker_range nine_dvd_card_of_two)

section Mact

variable {C : Type} [CommGroup C] {r : ℕ}

theorem prod_zpow_sum_ab {ι : Type*} (s : Finset ι) (a : C) (c : ι → ℤ) :
    ∏ j ∈ s, a ^ c j = a ^ ∑ j ∈ s, c j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, zpow_add, ih]

@[expose] def mactC (M : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → C) : Fin r → C :=
  fun k => ∏ j, t j ^ M k j

theorem mactC_one (t : Fin r → C) : mactC (1 : Matrix (Fin r) (Fin r) ℤ) t = t := by
  ext1 k
  simp [mactC, Matrix.one_apply, Finset.prod_ite_eq]

theorem mactC_mul (M N : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → C) :
    mactC (M * N) t = mactC M (mactC N t) := by
  ext1 k
  simp only [mactC, Matrix.mul_apply, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← prod_zpow_sum_ab]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem mactC_add (M N : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → C) :
    mactC (M + N) t = mactC M t * mactC N t := by
  ext1 k
  simp [mactC, zpow_add, Finset.prod_mul_distrib]

theorem mactC_mul_apply (M : Matrix (Fin r) (Fin r) ℤ) (s t : Fin r → C) :
    mactC M (s * t) = mactC M s * mactC M t := by
  ext1 k
  simp [mactC, mul_zpow, Finset.prod_mul_distrib]

theorem mactC_one_vec (M : Matrix (Fin r) (Fin r) ℤ) : mactC M (1 : Fin r → C) = 1 := by
  ext1 k
  simp [mactC]

theorem mactC_neg (M : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → C) :
    mactC (-M) t = (mactC M t)⁻¹ := by
  ext1 k
  simp [mactC, Finset.prod_inv_distrib]

theorem mactC_sub (M N : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → C) :
    mactC (M - N) t = mactC M t * (mactC N t)⁻¹ := by
  rw [sub_eq_add_neg, mactC_add, mactC_neg]

theorem mactC_one_sub (X : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → C) :
    mactC (1 - X) t = t * (mactC X t)⁻¹ := by
  rw [mactC_sub, mactC_one]

theorem mactC_smul_one (c : ℤ) (t : Fin r → C) :
    mactC (c • (1 : Matrix (Fin r) (Fin r) ℤ)) t = t ^ c := by
  ext1 k
  simp [mactC, Matrix.smul_apply, Matrix.one_apply, Finset.prod_ite_eq]

@[expose] def mactCHom (M : Matrix (Fin r) (Fin r) ℤ) : (Fin r → C) →* (Fin r → C) where
  toFun := mactC M
  map_one' := mactC_one_vec M
  map_mul' := mactC_mul_apply M

@[simp] theorem mactCHom_apply (M : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → C) :
    mactCHom M t = mactC M t := rfl

@[expose] def vecTC (w : Fin r → ℤ) (g : C) : Fin r → C := fun i => g ^ w i

theorem mactC_vecTC (M : Matrix (Fin r) (Fin r) ℤ) (w : Fin r → ℤ) (g : C) :
    mactC M (vecTC w g) = vecTC (M.mulVec w) g := by
  ext1 k
  simp only [mactC, vecTC, ← zpow_mul, Matrix.mulVec, dotProduct]
  rw [← prod_zpow_sum_ab]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem vecTC_eq_of_dvd (w w' : Fin r → ℤ) (ω : C) (hω : orderOf ω = 3)
    (h : ∀ i, (3 : ℤ) ∣ w i - w' i) : vecTC w ω = vecTC w' ω := by
  ext1 k
  simp only [vecTC]
  rw [zpow_eq_zpow_iff_modEq, hω]
  exact (Int.modEq_iff_dvd.2 (by simpa using (h k))).symm

theorem vecTC_pow_three (c : Fin r → ℤ) (ω : C) (hω : orderOf ω = 3) : vecTC c ω ^ 3 = 1 := by
  ext1 k
  simp only [vecTC, Pi.pow_apply, Pi.one_apply]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hω, pow_orderOf_eq_one,
    one_zpow]

theorem nine_dvd_of_vecTC (H : Subgroup (Fin r → C)) (ω : C) (hω : orderOf ω = 3)
    (c₁ c₂ : Fin r → ℤ) (p₁ p₂ : Fin r) (h11 : c₁ p₁ = 1) (_h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0)
    (h22 : c₂ p₂ = 1) (m₁ : vecTC c₁ ω ∈ H) (m₂ : vecTC c₂ ω ∈ H) : 9 ∣ Nat.card H := by
  have hne : ω ≠ 1 := by
    intro h; rw [h, orderOf_one] at hω; omega
  have o₁ : orderOf (vecTC c₁ ω) = 3 := by
    refine orderOf_eq_prime (vecTC_pow_three c₁ ω hω) ?_
    intro h
    have := congrFun h p₁
    simp [vecTC, h11] at this
    exact hne this
  refine nine_dvd_card_of_two H (fun a _ b _ => mul_comm a b) m₁ m₂ o₁
    (vecTC_pow_three c₂ ω hω) ?_
  rintro ⟨k, hk⟩
  have e1 := congrFun hk p₂
  simp [vecTC, h21, h22] at e1
  exact hne e1.symm

end Mact

section Main

variable {G : Type} [Group G] {W : Type} [Group W] {r : ℕ} {C : Type} [CommGroup C]
variable (ι : (Fin r → C) →* G) (π : G →* W) (A : W → Matrix (Fin r) (Fin r) ℤ)
variable (hι : Function.Injective ι)
  (hker : ∀ g : G, π g = 1 → g ∈ ι.range) (hιπ : ∀ t, π (ι t) = 1)
  (hconj : ∀ (g : G) (t : Fin r → C), g * ι t * g⁻¹ = ι (mactC (A (π g)) t))

include hι hιπ hconj in
theorem eightyOne_dvd_of_pair_ab (x y : W) (s c : G) (hs : π s = x)
    (hc : c ∈ Subgroup.centralizer ({s} : Set G)) (hcy : π c = y)
    (ω : C) (hω : orderOf ω = 3) (c₁ c₂ : Fin r → ℤ) (p₁ p₂ : Fin r)
    (hf₁ : ∀ i, (3 : ℤ) ∣ ((A x).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i, (3 : ℤ) ∣ ((A x).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : 9 ∣ Nat.card (Subgroup.closure ({x, y} : Set W))) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) := by
  set D := Subgroup.centralizer ({s} : Set G) with hD
  refine eightyOne_dvd_of_ker_range π D ?_ ?_
  · set Fix : Subgroup (Fin r → C) := (mactCHom (C := C) (1 - A x)).ker with hFix
    have hfixmem : ∀ t, t ∈ Fix ↔ mactC (A x) t = t := by
      intro t
      rw [hFix, MonoidHom.mem_ker, mactCHom_apply, mactC_one_sub, mul_inv_eq_one, eq_comm]
    have hfixc : ∀ c' : Fin r → ℤ, (∀ i, (3 : ℤ) ∣ ((A x).mulVec c') i - c' i) →
        vecTC c' ω ∈ Fix := by
      intro c' hc'
      rw [hfixmem, mactC_vecTC]
      exact vecTC_eq_of_dvd _ _ ω hω hc'
    have h9 : 9 ∣ Nat.card Fix :=
      nine_dvd_of_vecTC Fix ω hω c₁ c₂ p₁ p₂ h11 h12 h21 h22 (hfixc c₁ hf₁) (hfixc c₂ hf₂)
    have hle : Fix.map ι ≤ D ⊓ π.ker := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨?_, hιπ t⟩
      show ι t ∈ D
      rw [hD, Subgroup.mem_centralizer_singleton_iff]
      have := hconj s t
      rw [hs, (hfixmem t).1 ht] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [← Subgroup.card_map_of_injective hι] at h9
    exact h9.trans (Subgroup.card_dvd_of_le hle)
  · have hle : Subgroup.closure ({x, y} : Set W) ≤ D.map π := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨s, Subgroup.mem_centralizer_singleton_iff.2 rfl, hs⟩
      · exact ⟨c, hc, hcy⟩
    exact hQ.trans (Subgroup.card_dvd_of_le hle)

include hker in
theorem exists_decomp_ab {s gx : G} (h : π s = π gx) : ∃ t, s = ι t * gx := by
  have h1 : π (s * gx⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨t, ht⟩ := hker _ h1
  exact ⟨t, by rw [ht]; exact (inv_mul_cancel_right s gx).symm⟩

include hιπ hconj in
theorem lift_centralizer_of_solve_ab {s gx gy : G} (h u a : Fin r → C) (hs : s = ι h * gx)
    (hu : gy * gx * gy⁻¹ = ι u * gx)
    (ha : a * (mactC (A (π gx)) a)⁻¹ = h * (mactC (A (π gy)) h)⁻¹ * u⁻¹) :
    ι a * gy ∈ Subgroup.centralizer ({s} : Set G) ∧ π (ι a * gy) = π gy := by
  refine ⟨lift_mem_centralizer ι (mactCHom (C := C) (A (π gx))) (mactCHom (C := C) (A (π gy)))
    gx gy s h u a hs (fun t => hconj gx t) (fun t => hconj gy t) hu ha, ?_⟩
  rw [map_mul, hιπ, one_mul]

include hι hker hιπ hconj in
theorem caseA_ab (x y : W) (s gx gy : G)
    (hs : π s = x) (hgx : π gx = x) (hgy : π gy = y)
    (hcomm : gy * gx = gx * gy) (hgx3 : gx ^ 3 = 1) (hs3 : s ^ 3 = 1)
    (Φ Ψ : Matrix (Fin r) (Fin r) ℤ)
    (hid : 1 - A y = (1 - A x) * Φ + Ψ * (1 + A x + A x * A x))
    (ω : C) (hω : orderOf ω = 3) (c₁ c₂ : Fin r → ℤ) (p₁ p₂ : Fin r)
    (hf₁ : ∀ i, (3 : ℤ) ∣ ((A x).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i, (3 : ℤ) ∣ ((A x).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : 9 ∣ Nat.card (Subgroup.closure ({x, y} : Set W))) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) := by
  obtain ⟨h, hsh⟩ := exists_decomp_ab ι π hker (hs.trans hgx.symm)
  have hcube := cube_of_conj ι (mactCHom (C := C) (A x)) gx h
    (fun t => by have := hconj gx t; rwa [hgx] at this) hgx3
  rw [← hsh, hs3, ← map_one ι] at hcube
  have hN : mactC (1 + A x + A x * A x) h = 1 := by
    have := hι hcube
    rw [mactC_add, mactC_add, mactC_one, mactC_mul]
    simpa [mactCHom_apply, mul_assoc] using this.symm
  have ha : mactC Φ h * (mactC (A x) (mactC Φ h))⁻¹ =
      h * (mactC (A y) h)⁻¹ * (1 : Fin r → C)⁻¹ := by
    have h1 : mactC (1 - A y) h = h * (mactC (A y) h)⁻¹ := mactC_one_sub (A y) h
    have h2 : mactC (1 - A x) (mactC Φ h) = mactC Φ h * (mactC (A x) (mactC Φ h))⁻¹ :=
      mactC_one_sub (A x) _
    rw [← h2, inv_one, mul_one, ← h1, hid, mactC_add, mactC_mul Ψ, hN, mactC_one_vec, mul_one,
      mactC_mul]
  have hu : gy * gx * gy⁻¹ = ι 1 * gx := by
    rw [map_one, one_mul, mul_inv_eq_iff_eq_mul, hcomm]
  have ha' : mactC Φ h * (mactC (A (π gx)) (mactC Φ h))⁻¹ =
      h * (mactC (A (π gy)) h)⁻¹ * (1 : Fin r → C)⁻¹ := by
    rw [hgx, hgy]; exact ha
  obtain ⟨hc, hcy⟩ := lift_centralizer_of_solve_ab ι π A hιπ hconj h 1 _ hsh hu ha'
  exact eightyOne_dvd_of_pair_ab ι π A hι hιπ hconj x y s _ hs hc (hcy.trans hgy) ω hω c₁ c₂ p₁ p₂
    hf₁ hf₂ h11 h12 h21 h22 hQ

section Cyclic

variable [IsCyclic C]

theorem solve_group_ab {n : ℕ} (X : Matrix (Fin r) (Fin r) ℤ)
    (Y : Fin n → Matrix (Fin r) (Fin r) ℤ) (Ξ : Matrix (Fin r) (Fin r) ℤ)
    (hΞ : (1 - X) * Ξ = (3 : ℤ) • 1) (u : Fin n → (Fin r → C)) (hu : ∀ i, u i * u i = 1)
    (hsolve : ∀ c : Fin r → ℤ, ∃ i : Fin n, ∃ d : Fin r → ℤ,
      (1 - X).mulVec d = (1 - Y i).mulVec c) (h : Fin r → C) :
    ∃ i : Fin n, ∃ a : Fin r → C, a * (mactC X a)⁻¹ = h * (mactC (Y i) h)⁻¹ * (u i)⁻¹ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have hc : ∀ k, ∃ m : ℤ, g ^ m = h k := fun k => Subgroup.mem_zpowers_iff.1 (hg (h k))
  choose c hc using hc
  have hh : h = vecTC c g := funext fun k => (hc k).symm
  obtain ⟨i, d, hd⟩ := hsolve c
  refine ⟨i, vecTC d g * mactC Ξ (u i)⁻¹, ?_⟩
  have e1 : mactC (1 - X) (vecTC d g) = h * (mactC (Y i) h)⁻¹ := by
    rw [mactC_vecTC, hd, ← mactC_vecTC, ← hh, mactC_one_sub]
  have e2 : mactC (1 - X) (mactC Ξ (u i)⁻¹) = (u i)⁻¹ := by
    rw [← mactC_mul, hΞ, mactC_smul_one]
    have h2 : (u i)⁻¹ * (u i)⁻¹ = 1 := by rw [← mul_inv, hu, inv_one]
    calc (u i)⁻¹ ^ (3 : ℤ) = (u i)⁻¹ * ((u i)⁻¹ * (u i)⁻¹) := by group
      _ = (u i)⁻¹ := by rw [h2, mul_one]
  rw [← mactC_one_sub, mactC_mul_apply, e1, e2]

include hι hker hιπ hconj in
theorem caseB_ab {n : ℕ} (x : W) (ys : Fin n → W) (s gx : G)
    (hs : π s = x) (hgx : π gx = x)
    (hlift : ∀ i, ∃ g : G, π g = ys i ∧ g * gx = gx * g)
    (Ξ : Matrix (Fin r) (Fin r) ℤ)
    (hΞ : (1 - A x) * Ξ = (3 : ℤ) • 1)
    (hsolve : ∀ c : Fin r → ℤ, ∃ i : Fin n, ∃ d : Fin r → ℤ,
      (1 - A x).mulVec d = (1 - A (ys i)).mulVec c)
    (ω : C) (hω : orderOf ω = 3) (c₁ c₂ : Fin r → ℤ) (p₁ p₂ : Fin r)
    (hf₁ : ∀ i, (3 : ℤ) ∣ ((A x).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i, (3 : ℤ) ∣ ((A x).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : ∀ i, 9 ∣ Nat.card (Subgroup.closure ({x, ys i} : Set W))) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) := by
  obtain ⟨h, hsh⟩ := exists_decomp_ab ι π hker (hs.trans hgx.symm)
  choose gy hgy hgycomm using hlift
  obtain ⟨i, a, ha⟩ := solve_group_ab (C := C) (A x) (fun i => A (ys i)) Ξ hΞ
    (fun _ => 1) (fun _ => mul_one 1) hsolve h
  have ha' : a * (mactC (A (π gx)) a)⁻¹ =
      h * (mactC (A (π (gy i))) h)⁻¹ * (1 : Fin r → C)⁻¹ := by
    rw [hgx, hgy i]; simpa using ha
  have hu : gy i * gx * (gy i)⁻¹ = ι 1 * gx := by
    rw [map_one, one_mul, mul_inv_eq_iff_eq_mul, hgycomm i]
  obtain ⟨hc, hcy⟩ := lift_centralizer_of_solve_ab ι π A hιπ hconj h 1 a hsh hu ha'
  exact eightyOne_dvd_of_pair_ab ι π A hι hιπ hconj x (ys i) s _ hs hc (hcy.trans (hgy i)) ω hω
    c₁ c₂ p₁ p₂ hf₁ hf₂ h11 h12 h21 h22 (hQ i)

end Cyclic

end Main

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
