module

public import CFSG.LieType.SeitzGeneration.NonabParabolic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix
open scoped commutatorElement

variable {F : Type*} [Field F] {n : ℕ}

abbrev toPSL : SpecialLinearGroup (Fin n) F →* ProjectiveSpecialLinearGroup (Fin n) F :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))

theorem mem_center_iff_toPSL_eq_one {g : SpecialLinearGroup (Fin n) F} :
    g ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) ↔ toPSL g = 1 := by
  exact (QuotientGroup.eq_one_iff g).symm

theorem exists_scalar_of_mem_center (hn : 0 < n) {z : SpecialLinearGroup (Fin n) F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) F)) :
    ∃ r : F, r ≠ 0 ∧ (z : Matrix (Fin n) (Fin n) F) = r • (1 : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨r, hr, hz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  refine ⟨r, ?_, ?_⟩
  · rintro rfl
    rw [Fintype.card_fin, zero_pow hn.ne'] at hr
    exact zero_ne_one hr
  · rw [← hz]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

theorem exists_plane_lifts {p : ℕ} (hp : p.Prime)
    (E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    ∃ a b : SpecialLinearGroup (Fin n) F, toPSL a ∈ E ∧ toPSL b ∈ E ∧
      a ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) ∧
      b ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) ∧
      ⁅a, b⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) ∧
      (∀ j : ℕ, a * b ^ j ∉ Subgroup.center (SpecialLinearGroup (Fin n) F)) ∧
      b ∉ Subgroup.center (SpecialLinearGroup (Fin n) F) ∧
      E ≤ Subgroup.closure {toPSL a, toPSL b} := by
  have hπ : Function.Surjective (toPSL (n := n) (F := F)) := QuotientGroup.mk'_surjective _
  obtain ⟨x, hxE, y, hyE, hy1, hxy⟩ := exists_independent_pair hp E hexp hcard
  obtain ⟨a, rfl⟩ := hπ x
  obtain ⟨b, rfl⟩ := hπ y
  refine ⟨a, b, hxE, hyE, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_center_iff_toPSL_eq_one, map_pow]; exact hexp _ hxE
  · rw [mem_center_iff_toPSL_eq_one, map_pow]; exact hexp _ hyE
  · rw [mem_center_iff_toPSL_eq_one, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ hxE _ hyE)
  · intro j hj
    rw [mem_center_iff_toPSL_eq_one, map_mul, map_pow] at hj
    apply hxy
    have : toPSL a = ((toPSL b) ^ j)⁻¹ := eq_inv_of_mul_eq_one_left hj
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j)
  · intro hb
    exact hy1 (mem_center_iff_toPSL_eq_one.1 hb)
  · have hle : Subgroup.closure {toPSL a, toPSL b} ≤ E := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      exacts [hxE, hyE]
    have : Fact p.Prime := ⟨hp⟩
    have hfin : Finite E :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
    have hord : orderOf (toPSL b) = p := orderOf_eq_prime (hexp _ hyE) hy1
    have hzle : Subgroup.zpowers (toPSL b) ≤ Subgroup.closure {toPSL a, toPSL b} :=
      Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
    have hfinC : Finite (Subgroup.closure {toPSL a, toPSL b}) :=
      Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have hdvd : Nat.card (Subgroup.closure {toPSL a, toPSL b}) ∣ p ^ 2 :=
      hcard ▸ Subgroup.card_dvd_of_le hle
    obtain ⟨m, hm2, hm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hp_dvd : p ∣ Nat.card (Subgroup.closure {toPSL a, toPSL b}) := by
      have := Subgroup.card_dvd_of_le hzle
      rwa [Nat.card_zpowers, hord] at this
    have hm1 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      rw [hm] at hp_dvd
      exact hp.one_lt.ne' (Nat.dvd_one.1 hp_dvd)
    have hm2' : m ≠ 1 := by
      rintro rfl
      rw [pow_one] at hm
      have heq : Subgroup.zpowers (toPSL b) = Subgroup.closure {toPSL a, toPSL b} :=
        Subgroup.eq_of_le_of_card_ge hzle (by rw [Nat.card_zpowers, hord, hm])
      exact hxy (heq ▸ Subgroup.subset_closure (by simp))
    have hm_eq : m = 2 := by omega
    have heq : Subgroup.closure {toPSL a, toPSL b} = E :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hm, hm_eq, hcard])
    exact heq.ge

section ClassTwo

variable {G : Type*} [Group G]

theorem pow_mul_eq_of_quasi_commute {u v w : G} (hw : ∀ g, Commute w g) (h : v * u = w * (u * v))
    (k : ℕ) : v ^ k * u = w ^ k * (u * v ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc v ^ (k + 1) * u = v * (v ^ k * u) := by rw [pow_succ', mul_assoc]
      _ = v * (w ^ k * (u * v ^ k)) := by rw [ih]
      _ = w ^ k * (v * (u * v ^ k)) := by
          rw [← mul_assoc, ← ((hw v).pow_left k).eq, mul_assoc]
      _ = w ^ k * ((v * u) * v ^ k) := by rw [mul_assoc]
      _ = w ^ k * ((w * (u * v)) * v ^ k) := by rw [h]
      _ = w ^ (k + 1) * (u * v ^ (k + 1)) := by
          rw [pow_succ w k, pow_succ' v k]; simp only [mul_assoc]

theorem mul_pow_eq_of_quasi_commute {u v w : G} (hw : ∀ g, Commute w g)
    (h : v * u = w * (u * v)) (k : ℕ) : (u * v) ^ k = w ^ k.choose 2 * (u ^ k * v ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hvu := pow_mul_eq_of_quasi_commute hw h k
    have hwk : ∀ g, w ^ k * g = g * w ^ k := fun g => ((hw g).pow_left k).eq
    have hc : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
    calc (u * v) ^ (k + 1) = (u * v) ^ k * (u * v) := pow_succ _ _
      _ = w ^ k.choose 2 * (u ^ k * v ^ k) * (u * v) := by rw [ih]
      _ = w ^ k.choose 2 * (u ^ k * (v ^ k * u) * v) := by simp only [mul_assoc]
      _ = w ^ k.choose 2 * (u ^ k * (w ^ k * (u * v ^ k)) * v) := by rw [hvu]
      _ = w ^ k.choose 2 * (w ^ k * (u ^ k * (u * v ^ k) * v)) := by
          rw [← mul_assoc (u ^ k), ← hwk (u ^ k)]; simp only [mul_assoc]
      _ = w ^ (k + 1).choose 2 * (u ^ (k + 1) * v ^ (k + 1)) := by
          rw [hc, pow_add, pow_succ u k, pow_succ v k]; simp only [mul_assoc]

theorem mul_pow_prime_eq {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {u v w : G}
    (hw : ∀ g, Commute w g) (h : v * u = w * (u * v)) (hwp : w ^ p = 1) :
    (u * v) ^ p = u ^ p * v ^ p := by
  rw [mul_pow_eq_of_quasi_commute hw h p]
  have h2 : p.choose 2 = p * ((p - 1) / 2) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_assoc _ (even_iff_two_dvd.1 (hp.even_sub_one hp2))
  rw [h2, pow_mul, hwp, one_pow, one_mul]

end ClassTwo

section FiniteField

variable [Finite F]

theorem exists_pow_eq_of_pow_div_eq_one {p : ℕ} (hpq : p ∣ Nat.card F - 1) {t : F} (ht : t ≠ 0)
    (h : t ^ ((Nat.card F - 1) / p) = 1) : ∃ s : F, s ≠ 0 ∧ s ^ p = t := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  set d := (Nat.card F - 1) / p with hd
  have hN : Nat.card Fˣ = p * d := by
    rw [Nat.card_units]; exact (Nat.mul_div_cancel' hpq).symm
  have hord : orderOf g = p * d := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hN]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, g ^ m = Units.mk0 t ht :=
    (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hg _))
  have h1 : (Units.mk0 t ht) ^ d = 1 := Units.ext (by simpa using h)
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · have : Nat.card Fˣ = 0 := by rw [hN, h0, mul_zero]
      exact absurd this (Nat.card_pos (α := Fˣ)).ne'
    · exact h0
  have h2 : orderOf g ∣ m * d := orderOf_dvd_of_pow_eq_one (by rw [pow_mul, hm]; exact h1)
  rw [hord] at h2
  have h3 : p ∣ m := by
    have : p * d ∣ m * d := h2
    exact (Nat.mul_dvd_mul_iff_right hdpos).1 this
  obtain ⟨r, rfl⟩ := h3
  refine ⟨((g ^ r : Fˣ) : F), (g ^ r).ne_zero, ?_⟩
  have : (g ^ r) ^ p = Units.mk0 t ht := by rw [← pow_mul, mul_comm, hm]
  simpa using congrArg Units.val this

end FiniteField

section SplitLine

variable [Finite F]

theorem exists_split_line {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (hpq : p ∣ Nat.card F - 1) {a b : SpecialLinearGroup (Fin n) F}
    (hap : a ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hbp : b ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F))
    (hab : ⁅a, b⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F)) :
    ∃ e f : SpecialLinearGroup (Fin n) F, ((e = b ∧ f = a) ∨ ∃ j : ℕ, e = a * b ^ j ∧ f = b) ∧
      ∃ s : F, s ≠ 0 ∧ ((e ^ p : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (s ^ p) • (1 : Matrix (Fin n) (Fin n) F) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨α, hα0, hα⟩ := exists_scalar_of_mem_center hn hap
  obtain ⟨β, hβ0, hβ⟩ := exists_scalar_of_mem_center hn hbp
  set d := (Nat.card F - 1) / p with hd
  have hκ : ∀ t : F, t ≠ 0 → (t ^ d) ^ p = 1 := fun t ht => by
    rw [← pow_mul, mul_comm, hd, Nat.mul_div_cancel' hpq]
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one t ht
  by_cases hβ1 : β ^ d = 1
  · obtain ⟨s, hs0, hs⟩ := exists_pow_eq_of_pow_div_eq_one hpq hβ0 hβ1
    exact ⟨b, a, Or.inl ⟨rfl, rfl⟩, s, hs0, by rw [hβ, hs]⟩
  · have hω : IsPrimitiveRoot (β ^ d) p := by
      have := orderOf_eq_prime (hκ β hβ0) hβ1
      rw [← this]
      exact IsPrimitiveRoot.orderOf _
    obtain ⟨i, hi, hiα⟩ := hω.eq_pow_of_pow_eq_one (hκ α hα0)
    set j := p - i with hj
    have hαβ : α * β ^ j ≠ 0 := mul_ne_zero hα0 (pow_ne_zero _ hβ0)
    have h1 : (α * β ^ j) ^ d = 1 := by
      rw [mul_pow, ← hiα, pow_right_comm β j d, ← pow_add, hj, Nat.add_sub_cancel' hi.le]
      exact hω.pow_eq_one
    obtain ⟨s, hs0, hs⟩ := exists_pow_eq_of_pow_div_eq_one hpq hαβ h1
    refine ⟨a * b ^ j, b, Or.inr ⟨j, rfl, rfl⟩, s, hs0, ?_⟩
    set z := ⁅a, b⁆ with hz
    have hzc : ∀ g, Commute z g := fun g =>
      (Subgroup.mem_center_iff.1 hab g).symm
    have hzinv : ∀ g, Commute z⁻¹ g := fun g => (hzc g).inv_left
    have hba : b * a = z⁻¹ * (a * b) := by
      simp only [hz, commutatorElement_def, _root_.mul_inv_rev, inv_inv]; group
    have hbpa : b ^ p * a = a * b ^ p := (Subgroup.mem_center_iff.1 hbp a).symm
    have hzp : z ^ p = 1 := by
      have h0 := pow_mul_eq_of_quasi_commute hzinv hba p
      rw [hbpa] at h0
      have h2 : (z⁻¹) ^ p * (a * b ^ p) = 1 * (a * b ^ p) := by rw [← h0, one_mul]
      have h3 := mul_right_cancel h2
      simpa using h3
    have hw : ∀ g, Commute ((z⁻¹) ^ j) g := fun g => (hzinv g).pow_left j
    have hrel : b ^ j * a = (z⁻¹) ^ j * (a * b ^ j) := pow_mul_eq_of_quasi_commute hzinv hba j
    have hwp : ((z⁻¹) ^ j) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, inv_pow, hzp, inv_one, one_pow]
    have hmul := mul_pow_prime_eq hp hp2 hw hrel hwp
    have hbj : ((b ^ j) ^ p : SpecialLinearGroup (Fin n) F) = (b ^ p) ^ j := by
      rw [← pow_mul, mul_comm, pow_mul]
    rw [hmul, hbj, Matrix.SpecialLinearGroup.coe_mul, hα, Matrix.SpecialLinearGroup.coe_pow, hβ,
      smul_pow, one_pow, smul_mul_smul_comm, Matrix.one_mul, ← hs]

end SplitLine

section Eigen

open Polynomial in
theorem exists_eigenvector_of_pow_eq_one {p : ℕ} (hp0 : 0 < p) (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p)
    (hn : 0 < n) {M : Matrix (Fin n) (Fin n) F} (hM : M ^ p = 1) :
    ∃ (ξ : F) (v : Fin n → F), ξ ^ p = 1 ∧ v ≠ 0 ∧ M.mulVec v = ξ • v := by
  classical
  obtain ⟨ζ, hζ⟩ := hζ
  have hprod := X_pow_sub_one_eq_prod hp0 hζ
  have hprod' : (X ^ p - 1 : F[X]) =
      (((nthRootsFinset p (1 : F)).toList).map fun ξ => (X - C ξ : F[X])).prod := by
    rw [hprod, Finset.prod_map_toList]
  have hevl : aeval M (X ^ p - 1 : F[X]) = 0 := by simp [hM]
  rw [hprod', map_list_prod, List.map_map] at hevl
  have h0 : (((nthRootsFinset p (1 : F)).toList).map
      fun ξ => M - ξ • (1 : Matrix (Fin n) (Fin n) F)).prod = 0 := by
    rw [← hevl]
    congr 1
    refine List.map_congr_left fun ξ _ => ?_
    simp [Algebra.algebraMap_eq_smul_one]
  have hdet : Matrix.detMonoidHom ((((nthRootsFinset p (1 : F)).toList).map
      fun ξ => M - ξ • (1 : Matrix (Fin n) (Fin n) F)).prod) = 0 := by
    rw [h0, Matrix.coe_detMonoidHom]
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Matrix.det_zero
  rw [map_list_prod, List.map_map, List.prod_eq_zero_iff] at hdet
  obtain ⟨ξ, hξ, hξ0⟩ := List.mem_map.1 hdet
  have hξ0' : (M - ξ • (1 : Matrix (Fin n) (Fin n) F)).det = 0 := by
    simpa [Function.comp] using hξ0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hξ0'
  refine ⟨ξ, v, (mem_nthRootsFinset hp0 (1 : F)).1 (by simpa using hξ), hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hMv
  exact sub_eq_zero.1 hMv

end Eigen

section Stab

variable [Finite F]

@[expose] def stabSub (W : Submodule F (Fin n → F)) : Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {x | ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W}
  mul_mem' := fun {x y} hx hy w hw => by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    exact hx _ (hy w hw)
  one_mem' := fun w hw => by simpa using hw
  inv_mem' := fun {x} hx => by
    have hpow : ∀ k : ℕ, ∀ w ∈ W, ((x ^ k : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F).mulVec w ∈ W := by
      intro k
      induction k with
      | zero => intro w hw; simpa using hw
      | succ k ih =>
        intro w hw
        rw [pow_succ', Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
        exact hx _ (ih w hw)
    have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
      have ho : 0 < orderOf x := orderOf_pos x
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel ho, pow_orderOf_eq_one]
    intro w hw
    rw [hinv]
    exact hpow _ w hw

theorem mem_stabSub {W : Submodule F (Fin n → F)} {x : SpecialLinearGroup (Fin n) F} :
    x ∈ stabSub W ↔ ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W := Iff.rfl

theorem center_le_stabSub (W : Submodule F (Fin n → F)) :
    Subgroup.center (SpecialLinearGroup (Fin n) F) ≤ stabSub W := by
  intro z hz w hw
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have : (z : Matrix (Fin n) (Fin n) F).mulVec w = r • w := by
    rw [← hr]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [this]
  exact W.smul_mem r hw

theorem stable_of_gens {E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)}
    {a b : SpecialLinearGroup (Fin n) F} (hE : E ≤ Subgroup.closure {toPSL a, toPSL b})
    {W : Submodule F (Fin n → F)} (ha : a ∈ stabSub W) (hb : b ∈ stabSub W) :
    ∀ x : SpecialLinearGroup (Fin n) F, toPSL x ∈ E →
      ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W := by
  intro x hx
  have hcl : Subgroup.closure {a, b} ≤ stabSub W :=
    (Subgroup.closure_le _).2 (by rintro _ (rfl | rfl) <;> assumption)
  have hmap : (Subgroup.closure {a, b}).map toPSL = Subgroup.closure {toPSL a, toPSL b} := by
    rw [MonoidHom.map_closure, Set.image_pair]
  obtain ⟨m, hm, hmx⟩ : toPSL x ∈ (Subgroup.closure {a, b}).map toPSL := hmap ▸ hE hx
  have hz : m⁻¹ * x ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
    rw [mem_center_iff_toPSL_eq_one, map_mul, map_inv, hmx, inv_mul_cancel]
  have : x = m * (m⁻¹ * x) := by group
  rw [this]
  exact (stabSub W).mul_mem (hcl hm) (center_le_stabSub W hz)

end Stab

section Irreducible

variable [Finite F]

theorem irreducible_plane_dim {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) (hpn : p ∣ n)
    (hpq : p ∣ Nat.card F - 1) (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p)
    (E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2)
    (hirr : ∀ W : Submodule F (Fin n → F),
      (∀ x : SpecialLinearGroup (Fin n) F, toPSL x ∈ E →
        ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤) :
    n = p ∧ ∃ x y : SpecialLinearGroup (Fin n) F, toPSL x ∈ E ∧ toPSL y ∈ E ∧ x * y ≠ y * x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, haE, hbE, hap, hbp, hab, hline, hbc, hEcl⟩ :=
    exists_plane_lifts hp E hcomm hexp hcard
  obtain ⟨e, f, hef, s, hs0, hes⟩ := exists_split_line hp hp2 hn hpq hap hbp hab
  have key : toPSL e ∈ E ∧ toPSL f ∈ E ∧
      e ∉ Subgroup.center (SpecialLinearGroup (Fin n) F) ∧
      f ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) ∧
      ⁅e, f⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) ∧
      a ∈ Subgroup.closure {e, f} ∧ b ∈ Subgroup.closure {e, f} := by
    rcases hef with ⟨he, hf⟩ | ⟨j, he, hf⟩
    · rw [he, hf]
      refine ⟨hbE, haE, hbc, hap, ?_, Subgroup.subset_closure (by simp),
        Subgroup.subset_closure (by simp)⟩
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ hab
    · rw [he, hf]
      have hEmem : toPSL (a * b ^ j) ∈ E := by
        rw [map_mul, map_pow]; exact E.mul_mem haE (E.pow_mem hbE j)
      refine ⟨hEmem, hbE, hline j, hbp, ?_, ?_, Subgroup.subset_closure (by simp)⟩
      · rw [mem_center_iff_toPSL_eq_one, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ hEmem _ hbE)
      · have : a = (a * b ^ j) * (b ^ j)⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) j))
  obtain ⟨heE, hfE, heZ, hfp, hefZ, haCl, hbCl⟩ := key
  have hH : ∀ W : Submodule F (Fin n → F), e ∈ stabSub W → f ∈ stabSub W →
      ∀ x : SpecialLinearGroup (Fin n) F, toPSL x ∈ E →
        ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W := by
    intro W he hf
    have hcl : Subgroup.closure {e, f} ≤ stabSub W :=
      (Subgroup.closure_le _).2 (by rintro _ (rfl | rfl) <;> assumption)
    exact stable_of_gens hEcl (hcl haCl) (hcl hbCl)
  set ê : Matrix (Fin n) (Fin n) F := s⁻¹ • (e : Matrix (Fin n) (Fin n) F) with hêdef
  have hê : ê ^ p = 1 := by
    rw [hêdef, smul_pow, ← Matrix.SpecialLinearGroup.coe_pow, hes, smul_smul, ← mul_pow,
      inv_mul_cancel₀ hs0, one_pow, one_smul]
  obtain ⟨ξ, v, -, hv0, hêv⟩ := exists_eigenvector_of_pow_eq_one hp.pos hζ hn hê
  have hev : (e : Matrix (Fin n) (Fin n) F).mulVec v = (s * ξ) • v := by
    have : (e : Matrix (Fin n) (Fin n) F) = s • ê := by
      rw [hêdef, smul_smul, mul_inv_cancel₀ hs0, one_smul]
    rw [this, Matrix.smul_mulVec, hêv, smul_smul]
  set μ : F := s * ξ with hμ
  by_cases hc : e * f = f * e
  ·
    exfalso
    let W₁ : Submodule F (Fin n → F) :=
      LinearMap.ker (Matrix.toLin' ((e : Matrix (Fin n) (Fin n) F) - μ • 1))
    have hW₁ : ∀ w, w ∈ W₁ ↔ (e : Matrix (Fin n) (Fin n) F).mulVec w = μ • w := fun w => by
      simp [W₁, LinearMap.mem_ker, Matrix.toLin'_apply, sub_eq_zero]
    have heW : e ∈ stabSub W₁ := fun w hw => by
      rw [hW₁] at hw ⊢
      rw [hw, Matrix.mulVec_smul, hw]
    have hfW : f ∈ stabSub W₁ := fun w hw => by
      rw [hW₁] at hw ⊢
      have hcm : (e : Matrix (Fin n) (Fin n) F) * f = f * e := congrArg Subtype.val hc
      rw [Matrix.mulVec_mulVec, hcm, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
    rcases hirr W₁ (hH W₁ heW hfW) with h | h
    · have hv : v ∈ (⊥ : Submodule F (Fin n → F)) := h ▸ (hW₁ v).2 hev
      exact hv0 (by simpa using hv)
    · have hall : ∀ w, (e : Matrix (Fin n) (Fin n) F).mulVec w = μ • w := fun w =>
        (hW₁ w).1 (h ▸ Submodule.mem_top)
      have hescal : (e : Matrix (Fin n) (Fin n) F) = μ • (1 : Matrix (Fin n) (Fin n) F) := by
        rw [Matrix.ext_iff_mulVec]
        intro w
        rw [hall w, Matrix.smul_mulVec, Matrix.one_mulVec]
      apply heZ
      refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨μ, ?_, ?_⟩
      · have h1 := e.2
        rw [hescal, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
        rw [Fintype.card_fin]
        exact h1
      · rw [hescal]
        ext i j
        simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  · refine ⟨?_, e, f, heE, hfE, hc⟩
    obtain ⟨c, -, hcc⟩ := exists_scalar_of_mem_center hn hefZ
    obtain ⟨β, -, hβ⟩ := exists_scalar_of_mem_center hn hfp
    have hrel : (e : Matrix (Fin n) (Fin n) F) * f =
        c • ((f : Matrix (Fin n) (Fin n) F) * e) := by
      have h1 : (⁅e, f⁆ : SpecialLinearGroup (Fin n) F) * (f * e) = e * f := by
        simp only [commutatorElement_def]; group
      have h2 := congrArg Subtype.val h1
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hcc,
        Matrix.smul_mul, Matrix.one_mul] at h2
      exact h2.symm
    have hpow : ∀ k : ℕ, (e : Matrix (Fin n) (Fin n) F) * (f : Matrix (Fin n) (Fin n) F) ^ k =
        c ^ k • ((f : Matrix (Fin n) (Fin n) F) ^ k * e) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc (e : Matrix (Fin n) (Fin n) F) * (f : Matrix (Fin n) (Fin n) F) ^ (k + 1)
            = (e * (f : Matrix (Fin n) (Fin n) F) ^ k) * f := by rw [pow_succ, Matrix.mul_assoc]
          _ = c ^ k • ((f : Matrix (Fin n) (Fin n) F) ^ k * (e * f)) := by
              rw [ih, Matrix.smul_mul, Matrix.mul_assoc]
          _ = c ^ (k + 1) • ((f : Matrix (Fin n) (Fin n) F) ^ (k + 1) * e) := by
              rw [hrel, Matrix.mul_smul, smul_smul, pow_succ c k,
                pow_succ ((f : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) k,
                Matrix.mul_assoc]
    have hu : ∀ k : ℕ, (e : Matrix (Fin n) (Fin n) F).mulVec
        (((f : Matrix (Fin n) (Fin n) F) ^ k).mulVec v) =
        (c ^ k * μ) • ((f : Matrix (Fin n) (Fin n) F) ^ k).mulVec v := by
      intro k
      rw [Matrix.mulVec_mulVec, hpow k, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hev,
        Matrix.mulVec_smul, smul_smul]
    let u : Fin p → (Fin n → F) := fun k => ((f : Matrix (Fin n) (Fin n) F) ^ (k : ℕ)).mulVec v
    let W₂ : Submodule F (Fin n → F) := Submodule.span F (Set.range u)
    have hvW : v ∈ W₂ := by
      have : u ⟨0, hp.pos⟩ ∈ W₂ := Submodule.subset_span ⟨⟨0, hp.pos⟩, rfl⟩
      simpa [u] using this
    have heW₂ : e ∈ stabSub W₂ := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rw [show u k = ((f : Matrix (Fin n) (Fin n) F) ^ (k : ℕ)).mulVec v from rfl, hu k]
        exact W₂.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact W₂.add_mem hx hy
      | smul r x _ hx => rw [Matrix.mulVec_smul]; exact W₂.smul_mem r hx
    have hfW₂ : f ∈ stabSub W₂ := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rw [show u k = ((f : Matrix (Fin n) (Fin n) F) ^ (k : ℕ)).mulVec v from rfl,
          Matrix.mulVec_mulVec, ← pow_succ']
        by_cases hk : (k : ℕ) + 1 < p
        · exact Submodule.subset_span ⟨⟨k + 1, hk⟩, rfl⟩
        · have hkp : (k : ℕ) + 1 = p := by have := k.2; omega
          rw [hkp, ← Matrix.SpecialLinearGroup.coe_pow, hβ, Matrix.smul_mulVec,
            Matrix.one_mulVec]
          exact W₂.smul_mem _ hvW
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact W₂.add_mem hx hy
      | smul r x _ hx => rw [Matrix.mulVec_smul]; exact W₂.smul_mem r hx
    rcases hirr W₂ (hH W₂ heW₂ hfW₂) with h | h
    · exfalso
      rw [h] at hvW
      exact hv0 (by simpa using hvW)
    · have h1 : Module.finrank F W₂ ≤ p := by
        have := finrank_range_le_card (R := F) u
        simpa [Set.finrank, W₂] using this
      have h2 : Module.finrank F W₂ = n := by
        rw [h, finrank_top, Module.finrank_fin_fun]
      have h3 := Nat.le_of_dvd hn hpn
      omega

end Irreducible

end CFSG.LieType.SeitzGeneration
