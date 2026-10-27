module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617P

open Subgroup

variable {G : Type*} [Group G]

@[expose] def cj (A : Subgroup G) (b : G) : Subgroup G :=
  A.map (MulAut.conj b).toMonoidHom

theorem mem_cj {A : Subgroup G} {b y : G} : y ∈ cj A b ↔ b⁻¹ * y * b ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have e : b⁻¹ * ((MulAut.conj b).toMonoidHom a) * b = a := by
      show b⁻¹ * (b * a * b⁻¹) * b = a
      group
    rwa [e]
  · intro h
    refine ⟨b⁻¹ * y * b, h, ?_⟩
    show b * (b⁻¹ * y * b) * b⁻¹ = y
    group

theorem conj_mem_cj {A : Subgroup G} {a : G} (ha : a ∈ A) (b : G) : b * a * b⁻¹ ∈ cj A b := by
  rw [mem_cj]
  have e : b⁻¹ * (b * a * b⁻¹) * b = a := by group
  rwa [e]

theorem cj_mono {A A' : Subgroup G} (h : A ≤ A') (b : G) : cj A b ≤ cj A' b :=
  Subgroup.map_mono h

theorem cj_cj (A : Subgroup G) (c b : G) : cj (cj A c) b = cj A (b * c) := by
  ext y
  rw [mem_cj, mem_cj, mem_cj]
  have e : c⁻¹ * (b⁻¹ * y * b) * c = (b * c)⁻¹ * y * (b * c) := by group
  rw [e]

theorem cj_one (A : Subgroup G) : cj A 1 = A := by
  ext y
  rw [mem_cj]
  simp

theorem cj_iSup {ι : Sort*} (A : ι → Subgroup G) (b : G) :
    cj (⨆ i, A i) b = ⨆ i, cj (A i) b :=
  Subgroup.map_iSup _ _

theorem cj_eq_of_mem_normalizer {A : Subgroup G} {b : G} (hb : b ∈ normalizer (A : Set G)) :
    cj A b = A := by
  ext y
  rw [mem_cj]
  exact (Subgroup.mem_normalizer_iff''.mp hb y).symm

theorem mem_normalizer_of_cj_le {A : Subgroup G} {b : G} (h₁ : cj A b ≤ A)
    (h₂ : cj A b⁻¹ ≤ A) : b ∈ normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  constructor
  · intro hy
    refine h₂ ?_
    rw [mem_cj]
    have e : (b⁻¹)⁻¹ * (b⁻¹ * y * b) * b⁻¹ = y := by group
    rw [e]
    exact hy
  · intro hy
    exact h₁ (mem_cj.mpr hy)

theorem mem_normalizer_of_cj_eq {A : Subgroup G} {b : G} (h : cj A b = A) :
    b ∈ normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  rw [← mem_cj, h]

theorem mem_normalizer_of_commute {E F : Subgroup G} (hFE : F ≤ E)
    (hE : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u) {e : G} (he : e ∈ E) :
    e ∈ normalizer (F : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : e * h * e⁻¹ = h := by
      rw [hE e he h (hFE hh)]
      group
    rw [this]
    exact hh
  · intro hh
    have hhE : e * h * e⁻¹ ∈ E := hFE hh
    have hE' : h ∈ E := by
      have : h = e⁻¹ * (e * h * e⁻¹) * e := by group
      rw [this]
      exact E.mul_mem (E.mul_mem (E.inv_mem he) hhE) he
    have : e * h * e⁻¹ = h := by
      rw [hE e he h hE']
      group
    rw [this] at hh
    exact hh

theorem commute_of_iSup {ι : Sort*} (A : ι → Subgroup G)
    (h : ∀ i j, ∀ u ∈ A i, ∀ v ∈ A j, u * v = v * u) {u v : G} (hu : u ∈ ⨆ i, A i)
    (hv : v ∈ ⨆ i, A i) : u * v = v * u := by
  have h1 : ∀ i, ∀ u ∈ A i, ∀ v ∈ ⨆ i, A i, u * v = v * u := by
    intro i u hu v hv
    refine Subgroup.iSup_induction A (C := fun v => u * v = v * u) hv ?_ ?_ ?_
    · intro j w hw
      exact h i j u hu w hw
    · simp
    · intro a b ha hb
      rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  refine Subgroup.iSup_induction A (C := fun u => u * v = v * u) hu ?_ ?_ ?_
  · intro i w hw
    exact h1 i w hw v hv
  · simp
  · intro a b ha hb
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

theorem exists_diagonal_of_mem {Y E : Subgroup G} {z : G} {p : ℕ} (hp : 0 < p) (hz : z ^ p = 1)
    (hcomm : ∀ i : ℕ, 0 < i → i < p → ∀ x ∈ Y, ∀ t ∈ Y,
      z ^ i * x * (z ^ i)⁻¹ * t = t * (z ^ i * x * (z ^ i)⁻¹))
    {y : G} (hy : y ∈ Y) (hE : ∀ i : ℕ, z ^ i * y * (z ^ i)⁻¹ ∈ E) :
    ∃ d ∈ E ⊓ centralizer ({z} : Set G), ∀ t ∈ Y, d * t * d⁻¹ = y * t * y⁻¹ := by
  set a : ℕ → G := fun i => z ^ i * y * (z ^ i)⁻¹ with ha
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → G, r 0 = 1 ∧ ∀ k, r (k + 1) = r k * a (k + 1) :=
    ⟨fun k => Nat.rec 1 (fun k rk => rk * a (k + 1)) k, rfl, fun _ => rfl⟩
  have haE : ∀ i, a i ∈ E := hE
  have hyE : y ∈ E := by simpa [ha] using hE 0
  have hrE : ∀ k, r k ∈ E := by
    intro k
    induction k with
    | zero => rw [hr0]; exact E.one_mem
    | succ k ih => rw [hrs]; exact E.mul_mem ih (haE _)
  have hrC : ∀ k, k < p → ∀ t ∈ Y, r k * t = t * r k := by
    intro k
    induction k with
    | zero => intro _ t _; rw [hr0, one_mul, mul_one]
    | succ k ih =>
      intro hk t ht
      rw [hrs, mul_assoc, show a (k + 1) * t = t * a (k + 1) from
        hcomm (k + 1) k.succ_pos hk y hy t ht, ← mul_assoc, ih (by omega) t ht, mul_assoc]
  have hza : ∀ i : ℕ, z * a i * z⁻¹ = a (i + 1) := by
    intro i
    simp only [ha, pow_succ', mul_inv_rev]
    group
  have hrz : ∀ k, z * r k * z⁻¹ = (z * y * z⁻¹)⁻¹ * r (k + 1) := by
    intro k
    induction k with
    | zero =>
      rw [hr0, hrs, hr0, one_mul]
      simp only [ha, zero_add, pow_one]
      group
    | succ k ih =>
      have e : z * r (k + 1) * z⁻¹ = (z * r k * z⁻¹) * (z * a (k + 1) * z⁻¹) := by
        rw [hrs]
        group
      rw [e, ih, hza, hrs (k + 1), mul_assoc]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have haq : a (q + 1) = y := by simp [ha, hz]
  have hryc : r q * y = y * r q := hrC q (Nat.lt_succ_self q) y hy
  refine ⟨y * r q, Subgroup.mem_inf.mpr ⟨E.mul_mem hyE (hrE q), ?_⟩, ?_⟩
  · have hzd : z * (y * r q) * z⁻¹ = y * r q := by
      have e : z * (y * r q) * z⁻¹ = (z * y * z⁻¹) * (z * r q * z⁻¹) := by group
      rw [e, hrz q, mul_inv_cancel_left, hrs q, haq, hryc]
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * r q * z = z * (y * r q) * z⁻¹ * z := by rw [hzd]
      _ = z * (y * r q) := by group
  · intro t ht
    have h1 : r q * t * (r q)⁻¹ = t := by
      rw [hrC q (Nat.lt_succ_self q) t ht]
      group
    calc y * r q * t * (y * r q)⁻¹ = y * (r q * t * (r q)⁻¹) * y⁻¹ := by group
      _ = y * t * y⁻¹ := by rw [h1]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617P
