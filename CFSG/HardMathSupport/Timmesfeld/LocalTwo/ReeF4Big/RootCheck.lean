module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Ree.Duality

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree

@[expose, reducible] def U1 (v : ℤ) : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![-1, 0, 0, -v], ![0, -1, -v, 0]]

@[expose, reducible] def U2 (v : ℤ) : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![0, -1, 0, 1 - v], ![-1, -1, -v, 2]]

@[expose, reducible] def U4m (v : ℤ) : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![-1, 0, 0, 1 - v], ![-1, -1, 1 - v, 1]]

@[expose, reducible] def U4p (v : ℤ) : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![-1, 0, 0, -v], ![-1, -1, -v, 1]]

theorem dvd_norm_of_dvd {p : ℕ} {v b e c d : ℤ} (hh : (p : ℤ) ∣ 2 * v ^ 2 + b * v + e)
    (hu : (p : ℤ) ∣ c + d * v) : (p : ℤ) ∣ 2 * c ^ 2 - b * c * d + e * d ^ 2 := by
  have key : 2 * c ^ 2 - b * c * d + e * d ^ 2 =
      (c + d * v) * (2 * c - b * d - 2 * d * v) + d ^ 2 * (2 * v ^ 2 + b * v + e) := by
    ring
  rw [key]
  exact dvd_add (hu.mul_right _) (hh.mul_left _)

@[expose] def expA1 : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![-1, 0, 0, 0], ![0, -1, 0, 0]]

@[expose] def expB1 : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![0, 0, 0, -1], ![0, 0, -1, 0]]

@[expose] def expA2 : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![0, -1, 0, 1], ![-1, -1, 0, 2]]

@[expose] def expB2 : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![0, 0, 0, -1], ![0, 0, -1, 0]]

@[expose] def expA4m : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![-1, 0, 0, 1], ![-1, -1, 1, 1]]

@[expose] def expB4m : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![0, 0, 0, -1], ![0, 0, -1, 0]]

@[expose] def expA4p : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![-1, 0, 0, 0], ![-1, -1, 0, 1]]

@[expose] def expB4p : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ :=
  ![![0, 0, 0, -1], ![0, 0, -1, 0]]

theorem U1_affine (v : ℤ) (s : Fin 2) (i : Fin 4) :
    U1 v s i = expA1 s i + expB1 s i * v := by
  fin_cases s <;> fin_cases i <;> simp [U1, expA1, expB1] <;> ring

theorem U2_affine (v : ℤ) (s : Fin 2) (i : Fin 4) :
    U2 v s i = expA2 s i + expB2 s i * v := by
  fin_cases s <;> fin_cases i <;> simp [U2, expA2, expB2] <;> ring

theorem U4m_affine (v : ℤ) (s : Fin 2) (i : Fin 4) :
    U4m v s i = expA4m s i + expB4m s i * v := by
  fin_cases s <;> fin_cases i <;> simp [U4m, expA4m, expB4m] <;> ring

theorem U4p_affine (v : ℤ) (s : Fin 2) (i : Fin 4) :
    U4p v s i = expA4p s i + expB4p s i * v := by
  fin_cases s <;> fin_cases i <;> simp [U4p, expA4p, expB4p] <;> ring

@[expose] def ReeGoodRoot (b e : ℤ) (A B : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ)
    (β : Fin ReeTag.F4.tag.rank → ℤ) : Prop :=
  ∃ s : Fin 2, 2 * (∑ i, A s i * β i) ^ 2 - b * (∑ i, A s i * β i) * (∑ i, B s i * β i)
    + e * (∑ i, B s i * β i) ^ 2 ∣ 24

instance (b e : ℤ) (A B : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ)
    (β : Fin ReeTag.F4.tag.rank → ℤ) : Decidable (ReeGoodRoot b e A B β) := by
  unfold ReeGoodRoot
  infer_instance

theorem not_both_zero_of_good {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {v b e : ℤ}
    (hh : (p : ℤ) ∣ 2 * v ^ 2 + b * v + e)
    {U A B : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ} (hU : ∀ s i, U s i = A s i + B s i * v)
    {β : Fin ReeTag.F4.tag.rank → ℤ} (hgood : ReeGoodRoot b e A B β) :
    ¬ (((∑ i, U 0 i * β i : ℤ) : ZMod p) = 0 ∧ ((∑ i, U 1 i * β i : ℤ) : ZMod p) = 0) := by
  rintro ⟨h0, h1⟩
  obtain ⟨s, hs24⟩ := hgood
  have hlin : ∀ t, ∑ i, U t i * β i = (∑ i, A t i * β i) + (∑ i, B t i * β i) * v := by
    intro t
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hU]
    ring
  have hall : ∀ t : Fin 2, ((∑ i, U t i * β i : ℤ) : ZMod p) = 0 :=
    Fin.forall_fin_two.2 ⟨h0, h1⟩
  have hu : (p : ℤ) ∣ (∑ i, A s i * β i) + (∑ i, B s i * β i) * v := by
    rw [← hlin s]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (hall s)
  have hp24 : (p : ℤ) ∣ 24 := dvd_trans (dvd_norm_of_dvd hh hu) hs24
  have hp24' : p ∣ 2 ^ 3 * 3 := by
    norm_num
    exact_mod_cast hp24
  rcases (Nat.Prime.dvd_mul hp).1 hp24' with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

theorem good_phi1 : ∀ β ∈ rootFinset ReeTag.F4.tag, ReeGoodRoot 0 (-1) expA1 expB1 β := by
  decide +kernel

theorem good_phi2 : ∀ β ∈ rootFinset ReeTag.F4.tag, ReeGoodRoot 0 1 expA2 expB2 β := by
  decide +kernel

theorem good_phi4m : ∀ β ∈ rootFinset ReeTag.F4.tag, ReeGoodRoot (-2) 1 expA4m expB4m β := by
  decide +kernel

theorem good_phi4p : ∀ β ∈ rootFinset ReeTag.F4.tag, ReeGoodRoot 2 1 expA4p expB4p β := by
  decide +kernel

theorem regular_roots_phi1 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {v : ℤ}
    (hv : (p : ℤ) ∣ 2 * v ^ 2 - 1) :
    ∀ β ∈ rootFinset ReeTag.F4.tag,
      ¬ (((∑ i, U1 v 0 i * β i : ℤ) : ZMod p) = 0 ∧ ((∑ i, U1 v 1 i * β i : ℤ) : ZMod p) = 0) := by
  intro β hβ
  have hh : (p : ℤ) ∣ 2 * v ^ 2 + 0 * v + (-1) := by
    rw [show 2 * v ^ 2 + 0 * v + (-1) = 2 * v ^ 2 - 1 by ring]
    exact hv
  exact not_both_zero_of_good hp hp3 (b := 0) (e := -1) hh (U := U1 v) (A := expA1)
    (B := expB1) (U1_affine v) (good_phi1 β hβ)

theorem regular_roots_phi2 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {v : ℤ}
    (hv : (p : ℤ) ∣ 2 * v ^ 2 + 1) :
    ∀ β ∈ rootFinset ReeTag.F4.tag,
      ¬ (((∑ i, U2 v 0 i * β i : ℤ) : ZMod p) = 0 ∧ ((∑ i, U2 v 1 i * β i : ℤ) : ZMod p) = 0) := by
  intro β hβ
  have hh : (p : ℤ) ∣ 2 * v ^ 2 + 0 * v + 1 := by
    rw [show 2 * v ^ 2 + 0 * v + 1 = 2 * v ^ 2 + 1 by ring]
    exact hv
  exact not_both_zero_of_good hp hp3 (b := 0) (e := 1) hh (U := U2 v) (A := expA2)
    (B := expB2) (U2_affine v) (good_phi2 β hβ)

theorem regular_roots_phi4m {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {v : ℤ}
    (hv : (p : ℤ) ∣ 2 * v ^ 2 - 2 * v + 1) :
    ∀ β ∈ rootFinset ReeTag.F4.tag,
      ¬ (((∑ i, U4m v 0 i * β i : ℤ) : ZMod p) = 0 ∧ ((∑ i, U4m v 1 i * β i : ℤ) : ZMod p) = 0) := by
  intro β hβ
  have hh : (p : ℤ) ∣ 2 * v ^ 2 + (-2) * v + 1 := by
    rw [show 2 * v ^ 2 + (-2) * v + 1 = 2 * v ^ 2 - 2 * v + 1 by ring]
    exact hv
  exact not_both_zero_of_good hp hp3 (b := -2) (e := 1) hh (U := U4m v) (A := expA4m)
    (B := expB4m) (U4m_affine v) (good_phi4m β hβ)

theorem regular_roots_phi4p {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {v : ℤ}
    (hv : (p : ℤ) ∣ 2 * v ^ 2 + 2 * v + 1) :
    ∀ β ∈ rootFinset ReeTag.F4.tag,
      ¬ (((∑ i, U4p v 0 i * β i : ℤ) : ZMod p) = 0 ∧ ((∑ i, U4p v 1 i * β i : ℤ) : ZMod p) = 0) := by
  intro β hβ
  exact not_both_zero_of_good hp hp3 (b := 2) (e := 1) hv (U := U4p v) (A := expA4p)
    (B := expB4p) (U4p_affine v) (good_phi4p β hβ)

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big
