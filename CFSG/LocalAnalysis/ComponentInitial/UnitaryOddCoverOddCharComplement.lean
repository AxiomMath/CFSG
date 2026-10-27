module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverOddCharSplit
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverLargeComplement

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverOddChar

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension UnitaryOddCover
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 1} (hθ : Function.Surjective θ)
  (hC : θ.ker ≤ Subgroup.center E)

theorem lift_scalar_commute {σ : Kˣ} {g₀ : E}
    (hg₀ : θ g₀ = hypProj h r 1 (lHom h r (hTorusGL fun _ => σ))) {B : GL (Fin r) K} {u : E}
    (hu : θ u = hypProj h r 1 (lHom h r B)) : θ u * θ g₀ = θ g₀ * θ u := by
  rw [hu, hg₀, ← map_mul (hypProj h r 1), ← map_mul (hypProj h r 1), lHom_scalar_commute σ B]

include hC in
theorem conj_scalar_lift_mem_center {σ : Kˣ} {g₀ : E}
    (hg₀ : θ g₀ = hypProj h r 1 (lHom h r (hTorusGL fun _ => σ))) {B : GL (Fin r) K} {u : E}
    (hu : θ u = hypProj h r 1 (lHom h r B)) : u * g₀ * u⁻¹ * g₀⁻¹ ∈ Subgroup.center E :=
  hC (by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      lift_scalar_commute hg₀ hu]
    group)

include hθ hC in
theorem exists_radical_complement (hq : 5 ≤ p ^ f) (hr : 2 ≤ r) (hp : IsPGroup p θ.ker) :
    ∃ M₀ : Subgroup E, M₀ ≤ preN θ ∧ (∀ y ∈ M₀, θ y = 1 → y = 1) ∧
      (∀ {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} (hx : IsRad h x C),
        ∃ y ∈ M₀, θ y = hypProj h r 1 (nElt hx)) ∧
      ∀ (A : SpecialLinearGroup (Fin r) K) (u : E),
        θ u = hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) →
          ∀ y, y ∈ M₀ ↔ u * y * u⁻¹ ∈ M₀ := by
  obtain ⟨Vt, hVt⟩ := exists_levi_complement hθ hC hq hp
  obtain ⟨σ, hσ, hσ2⟩ := exists_fixed_unit_sq_ne_one (h := h) hq
  have hσ1 : (σ : K) ≠ 1 := fun h1 => hσ2 (by rw [h1, one_pow])
  obtain ⟨g₀, hg₀⟩ := hθ (hypProj h r 1 (lHom h r (hTorusGL fun _ => σ)))
  have hg₀M : ∀ y ∈ preN θ, g₀ * y * g₀⁻¹ ∈ preN θ := fun y hy =>
    conj_mem_preN_of_lift hg₀ hy
  have hMV : ∀ y ∈ preN θ, ∀ y' ∈ preN θ, ⁅y, y'⁆ ∈ Vt := fun y hy y' hy' =>
    commutatorElement_mem_levi_complement hθ hC hVt hq hr hy hy'
  have hVM : ∀ v ∈ Vt, ∀ y ∈ preN θ, v * y = y * v := fun v hv y hy =>
    mul_comm_of_mem_preV_of_mem_preN hθ hC hq hr (hVt.le hv) hy
  have hVle : Vt ≤ preN θ := hVt.le.trans preV_le_preN
  set M₀ := radLift g₀ (preN θ) Vt hg₀M hMV hVM with hM₀
  have hM₀N : M₀ ≤ preN θ := by
    rintro z ⟨y, hy, hz⟩
    rw [show z = ⁅g₀, y⁆ * (⁅g₀, y⁆⁻¹ * z) by group]
    exact mul_mem (commutatorElement_mem_of_normalizes hg₀M hy) (hVle hz)
  have hg₀m := map_pow_card_units_eq_one hg₀
  refine ⟨M₀, hM₀N, ?_, fun {x C₁} hx => ?_, fun A u hu y => ?_⟩
  ·
    rintro z ⟨y, hy, hz⟩ hz1
    have hc : z ∈ Subgroup.center E := hC hz1
    set v := ⁅g₀, y⁆⁻¹ * z with hv
    have hstep : g₀ * y * g₀⁻¹ = z * v⁻¹ * y := by
      rw [hv, commutatorElement_def]
      group
    have hk : ∀ k : ℕ, ∃ w ∈ Vt, g₀ ^ k * y * (g₀ ^ k)⁻¹ = z ^ k * w * y := by
      intro k
      induction k with
      | zero => exact ⟨1, one_mem _, by simp⟩
      | succ k ih =>
        obtain ⟨w, hw, hwk⟩ := ih
        refine ⟨g₀ * w * g₀⁻¹ * v⁻¹, mul_mem (hVt.conj _ g₀ hg₀ w hw) (inv_mem hz), ?_⟩
        have hzc := Subgroup.mem_center_iff.mp hc (g₀ * w * g₀⁻¹)
        calc g₀ ^ (k + 1) * y * (g₀ ^ (k + 1))⁻¹ = g₀ * (g₀ ^ k * y * (g₀ ^ k)⁻¹) * g₀⁻¹ := by
              group
          _ = g₀ * (z ^ k * w * y) * g₀⁻¹ := by rw [hwk]
          _ = (g₀ * z ^ k * g₀⁻¹) * (g₀ * w * g₀⁻¹) * (g₀ * y * g₀⁻¹) := by group
          _ = z ^ k * ((g₀ * w * g₀⁻¹) * z) * v⁻¹ * y := by
              rw [conj_central (Subgroup.pow_mem _ hc k), hstep]
              group
          _ = z ^ (k + 1) * (g₀ * w * g₀⁻¹ * v⁻¹) * y := by
              rw [hzc, pow_succ]
              group
    obtain ⟨w, hw, hwn⟩ := hk (Nat.card Kˣ)
    rw [conj_eq_of_mem_center (hC hg₀m)] at hwn
    have hzw : z ^ Nat.card Kˣ * w = 1 := mul_eq_right.mp hwn.symm
    have hzn : z ^ Nat.card Kˣ = 1 := by
      have hmem : z ^ Nat.card Kˣ ∈ Vt := by
        rw [eq_inv_of_mul_eq_one_left hzw]
        exact inv_mem hw
      exact hVt.inj _ hmem (by rw [map_pow, hz1, one_pow])
    obtain ⟨a, ha⟩ := hp ⟨z, hz1⟩
    have ha' : z ^ p ^ a = 1 := by
      simpa using congrArg (fun w : θ.ker => (w : E)) ha
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left a (coprime_card_units h))
      (orderOf_dvd_of_pow_eq_one ha') (orderOf_dvd_of_pow_eq_one hzn))
  ·
    have hσ1' : (σ : K) - 1 ≠ 0 := sub_ne_zero.mpr hσ1
    obtain ⟨y, hy⟩ := exists_isN hθ (((σ : K) - 1)⁻¹ • x)
    have hφ : IsN θ x ⁅g₀, y⁆ := by
      rw [commutatorElement_def]
      refine ((isN_conj_scalar hσ hy hg₀).mul hy.inv).congr ?_
      rw [smul_smul, ← sub_eq_add_neg, ← sub_smul, ← sub_one_mul, mul_inv_cancel₀ hσ1',
        one_smul]
    obtain ⟨m, hm⟩ := hθ (hypProj h r 1 (nElt hx))
    have hmN : IsN θ x m := ⟨C₁, hx, hm⟩
    obtain ⟨c, v, hc1, hv, hcv⟩ := hVt.dec _ (hφ.inv_mul_mem hmN)
    refine ⟨⁅g₀, y⁆ * v, ⟨y, hy.mem, by rw [inv_mul_cancel_left]; exact hv⟩, ?_⟩
    have hθv : θ v = θ (⁅g₀, y⁆⁻¹ * m) := by rw [hcv, map_mul, hc1, one_mul]
    rw [map_mul, hθv, ← map_mul, mul_inv_cancel_left, hm]
  ·
    have key : ∀ (B : GL (Fin r) K) (u : E), θ u = hypProj h r 1 (lHom h r B) →
        ∀ z ∈ M₀, u * z * u⁻¹ ∈ M₀ := by
      rintro B u hu z ⟨y, hy, hz⟩
      have hc := conj_scalar_lift_mem_center hC hg₀ hu
      have hug₀ : u * g₀ * u⁻¹ = (u * g₀ * u⁻¹ * g₀⁻¹) * g₀ := by group
      refine ⟨u * y * u⁻¹, conj_mem_preN_of_lift hu hy, ?_⟩
      have e : ⁅g₀, u * y * u⁻¹⁆ = u * ⁅g₀, y⁆ * u⁻¹ := by
        rw [conjugate_commutatorElement, hug₀, commutatorElement_central_mul_left hc]
      rw [e, show (u * ⁅g₀, y⁆ * u⁻¹)⁻¹ * (u * z * u⁻¹) = u * (⁅g₀, y⁆⁻¹ * z) * u⁻¹ by group]
      exact hVt.conj B u hu _ hz
    refine ⟨key _ u hu y, fun hy => ?_⟩
    have := key _ u⁻¹ (by rw [map_inv, hu, ← map_inv, ← map_inv]) _ hy
    rwa [show u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y by group] at this

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverOddChar
